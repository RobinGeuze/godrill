package main

import (
	"bytes"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/hex"
	"encoding/xml"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"math/rand"
	"net/http"
	"os"
	"strings"
	"time"

	"github.com/miekg/dns"
)

type recursor struct {
	rootNameservers []*dns.NS
	trustAnchors []*dns.DS
	glues map[string][]string
	pinalg uint8
}

func newRecursor(rootNameservers []*dns.NS, trustAnchors []*dns.DS, rootGlues map[string][]string, pinalg uint8) *recursor {
	return &recursor{rootNameservers: rootNameservers, trustAnchors: trustAnchors, glues: rootGlues, pinalg: pinalg}
}

type dnssecInfo struct {
	domain  string
	dsRecords []*dns.DS
	keys []*dns.DNSKEY
	dotPins [][]byte
}

type keyDigest struct {
	XMLName xml.Name `xml:"KeyDigest"`
	Id string `xml:"id,attr"`
	ValidFrom string `xml:"validFrom,attr"`
	ValidUntil string `xml:"validUntil,attr"`
	KeyTag uint16 `xml:"KeyTag"`
	Algorithm uint8 `xml:"Algorithm"`
	DigestType uint8 `xml:"DigestType"`
	Digest string `xml:"Digest"`
}

type trustAnchor struct {
	XMLName xml.Name `xml:"TrustAnchor"`
	Id string `xml:"id,attr"`
	Source string `xml:"source,attr"`
	Zone string `xml:"Zone"`
	KeyDigests []keyDigest `xml:"KeyDigest"`
}

func toDnsName(domain string) []byte {
	var outBuffer []byte
	parts := strings.Split(domain, ".")
	for _, label := range parts {
		outBuffer = append(outBuffer, byte(len(label)))
		outBuffer = append(outBuffer, label...)
	}
	return outBuffer
}

func (r *recursor) sendQuery(query *dns.Msg, nameserver, ipAddr string, dotPins *dnssecInfo) *dns.Msg {
	var conn *dns.Conn
	var err error
	if dotPins == nil || len(dotPins.dotPins) == 0 {
		conn, err = dns.Dial("udp", ipAddr+":53")
		if err != nil {
			log.Println("Encountered error setting up UDP for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " error ", err)
			answer := query.Copy()
			answer.Rcode = dns.RcodeServerFailure
			return answer
		}
	} else {
		// Implement the pinning here
		conn, err = dns.DialWithTLS("tcp", ipAddr+":853", &tls.Config{
			InsecureSkipVerify: true,
			ServerName: nameserver,
			VerifyPeerCertificate: func(certificates [][]byte, _ [][]*x509.Certificate) error {
				certs := make([]*x509.Certificate, len(certificates))
				for i, asn1Data := range certificates {
					cert, err := x509.ParseCertificate(asn1Data)
					if err != nil {
						return errors.New("tls: failed to parse certificate from server: " + err.Error())
					}
					certs[i] = cert
				}
				// Assume that the first cert is probably the right one
				cert := certs[0]
				hashData := []byte(toDnsName(dns.CanonicalName(dotPins.domain)))
				hashData = append(hashData,  0,0, 3, byte(r.pinalg))
				hashData = append(hashData, cert.RawSubjectPublicKeyInfo...)
				hash := sha256.Sum256(hashData)
				for _, pin := range dotPins.dotPins {
					if bytes.Compare(hash[:], pin) == 0 {
						return nil
					}
				}

				return errors.New("invalid public key received")
			},
		})
		if err != nil {
			log.Println("Encountered error setting up DoT for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " pin ", dotPins, " error ", err)
			answer := query.Copy()
			answer.Rcode = dns.RcodeServerFailure
			return answer
		}
	}

	err = conn.WriteMsg(query)
	if err != nil {
		log.Println("Encountered error sending message for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " pin ", dotPins, " error ", err)
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}
	resp, err := conn.ReadMsg()
	if err != nil {
		log.Println("Encountered error receiving message for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " pin ", dotPins, " error ", err)
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}

	if (dotPins != nil && len(dotPins.dotPins) > 0) || !resp.Truncated {
		return resp
	}
	conn, err = dns.Dial("tcp", ipAddr+":53")
	if err != nil {
		log.Println("Encountered error setting up TCP for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " error ", err)
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}
	err = conn.WriteMsg(query)
	if err != nil {
		log.Println("Encountered error sending message for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " pin ", dotPins, " error ", err)
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}
	resp, err = conn.ReadMsg()
	if err != nil {
		log.Println("Encountered error receiving message for query", query, " at nameserver ", nameserver, " ip ", ipAddr, " pin ", dotPins, " error ", err)
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}
	return resp
}

func (r* recursor) selectNameServer(nameServers []*dns.NS) (*dns.NS, string) {
	rand.Seed(time.Now().Unix())
	nameServer := nameServers[rand.Intn(len(nameServers))]
	ipAddrs, ok := r.glues[nameServer.Ns]
	if !ok {
		return nil, ""
	}
	ipAddr := selectIp(ipAddrs)

	return nameServer, ipAddr
}

func selectIp(ipAddrs []string) string {
	rand.Seed(time.Now().Unix())
	return ipAddrs[rand.Intn(len(ipAddrs))]
}

func makeQuestion(domain string, qtype uint16) *dns.Msg {
	o := &dns.OPT{
		Hdr: dns.RR_Header{
			Name:   ".",
			Rrtype: dns.TypeOPT,
		},
	}
	o.SetDo()

	return &dns.Msg{
		Question: []dns.Question{
			dns.Question{Name: domain, Qtype: qtype, Qclass: dns.ClassINET},
		},
		Extra: []dns.RR{
			o,
		},
	}
}

func (r *recursor) addGlues(records []dns.RR) {
	for _, rec := range records {
		switch t := rec.(type) {
		case *dns.A:
			glueRecs, ok := r.glues[t.Header().Name]
			if !ok {
				r.glues[t.Header().Name] = []string{t.A.String()}
			} else {
				found := false
				for _, glue := range glueRecs {
					if glue == t.A.String() {
						found = true
						break
					}
				}
				if !found {
					r.glues[t.Header().Name] = append(glueRecs, t.A.String())
				}
			}
		}
	}
}

func (r *recursor) handleDsReponse(domain string, records []dns.RR, dnssec *dnssecInfo) *dnssecInfo {
	var nextPins *dnssecInfo
	nextPins = nil

	rrsigs := []*dns.RRSIG{}
	dsSet := []dns.RR{}
	for _, rr := range records {
		switch t := rr.(type) {
		case *dns.DS:
			if r.pinalg != 255 && t.Algorithm == r.pinalg {
				decodedPin,_ := hex.DecodeString(t.Digest)
				if nextPins == nil {
					nextPins = &dnssecInfo{domain: domain, dotPins: [][]byte{decodedPin}}
				} else {
					nextPins.dotPins = append(nextPins.dotPins, decodedPin)
				}
			} else {
				if nextPins == nil {
					nextPins = &dnssecInfo{domain: domain, dsRecords: []*dns.DS{t}}
				} else {
					nextPins.dsRecords = append(nextPins.dsRecords, t)
				}
			}
			dsSet = append(dsSet, rr)
		case *dns.RRSIG:
			if t.TypeCovered == dns.TypeDS {
				rrsigs = append(rrsigs, t)
			}
		}
	}

	valid := false
	for _,rrsig := range rrsigs {
		keyTag := rrsig.KeyTag
		for _, key := range dnssec.keys {
			if keyTag == key.KeyTag() {
				if rrsig.Verify(key, dsSet) == nil {
					valid = true
					break
				}
			}
		}
		if valid {
			break
		}
	}

	if !valid {
		panic(errors.New("Unable to validate record"))
	}

	return nextPins
}

func (r *recursor) handleUnauthoritativeResponse(domain string, records []dns.RR, dnssec *dnssecInfo) ([]*dns.NS, *dnssecInfo) {
	var nextPins *dnssecInfo
	nextPins = nil
	nextNameservers := []*dns.NS{}
	rrsigs := []*dns.RRSIG{}
	dsSet := []dns.RR{}
	for _,rr := range records {
		switch t := rr.(type) {
		case *dns.NS:
			nextNameservers = append(nextNameservers, t)
		case *dns.DS:
			if r.pinalg != 255 && t.Algorithm == r.pinalg {
				decodedPin,_ := hex.DecodeString(t.Digest)
				if nextPins == nil {
					nextPins = &dnssecInfo{domain: domain, dotPins: [][]byte{decodedPin}}
				} else {
					nextPins.dotPins = append(nextPins.dotPins, decodedPin)
				}
			} else {
				if nextPins == nil {
					nextPins = &dnssecInfo{domain: domain, dsRecords: []*dns.DS{t}}
				} else {
					nextPins.dsRecords = append(nextPins.dsRecords, t)
				}
			}
			dsSet = append(dsSet, rr)
		case *dns.RRSIG:
			if t.TypeCovered == dns.TypeDS {
				rrsigs = append(rrsigs, t)
			}
		}
	}
	valid := false
	for _,rrsig := range rrsigs {
		keyTag := rrsig.KeyTag
		for _, key := range dnssec.keys {
			if keyTag == key.KeyTag() {
				if rrsig.Verify(key, dsSet) == nil {
					valid = true
					break
				}
			}
		}
		if valid {
			break
		}
	}

	if !valid {
		panic(errors.New("Unable to validate record"))
	}

	return nextNameservers, nextPins
}

func (r *recursor) doLookup(domain string, qtype uint16) *dns.Msg {
	query := makeQuestion(domain, qtype)
	labels := strings.Split(domain, ".")
	currentNameservers := r.rootNameservers
	currentDnssecData := &dnssecInfo{
		domain: ".",
		dsRecords: r.trustAnchors,
	}
	currentZone := "."
	for i := len(labels) - 1; i >= 0; i-- {
		nameserver, ipaddr := r.selectNameServer(currentNameservers)
		if nameserver == nil {
			log.Println("Unable to find valid nameservers", currentNameservers, r.glues)
			fmt.Println()
			answer := query.Copy()
			answer.Rcode = dns.RcodeServerFailure
			return answer
		}

		if currentDnssecData != nil && len(currentDnssecData.dsRecords) > 0 && len(currentDnssecData.keys) == 0 {
			// We don't have our keys yet, lets fetch them.
			dnskeyQuestion := makeQuestion(currentZone, dns.TypeDNSKEY)

			dnskeyAnswer := r.sendQuery(dnskeyQuestion, nameserver.Ns, ipaddr, currentDnssecData)

			if dnskeyAnswer.Authoritative == false {
				log.Println("Unable to find dnskeys ", nameserver, ipaddr)
				log.Println()
				answer := query.Copy()
				answer.Rcode = dns.RcodeServerFailure
				return answer
			}

			dnskeys := []*dns.DNSKEY{}
			dnskeyRRs := []dns.RR{}
			rrsigs := []*dns.RRSIG{}
			for _,record := range dnskeyAnswer.Answer {
				switch t := record.(type) {
				case *dns.DNSKEY:
					dnskeys = append(dnskeys, t)
					dnskeyRRs = append(dnskeyRRs, record)
				case *dns.RRSIG:
					if t.TypeCovered == dns.TypeDNSKEY {
						rrsigs = append(rrsigs, t)
					}
				}
			}

			trustedKeys := []*dns.DNSKEY{}
			for _,key := range dnskeys {
				for _,ds := range currentDnssecData.dsRecords {
					if ds.KeyTag == key.KeyTag() {
						tempDs := key.ToDS(ds.DigestType)
						if strings.ToLower(tempDs.Digest) == strings.ToLower(ds.Digest) {
							trustedKeys = append(trustedKeys, key)
							break
						}
					}
				}
			}

			goodSign := false
			for _,rrsig := range rrsigs {
				for _, trustedKey := range trustedKeys {
					if rrsig.KeyTag == trustedKey.KeyTag() && rrsig.Verify(trustedKey, dnskeyRRs) == nil {
						goodSign = true
						break
					}
				}
			}
			if !goodSign {
				log.Println("Invalid DNSKEYs ", nameserver, ipaddr, dnskeyAnswer)
				answer := query.Copy()
				answer.Rcode = dns.RcodeServerFailure
				return answer
			}
			currentDnssecData.keys = dnskeys
		}

		parts := strings.Join(labels[i:len(labels)], ".")
		if !strings.HasSuffix(parts, ".") {
			parts = parts + "."
		}
		question := makeQuestion(parts, dns.TypeSOA)

		answer := r.sendQuery(question, nameserver.Ns, ipaddr, currentDnssecData)

		if answer.Rcode != dns.RcodeSuccess {
			answer.Question = query.Question
			return answer
		}

		if answer.Authoritative && parts != currentZone {
			// This means we may have crossed a zone boundary
			cname := false
			soa := false
			for _,rr := range answer.Answer {
				switch rr.Header().Rrtype {
				case dns.TypeSOA:
					soa = true
				case dns.TypeCNAME:
					cname = true
				}
			}

			if soa && !cname {
				// This is definitely a zone cut on the same nameserver, lets ask the "parent" for DS records
				question.Question[0].Qtype = dns.TypeDS
				answer = r.sendQuery(question, nameserver.Ns, ipaddr, currentDnssecData)
				// DS might be in answer or Ns section, lets look in both
				currentDnssecData = r.handleDsReponse(parts, append(answer.Answer, answer.Ns...), currentDnssecData)
				currentZone = parts
			}
			// Guess we are just still in the current zone, moving on
		} else if !answer.Authoritative {
			// Lets see if we have some new nameservers
			nextNameservers, nextPins := r.handleUnauthoritativeResponse(parts, answer.Ns, currentDnssecData)

			if len(nextNameservers) == 0 {
				// Some nameservers
				log.Println("Unable to find valid nameservers")
				answer := query.Copy()
				answer.Rcode = dns.RcodeServerFailure
				return answer
			}

			r.addGlues(answer.Extra)

			var goodNameservers []*dns.NS
			for _, nextNameserver := range nextNameservers {
				_, ok := r.glues[nextNameserver.Ns]
				if ok {
					goodNameservers = append(goodNameservers, nextNameserver)
					continue
				}
				// Missing glue
				if !dns.IsSubDomain(nextNameserver.Header().Name, nextNameserver.Ns) {
					answer := r.doLookup(nextNameserver.Ns, dns.TypeA)
					if answer.Answer != nil && len(answer.Answer) > 0 {
						r.addGlues(answer.Answer)
					}
					_, ok = r.glues[nextNameserver.Ns]
					if ok {
						goodNameservers = append(goodNameservers, nextNameserver)
					}
				}
			}
			currentNameservers = goodNameservers
			currentDnssecData = nextPins
			currentZone = parts
		}
	}

	nameserver, ipaddr := r.selectNameServer(currentNameservers)
	if nameserver == nil {
		log.Println("Unable to find valid nameservers", currentNameservers, r.glues)
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}

	answer := r.sendQuery(query, nameserver.Ns, ipaddr, currentDnssecData)

	var cname *dns.CNAME
	cname = nil
	other := false
	for _,rr := range answer.Answer {
		switch t := rr.(type) {
		case *dns.CNAME:
			cname = t
		default:
			other = true
		}
	}

	if cname != nil && !other {
		nextAnswer := r.doLookup(cname.Target,qtype)
		answer.Rcode = nextAnswer.Rcode
		answer.Answer = append(answer.Answer, nextAnswer.Answer...)
		answer.Ns = append(answer.Ns, nextAnswer.Ns...)
	}

	return answer
}

func main() {
	rootHintsLocation := flag.String("rootHintsLocation", "http://www.internic.net/domain/named.root", "Where to get the root hints. Can be a HTTP url or a local file")
	rootTrustAnchorLocation := flag.String("rootTrustAnchorLocation", "https://data.iana.org/root-anchors/root-anchors.xml", "Where to get the root trust anchor. Can be a HTTP url or a local file")
	qtype := flag.String("qtype", "A", "What type to resolve")
	pinalg := flag.Uint("dotPinAlgorithm", 255, "Algorithm number used for DoT pinning, 255 turns it off")

	flag.Parse()

	var rootFile io.Reader
	if strings.HasPrefix(*rootHintsLocation, "http") {
		client := &http.Client{}
		resp, err := client.Get(*rootHintsLocation)
		if err != nil {
			fmt.Println("Unable to fetch root hints, error: ", err)
			os.Exit(1)
		}
		rootFile = resp.Body
	} else {
		file, err := os.Open(*rootHintsLocation)
		if err != nil {
			fmt.Println("Unable to open root hints, error: ", err)
			os.Exit(1)
		}
		rootFile = file
	}

	rootZoneHints := dns.NewZoneParser(rootFile, ".", "")

	var rootNameservers []*dns.NS
	rootGlues := make(map[string][]string)

	for rr, eof := rootZoneHints.Next(); eof; rr, eof = rootZoneHints.Next() {
		switch t := rr.(type) {
		case *dns.NS:
			rootNameservers = append(rootNameservers, t)
		case *dns.A:
			glue, ok := rootGlues[rr.Header().Name]
			if !ok {
				rootGlues[rr.Header().Name] = []string{t.A.String()}
			} else {
				rootGlues[rr.Header().Name] = append(glue, t.A.String())
			}
		}
	}

	var rootAnchor io.Reader
	if strings.HasPrefix(*rootTrustAnchorLocation, "http") {
		client := &http.Client{}
		resp, err := client.Get(*rootTrustAnchorLocation)
		if err != nil {
			fmt.Println("Unable to fetch root anchor, error: ", err)
			os.Exit(1)
		}
		rootAnchor = resp.Body
	} else {
		file, err := os.Open(*rootTrustAnchorLocation)
		if err != nil {
			fmt.Println("Unable to open root anchor, error: ", err)
			os.Exit(1)
		}
		rootAnchor = file
	}
	rootAnchorData,err := ioutil.ReadAll(rootAnchor)
	if err != nil {
		fmt.Println("Unable to read root anchor, error: ", err)
		os.Exit(1)
	}

	var rootTrustAnchor trustAnchor
	err = xml.Unmarshal(rootAnchorData, &rootTrustAnchor)
	if err != nil {
		fmt.Println("Failed to unmarshal root anchor, error: ", err)
		os.Exit(1)
	}
	trustDSes := []*dns.DS{}
	for _,anchor := range rootTrustAnchor.KeyDigests {
		validUntil,err := time.Parse(time.RFC3339, anchor.ValidUntil)
		if err != nil && anchor.ValidUntil != "" {
			fmt.Println("Unable to parse trust anchor ValidUntil, error: ", err)
			os.Exit(1)
		}
		if anchor.ValidUntil == "" || validUntil.After(time.Now()) {
			trustDSes = append(trustDSes, &dns.DS{
				Hdr: dns.RR_Header{
					Name: rootTrustAnchor.Zone,
					Rrtype: dns.TypeDS,
					Class: dns.ClassINET,
					Ttl: 0,
				},
				Algorithm: anchor.Algorithm,
				KeyTag: anchor.KeyTag,
				DigestType: anchor.DigestType,
				Digest: anchor.Digest,
			})
		}
	}

	qtypeVal, ok  := dns.StringToType[*qtype]
	if !ok {
		log.Println("Invalid Qtype provided: ", qtype)
		return
	}

	domain := flag.Arg(0)
	if domain == "" {
		log.Println("Please provide a domain to resolve as an argument")
		return
	}

	if *pinalg > 255 {
		log.Println("Please provide a dotPinAlgorithm between 0 and 254")
	}

	if !strings.HasSuffix(domain, ".") {
		domain = domain+"."
	}

	recursorInstance := newRecursor(rootNameservers, trustDSes, rootGlues, uint8(*pinalg))

	result := recursorInstance.doLookup(domain, qtypeVal)

	fmt.Println(result)
}
