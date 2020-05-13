package main

import (
	"bytes"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
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
	glues map[string][]string
	pinalg uint8
}

func newRecursor(rootNameservers []*dns.NS, rootGlues map[string][]string, pinalg uint8) *recursor {
	return &recursor{rootNameservers: rootNameservers, glues: rootGlues, pinalg: pinalg}
}

type dotPin struct {
	domain string
	pins [][]byte
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

func (r *recursor) sendQuery(query *dns.Msg, nameserver, ipAddr string, dotPins *dotPin) *dns.Msg {
	var conn *dns.Conn
	var err error
	if dotPins == nil {
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
				for _, pin := range dotPins.pins {
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

	if dotPins != nil || !resp.Truncated {
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

func (r *recursor) handleDsReponse(domain string, records []dns.RR) *dotPin {
	var nextPins *dotPin
	nextPins = nil

	for _, rr := range records {
		switch t := rr.(type) {
		case *dns.DS:
			if r.pinalg != 255 && t.Algorithm == r.pinalg {
				decodedPin,_ := hex.DecodeString(t.Digest)
				if nextPins == nil {
					nextPins = &dotPin{domain: domain, pins: [][]byte{decodedPin}}
				} else {
					nextPins.pins = append(nextPins.pins, decodedPin)
				}
			}
		}
	}
	return nextPins
}

func (r *recursor) handleUnauthoritativeResponse(domain string, records []dns.RR) ([]*dns.NS, *dotPin) {
	var nextPins *dotPin
	nextPins = nil
	nextNameservers := []*dns.NS{}
	for _,rr := range records {
		switch t := rr.(type) {
		case *dns.NS:
			nextNameservers = append(nextNameservers, t)
		case *dns.DS:
			if r.pinalg != 255 && t.Algorithm == r.pinalg {
				decodedPin,_ := hex.DecodeString(t.Digest)
				if nextPins == nil {
					nextPins = &dotPin{domain: domain, pins: [][]byte{decodedPin}}
				} else {
					nextPins.pins = append(nextPins.pins, decodedPin)
				}
			}
		}
	}

	return nextNameservers, nextPins
}

func (r *recursor) doLookup(domain string, qtype uint16) *dns.Msg {
	query := makeQuestion(domain, qtype)
	labels := strings.Split(domain, ".")
	currentNameservers := r.rootNameservers
	var currentDotPins *dotPin
	currentDotPins = nil
	currentZone := ""
	for i := len(labels) - 1; i >= 0; i-- {
		nameserver, ipaddr := r.selectNameServer(currentNameservers)
		if nameserver == nil {
			log.Println("Unable to find valid nameservers", currentNameservers, r.glues)
			fmt.Println()
			answer := query.Copy()
			answer.Rcode = dns.RcodeServerFailure
			return answer
		}

		parts := strings.Join(labels[i:len(labels)], ".")
		if !strings.HasSuffix(parts, ".") {
			parts = parts + "."
		}
		question := makeQuestion(parts, dns.TypeSOA)

		answer := r.sendQuery(question, nameserver.Ns, ipaddr, currentDotPins)

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
				answer = r.sendQuery(question, nameserver.Ns, ipaddr, currentDotPins)
				// DS might be in answer or Ns section, lets look in both
				currentDotPins = r.handleDsReponse(parts, append(answer.Answer, answer.Ns...))
				currentZone = parts
			}
			// Guess we are just still in the current zone, moving on
		} else if !answer.Authoritative {
			// Lets see if we have some new nameservers
			nextNameservers, nextPins := r.handleUnauthoritativeResponse(parts, answer.Ns)

			if len(nextNameservers) == 0 {
				fmt.Println(nameserver, ipaddr, answer)
				fmt.Println()
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
			currentDotPins = nextPins
			currentZone = parts
		}
	}

	nameserver, ipaddr := r.selectNameServer(currentNameservers)
	if nameserver == nil {
		log.Println("Unable to find valid nameservers", currentNameservers, r.glues)
		fmt.Println()
		answer := query.Copy()
		answer.Rcode = dns.RcodeServerFailure
		return answer
	}

	answer := r.sendQuery(query, nameserver.Ns, ipaddr, currentDotPins)

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
/*		case *dns.AAAA:
			glue, ok := rootGlues[rr.Header().Name]
			if !ok {
				rootGlues[rr.Header().Name] = []string{"["+t.AAAA.String()+"]"}
			} else {
				rootGlues[rr.Header().Name] = append(glue, "["+t.AAAA.String()+"]")
			}*/
		}
	}

	qtypeVal, ok  := dns.StringToType[*qtype]
	if !ok {
		fmt.Println("Invalid Qtype provided: ", qtype)
		return
	}

	domain := flag.Arg(0)
	if domain == "" {
		fmt.Println("Please provide a domain to resolve as an argument")
		return
	}

	if *pinalg > 255 {
		fmt.Println("Please provide a dotPinAlgorithm between 0 and 254")
	}

	if !strings.HasSuffix(domain, ".") {
		domain = domain+"."
	}

	recursorInstance := newRecursor(rootNameservers, rootGlues, uint8(*pinalg))

	result := recursorInstance.doLookup(domain, qtypeVal)

	fmt.Println(result)
}
