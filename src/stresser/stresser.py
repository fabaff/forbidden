#!/usr/bin/env python3

import datetime, sys, os, io, tempfile, random, json, regex as re, threading, concurrent.futures, subprocess, socket, pycurl, requests, urllib.parse, copy, colorama, termcolor

start = datetime.datetime.now()

colorama.init(autoreset = True)

requests.packages.urllib3.disable_warnings(requests.packages.urllib3.exceptions.InsecureRequestWarning)

# ----------------------------------------

default_quotes = "'"

def escape_quotes(value):
	return str(value).replace(default_quotes, ("\\{0}").format(default_quotes))

def set_param(value, param = ""):
	tmp = default_quotes + escape_quotes(value) + default_quotes
	if param:
		tmp = ("{0} {1}").format(param, tmp)
	return tmp

# ----------------------------------------

def get_base_https_url(scheme, dnp, port, full_path):
	return ("https://{0}:{1}{2}").format(dnp, port if scheme == "https" else 443, full_path)

def get_base_http_url(scheme, dnp, port, full_path):
	return ("http://{0}:{1}{2}").format(dnp, port if scheme == "http" else 80, full_path)

# NOTE: Extends domain names or IPs.
def get_all_domains(scheme, dnps, port):
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

# ----------------------------------------

fs_const = "/"

def replace_multiple_slashes(path):
	return re.sub(r"\/{2,}", fs_const, path)

def prepend_slash(path):
	if not path.startswith(fs_const):
		path = fs_const + path
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
				tmp.append(base.rstrip(fs_const) + prepend_slash(path) if path else base)
	return unique(tmp)

def extend_path(path, query_string = "", fragment = ""):
	tmp = []
	path = path.strip(fs_const)
	if not path:
		tmp.append(fs_const)
	else:
		tmp.extend([fs_const + path + fs_const, path + fs_const, fs_const + path, path])
	tmp = [entry + query_string + fragment for entry in tmp]
	return unique(tmp)

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

default_user_agent = "Stresser/10.1"

# NOTE: Returns a user agents list (string array) on success.
# NOTE: Returns the default user agent (string) on failure.
def get_user_agents():
	tmp = []
	file = os.path.join(os.path.abspath(os.path.split(__file__)[0]), "user_agents.txt")
	if os.path.isfile(file) and os.access(file, os.R_OK) and os.stat(file).st_size > 0:
		with open(file, "r", encoding = default_encoding) as stream:
			for line in stream:
				line = line.strip()
				if line:
					tmp.append(line)
		stream.close()
	if not tmp:
		tmp = default_user_agent
	return tmp

# NOTE: Returns a random user agent (string) on success.
# NOTE: Returns the default user agent (string) on failure.
def get_random_user_agent():
	tmp = get_user_agents()
	if isinstance(tmp, list):
		tmp = tmp[random.randint(0, len(tmp) - 1)]
	return tmp

# ----------------------------------------

class Stresser:

	def __init__(self, url, ignore_qsf, ignore_curl, force, ignore, lengths, repeat, threads, agent, proxy, directory, debug):
		# --------------------------------
		# NOTE: User-controlled input.
		self.__url             = self.__parse_url(url, bool(ignore_qsf))
		self.__force           = force
		self.__ignore          = ignore
		self.__lengths         = lengths
		self.__repeat          = repeat
		self.__threads         = threads
		self.__agent           = agent
		self.__proxy           = proxy
		self.__directory       = directory
		self.__debug           = debug
		# --------------------------------
		# NOTE: Python cURL configuration.
		self.__curl            = not bool(ignore_curl)
		self.__verify          = False # NOTE: Ignore SSL/TLS verification.
		self.__allow_redirects = True
		self.__max_redirects   = 10
		self.__connect_timeout = 60
		self.__read_timeout    = 90
		self.__encoding        = "UTF-8" # NOTE: ISO-8859-1 works better than UTF-8 to access files.
		self.__regex_flags     = re.MULTILINE | re.IGNORECASE
		# --------------------------------
		self.__error           = False
		self.__print_lock      = threading.Lock()
		self.__default_method  = "GET"
		self.__allowed_methods = []
		self.__collection      = []
		self.__identifier      = 0
		self.__total           = 0
		self.__progress        = 0

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
		fragment["parsed"] = {} # NOTE: Not needed.
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

	def __add_lengths(self, lengths):
		if not isinstance(lengths, list):
			lengths = [lengths]
		self.__lengths = unique(self.__lengths + lengths)

	def get_results(self):
		return self.__collection

	def __print_error(self, text):
		self.__error = True
		print_red(("ERROR: {0}").format(text))

	def __print_progress(self):
		with self.__print_lock:
			print(("Progress: {0}/{1} | {2:.2f}%").format(self.__progress, self.__total, (self.__progress / self.__total) * 100), end = "\n" if self.__progress == self.__total else "\r")

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
		self.__validate_inaccessible_url()
		if not self.__error:
			self.__fetch_inaccessible_ip()
			if not self.__error:
				self.__set_allowed_http_methods()
				self.__prepare_collection()
				if not self.__collection:
					print("No test records were created")
				else:
					self.__total = len(self.__collection)
					print_cyan(("Number of created test records: {0}").format(self.__total))
					self.__run_tests()
					self.__validate_results()

	def __validate_inaccessible_url(self):
		# --------------------------------
		print_cyan(("Normalized inaccessible URL: {0}").format(self.__url["urls"]["base"]))
		print_time("Validating the inaccessible URL...")
		record = self.__fetch(url = self.__url["urls"]["base"], method = "GET")
		if not (record["code"] > 0):
			self.__print_error("Cannot validate the inaccessible URL, script will exit shortly...")
		elif "base" in self.__lengths:
			print_green(("Ignoring the inaccessible URL response content length: {0}").format(record["length"]))
			self.__lengths.pop(self.__lengths.index("base"))
			self.__add_lengths(record["length"])
		# --------------------------------

	def __fetch_inaccessible_ip(self):
		# --------------------------------
		print_time("Fetching IP of the inaccessible URL...")
		self.__url = self.__parse_ip(copy.deepcopy(self.__url))
		if not self.__url["ip_no_port"]:
			self.__print_error("Cannot fetch IP of the inaccessible URL, script will exit shortly...")
		# --------------------------------

	def __set_allowed_http_methods(self):
		# --------------------------------
		if self.__force:
			print_cyan(("Forcing HTTP {0} method for all non-specific test cases...").format(self.__force))
			self.__allowed_methods = [self.__force]
		# --------------------------------
		else:
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
				print_cyan(("Cannot fetch allowed HTTP methods, defaulting to HTTP {0} method for all non-specific test cases...").format(self.__default_method))
				self.__allowed_methods = [self.__default_method]
			else:
				print_green(("Allowed HTTP methods: [{0}]").format((", ").join(self.__allowed_methods)))
		# --------------------------------

	def __fetch(self, url, method = None, headers = None, body = None, agent = None, proxy = None, curl = None, passthrough = True):
		record = self.__record("SYSTEM-0", url, method, headers, body, agent, proxy, curl)
		return self.__send_curl(record, passthrough) if record["curl"] else self.__send_request(record, passthrough)

	def __records(self, identifier, urls, methods = None, headers = None, body = None, agent = None, proxy = None, curl = None, repeat = None):
		if not isinstance(urls, list):
			urls = [urls]	
		if not isinstance(methods, list):
			methods = [methods]
		if not repeat:
			repeat = self.__repeat
		if headers:
			for url in urls:
				for method in methods:
					for header in headers:
						if not isinstance(header, list):
							# NOTE: Python cURL accepts only string arrays as HTTP request headers.
							header = [header]
						for i in range(repeat):
							self.__collection.append(self.__record(identifier, url, method, header, body, agent, proxy, curl))
		else:
			for url in urls:
				for method in methods:
					for i in range(repeat):
						self.__collection.append(self.__record(identifier, url, method, [], body, agent, proxy, curl))

	def __record(self, identifier, url, method, headers, body, agent, proxy, curl):
		self.__identifier += 1
		# identifier = ("{0}-{1}").format(self.__identifier, identifier)
		if not method:
			method = self.__force if self.__force else self.__default_method
		if not agent:
			agent = self.__agent[random.randint(0, len(self.__agent) - 1)] if isinstance(self.__agent, list) else self.__agent
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
			"agent"           : agent,
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
		tmp = ["curl", set_param(self.__connect_timeout, "--connect-timeout"), set_param(self.__read_timeout, "-m"), "-iskL", set_param(self.__max_redirects, "--max-redirs"), "--path-as-is"]
		if record["body"]:
			tmp.append(set_param(record["body"], "-d"))
		if record["proxy"]:
			tmp.append(set_param(record["proxy"], "-x"))
		if record["agent"]:
			tmp.append(set_param(record["agent"], "-A"))
		if record["headers"]:
			for header in record["headers"]:
				tmp.append(set_param(header, "-H"))
		tmp.append(set_param(record["method"], "-X"))
		tmp.append(set_param(record["url"]))
		tmp = (" ").join(tmp)
		return tmp

	def __run_tests(self):
		results = []
		print_time(("Running tests with {0} engine...").format("PycURL" if self.__curl else "Python Requests"))
		print("Press CTRL + C to exit early - results will be saved")
		self.__print_progress()
		with concurrent.futures.ThreadPoolExecutor(max_workers = self.__threads) as executor:
			subprocesses = []
			try:
				for record in self.__collection:
					subprocesses.append(executor.submit(self.__send_curl if record["curl"] else self.__send_request, record))
				for subprocess in concurrent.futures.as_completed(subprocesses):
					results.append(subprocess.result())
					self.__progress += 1
					self.__print_progress()
			except KeyboardInterrupt:
				executor.shutdown(wait = True, cancel_futures = True)
		self.__collection = results

	def __send_curl(self, record, passthrough = False):
		curl = None
		cookiefile = None
		headers = None
		response = None
		try:
			# --------------------------------
			curl = pycurl.Curl()
			# --------------------------------
			cookiefile = tempfile.NamedTemporaryFile(mode = "r") # NOTE: Important! Store and pass HTTP cookies on HTTP redirects.
			curl.setopt(pycurl.COOKIESESSION, True)
			curl.setopt(pycurl.COOKIEFILE, cookiefile.name)
			curl.setopt(pycurl.COOKIEJAR, cookiefile.name)
			# --------------------------------
			if passthrough:
				headers = io.BytesIO()
				curl.setopt(pycurl.HEADERFUNCTION, headers.write)
			# --------------------------------
			response = io.BytesIO()
			curl.setopt(pycurl.WRITEFUNCTION, response.write)
			# --------------------------------
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
			# --------------------------------
			# NOTE: Important! Encode Unicode characters.
			curl.setopt(pycurl.URL, record["url"])
			curl.setopt(pycurl.CUSTOMREQUEST, record["method"])
			if record["method"] in ["HEAD"]:
				curl.setopt(pycurl.NOBODY, True)
			if record["agent"]:
				curl.setopt(pycurl.USERAGENT, self.__encode(record["agent"]))
			if record["headers"]:
				curl.setopt(pycurl.HTTPHEADER, self.__encode(record["headers"])) # Will override 'User-Agent' HTTP request header.
			if record["body"]:
				curl.setopt(pycurl.POSTFIELDS, record["body"])
			if record["proxy"]:
				curl.setopt(pycurl.PROXY, record["proxy"])
			# --------------------------------
			curl.perform()
			# --------------------------------
			record["code"] = int(curl.getinfo(pycurl.RESPONSE_CODE))
			record["length"] = int(curl.getinfo(pycurl.SIZE_DOWNLOAD))
			record["id"] = ("{0}-{1}-{2}").format(record["code"], record["length"], record["id"])
			content = response.getvalue()
			if passthrough:
				record["response_headers"] = self.__decode(headers.getvalue())
				# record["response"] = self.__decode(content)
			elif record["length"] in self.__lengths or (self.__ignore and re.search(self.__ignore, self.__decode(content), self.__regex_flags)):
				record["code"] = -1
			# NOTE: Additional validation to prevent congestion from writing large and usless data to files.
			elif record["code"] >= 200 and record["code"] < 400:
				file = os.path.join(self.__directory, ("{0}.txt").format(record["id"]))
				if not os.path.exists(file):
					open(file, "wb").write(content)
			# --------------------------------
		except (pycurl.error, FileNotFoundError) as ex:
			# --------------------------------
			self.__print_debug(ex, ("{0}: {1}").format(record["id"], record["command"]))
			# --------------------------------
		finally:
			# --------------------------------
			if response:
				response.close()
			# --------------------------------
			if headers:
				headers.close()
			# --------------------------------
			if curl:
				curl.close()
			# --------------------------------
			if cookiefile:
				cookiefile.close() # NOTE: Important! Close the file handle strictly after closing the cURL handle.
			# --------------------------------
		return record

	def __send_request(self, record, passthrough = False):
		session = None
		response = None
		try:
			# --------------------------------
			session = requests.Session()
			session.max_redirects = self.__max_redirects
			# --------------------------------
			session.cookies.clear()
			# --------------------------------
			request = requests.Request(
				record["method"],
				record["url"]
			)
			if record["agent"]:
				request.headers["User-Agent"] = self.__encode(record["agent"])
			if record["headers"]:
				self.__set_double_headers(request, record["headers"]) # Will override 'User-Agent' HTTP request header.
			if record["body"]:
				request.data = record["body"]
			if record["proxy"]:
				session.proxies["https"] = session.proxies["http"] = record["proxy"]
			# --------------------------------
			prepared = session.prepare_request(request)
			prepared.url = record["url"]
			# --------------------------------
			response = session.send(
				prepared,
				verify = self.__verify,
				allow_redirects = self.__allow_redirects,
				timeout = (self.__connect_timeout, self.__read_timeout)
			)
			# --------------------------------
			record["code"] = int(response.status_code)
			record["length"] = len(response.content)
			record["id"] = ("{0}-{1}-{2}").format(record["code"], record["length"], record["id"])
			content = response.content
			if passthrough:
				record["response_headers"] = dict(response.headers)
				# record["response"] = self.__decode(content)
			elif record["length"] in self.__lengths or (self.__ignore and re.search(self.__ignore, self.__decode(content), self.__regex_flags)):
				record["code"] = -1
			# NOTE: Additional validation to prevent congestion from writing large and usless data to files.
			elif record["code"] >= 200 and record["code"] < 400:
				file = os.path.join(self.__directory, ("{0}.txt").format(record["id"]))
				if not os.path.exists(file):
					open(file, "wb").write(content)
			# --------------------------------
		except (requests.packages.urllib3.exceptions.LocationParseError, requests.exceptions.RequestException, FileNotFoundError) as ex:
			# --------------------------------
			self.__print_debug(ex, ("{0}: {1}").format(record["id"], record["command"]))
			# --------------------------------
		finally:
			# --------------------------------
			if response:
				response.close()
			# --------------------------------
			if session:
				session.close()
			# --------------------------------
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
		self.__mark_duplicates()
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
		self.__total = len(self.__collection)
		table.show()

	def __mark_duplicates(self):
		exists = set()
		for record in self.__collection:
			if record["id"] not in exists and not exists.add(record["id"]):
				continue
			record["code"] = -2

	def __prepare_collection(self):
		print_time("Preparing test records...")
		# --------------------------------
		# NOTE: Stress testing.
		self.__records(
			identifier = "STRESS-1",
			urls       = self.__url["urls"]["base"]
		)

# ----------------------------------------

class Table:

	def __init__(self, collection):
		self.__table     = self.__init_table(collection)
		self.__has_valid = any(code > 0 for code in self.__table)

	def __init_table(self, collection):
		table = {}
		for record in collection:
			if record["code"] not in table:
				table[record["code"]] = 0
			table[record["code"]] += 1
		table = dict(sorted(table.items()))
		return table

	def __table_horizontal_border(self):
		print_white("-" * 27)

	def __format_row(self, key, value):
		return ("| {0:<10} | {1:<10} |").format(key, value)

	def show(self):
		if self.__has_valid:
			self.__table_horizontal_border()
			print_white(self.__format_row("Code", "Count"))
			self.__table_horizontal_border()
			for code in self.__table:
				if code >= 500:
					print_cyan(self.__format_row(code, self.__table[code]))
				elif code >= 400:
					print_red(self.__format_row(code, self.__table[code]))
				elif code >= 300:
					print_yellow(self.__format_row(code, self.__table[code]))
				elif code >= 200:
					print_green(self.__format_row(code, self.__table[code]))
				elif code > 0:
					print_white(self.__format_row(code, self.__table[code]))
		self.__table_horizontal_border()
		if 0 in self.__table:
			print_white(self.__format_row("Errors", self.__table[0]))
			self.__table_horizontal_border()
		if -1 in self.__table:
			print_white(self.__format_row("Ignored", self.__table[-1]))
			self.__table_horizontal_border()
		if -2 in self.__table:
			print_white(self.__format_row("Duplicates", self.__table[-2]))
			self.__table_horizontal_border()

# ----------------------------------------

# my own validation algorithm

class Validate:

	def __init__(self):
		self.__proceed = True
		self.__args    = {
			"url"        : None,
			"ignore_qsf" : None,
			"ignore_curl": None,
			"force"      : None,
			"ignore"     : None,
			"lengths"    : None,
			"repeat"     : None,
			"threads"    : None,
			"agent"      : None,
			"proxy"      : None,
			"out"        : None,
			"directory"  : None,
			"debug"      : None
		}

	def __basic(self):
		self.__proceed = False
		print("Stresser v10.1 ( github.com/ivan-sincek/forbidden )")
		print("")
		print("Usage:   stresser -u url                        -dir directory -r repeat -th threads [-f force] [-o out         ]")
		print("Example: stresser -u https://example.com/secret -dir results   -r 1000   -th 200     [-f GET  ] [-o results.json]")

	def __advanced(self):
		self.__basic()
		print("")
		print("DESCRIPTION")
		print("    Bypass 4xx HTTP response status codes with stress testing")
		print("URL")
		print("    Inaccessible URL")
		print("    -u <url> - https://example.com/secret | etc.")
		print("IGNORE QSF")
		print("    Ignore URL query string and fragment")
		print("    -iqsf <ignore-qsf> - yes")
		print("IGNORE CURL")
		print("    Use Python Requests instead of PycURL")
		print("    -ic <ignore-curl> - yes")
		print("FORCE")
		print("    Force an HTTP method for all non-specific test cases")
		print("    -f <force> - GET | POST | CUSTOM | etc.")
		print("IGNORE")
		print("    Filter out 200 OK false positive results with RegEx")
		print("    Spacing will be stripped")
		print("    -i <ignore> - Inaccessible | \"Access Denied\" | etc.")
		print("LENGTHS")
		print("    Filter out 200 OK false positive results by HTTP response content lengths")
		print("    Specify 'base' to ignore content length of the base HTTP response")
		print("    Use comma-separated values")
		print("    -l <lengths> - 12 | base | etc.")
		print("REPEAT")
		print("    Number of total HTTP requests to send for each test case")
		print("    -r <repeat> - 1000 | etc.")
		print("THREADS")
		print("    Number of parallel threads to run")
		print("    -th <threads> - 200 | etc.")
		print("AGENT")
		print("    User agent to use")
		print(("    Default: {0}").format(default_user_agent))
		print("    -a <agent> - curl/3.30.1 | random[-all] | etc.")
		print("PROXY")
		print("    Web proxy to use")
		print("    -x <proxy> - http://127.0.0.1:8080 | etc.")
		print("OUT")
		print("    Output file")
		print("    -o <out> - results.json | etc.")
		print("DIRECTORY")
		print("    Output directory")
		print("    All valid and unique HTTP responses will be saved in this directory")
		print("    -dir <directory> - results | etc.")
		print("DEBUG")
		print("    Debug output")
		print("    -dbg <debug> - yes")

	def __print_error(self, msg):
		print(("ERROR: {0}").format(msg))

	def __error(self, msg, help = False):
		self.__proceed = False
		self.__print_error(msg)
		if help:
			print("Use -h for basic and --help for advanced info")

	def __parse_url(self, url, key):
		data = {
			"url": {
				"schemes": ["http", "https"],
				"scheme_error": [
					"Inaccessible URL scheme is required",
					"Supported inaccessible URL schemes are 'http' and 'https'"
				],
				"domain_error": "Invalid inaccessible domain name",
				"port_error": "Inaccessible port number is out of range"
			},
			"proxy": {
				"schemes": ["http", "https", "socks4", "socks4h", "socks5", "socks5h"],
				"scheme_error": [
					"Proxy URL scheme is required",
					"Supported proxy URL schemes are 'http[s]', 'socks4[h]', and 'socks5[h]'"
				],
				"domain_error": "Invalid proxy domain name",
				"port_error": "Proxy port number is out of range"
			}
		}
		tmp = urllib.parse.urlsplit(url)
		if not tmp.scheme:
			self.__error(data[key]["scheme_error"][0])
		elif tmp.scheme not in data[key]["schemes"]:
			self.__error(data[key]["scheme_error"][1])
		elif not tmp.netloc:
			self.__error(data[key]["domain_error"])
		elif tmp.port and (tmp.port < 1 or tmp.port > 65535):
			self.__error(data[key]["port_error"])
		return url

	def __parse_content_lengths(self, string, specials):
		tmp = []
		for entry in string.split(","):
			entry = entry.strip()
			if not entry:
				continue
			elif entry in specials: # base, path
				tmp.append(entry)
			elif entry.isdigit() and int(entry) >= 0:
				tmp.append(int(entry))
			else:
				tmp = []
				break
		return unique(tmp)

	def __parse_regex(self, regex):
		try:
			re.compile(regex)
		except re.error:
			self.__error("Invalid RegEx")
		return regex

	def __validate(self, key, value):
		value = value.strip()
		if len(value) > 0:
			# --------------------
			if key == "-u" and self.__args["url"] is None:
				self.__args["url"] = self.__parse_url(value, "url")
			# --------------------
			elif key == "-iqsf" and self.__args["ignore_qsf"] is None:
				self.__args["ignore_qsf"] = value.lower()
				if self.__args["ignore_qsf"] != "yes":
					self.__error("Specify 'yes' to ignore URL query string and fragment")
			# --------------------
			elif key == "-ic" and self.__args["ignore_curl"] is None:
				self.__args["ignore_curl"] = value.lower()
				if self.__args["ignore_curl"] != "yes":
					self.__error("Specify 'yes' to use Python Requests instead of PycURL")
			# --------------------
			elif key == "-f" and self.__args["force"] is None:
				self.__args["force"] = value.upper()
			# --------------------
			elif key == "-i" and self.__args["ignore"] is None:
				self.__args["ignore"] = self.__parse_regex(value)
			# --------------------
			elif key == "-l" and self.__args["lengths"] is None:
				self.__args["lengths"] = self.__parse_content_lengths(value.lower(), ["base"])
				if not self.__args["lengths"]:
					self.__error("Content length must be either 'base' or numeric equal or greater than zero")
			# --------------------
			elif key == "-r" and self.__args["repeat"] is None:
				self.__args["repeat"] = value
				if not self.__args["repeat"].isdigit():
					self.__error("Number of total HTTP requests to send must be numeric")
				else:
					self.__args["repeat"] = int(self.__args["repeat"])
					if self.__args["repeat"] < 1:
						self.__error("Number of total HTTP requests to send must be greater than zero")
			# --------------------
			elif key == "-th" and self.__args["threads"] is None:
				self.__args["threads"] = value
				if not self.__args["threads"].isdigit():
					self.__error("Number of parallel threads to run must be numeric")
				else:
					self.__args["threads"] = int(self.__args["threads"])
					if self.__args["threads"] < 1:
						self.__error("Number of parallel threads to run must be greater than zero")
			# --------------------
			elif key == "-a" and self.__args["agent"] is None:
				self.__args["agent"] = value
			# --------------------
			elif key == "-x" and self.__args["proxy"] is None:
				self.__args["proxy"] = self.__parse_url(value, "proxy")
			# --------------------
			elif key == "-o" and self.__args["out"] is None:
				self.__args["out"] = os.path.abspath(value)
			elif key == "-dir" and self.__args["directory"] is None:
				self.__args["directory"] = os.path.abspath(value)
			# --------------------
			elif key == "-dbg" and self.__args["debug"] is None:
				self.__args["debug"] = value.lower()
				if self.__args["debug"] != "yes":
					self.__error("Specify 'yes' to enable debug output")
			# --------------------

	def __check(self, argc):
		count = 0
		for key in self.__args:
			if self.__args[key] is not None:
				count += 1
		return argc - count == argc / 2

	def run(self):
		# --------------------
		argc = len(sys.argv) - 1
		# --------------------
		if argc == 0:
			self.__advanced()
		# --------------------
		elif argc == 1:
			if sys.argv[1] == "-h":
				self.__basic()
			elif sys.argv[1] == "--help":
				self.__advanced()
			else:
				self.__error("Incorrect usage", True)
		# --------------------
		elif argc % 2 == 0 and argc <= len(self.__args) * 2:
			for i in range(1, argc, 2):
				self.__validate(sys.argv[i], sys.argv[i + 1])
			if None in [self.__args["url"], self.__args["directory"], self.__args["repeat"], self.__args["threads"]] or not self.__check(argc):
				self.__error("Missing a mandatory option (-u, -dir, -r, -th) and/or optional (-iqsf, -ic, -f, -i, -l, -a, -x, -o, -dbg)", True)
		# --------------------
		else:
			self.__error("Incorrect usage", True)
		# --------------------
		if self.__proceed:
			if not self.__args["lengths"]:
				self.__args["lengths"] = []
			if not self.__args["agent"]:
				self.__args["agent"] = default_user_agent
			elif self.__args["agent"].lower() == "random-all":
				self.__args["agent"] = get_user_agents()
			elif self.__args["agent"].lower() == "random":
				self.__args["agent"] = get_random_user_agent()
		# --------------------
		return self.__proceed
		# --------------------

	def get_arg(self, key):
		return self.__args[key]

# ----------------------------------------

def main():
	validate = Validate()
	if validate.run():
		print("##########################################################################")
		print("#                                                                        #")
		print("#                             Stresser v10.1                             #")
		print("#                                 by Ivan Sincek                         #")
		print("#                                                                        #")
		print("# Bypass 4xx HTTP response status codes  with stress testing.            #")
		print("# GitHub repository at github.com/ivan-sincek/forbidden.                 #")
		print("# Feel free to donate ETH at 0xbc00e800f29524AD8b0968CEBEAD4cD5C5c1f105. #")
		print("#                                                                        #")
		print("##########################################################################")
		out = validate.get_arg("out")
		stresser = Stresser(
			validate.get_arg("url"),
			validate.get_arg("ignore_qsf"),
			validate.get_arg("ignore_curl"),
			validate.get_arg("force"),
			validate.get_arg("ignore"),
			validate.get_arg("lengths"),
			validate.get_arg("repeat"),
			validate.get_arg("threads"),
			validate.get_arg("agent"),
			validate.get_arg("proxy"),
			validate.get_arg("directory"),
			validate.get_arg("debug")
		)
		stresser.run()
		results = stresser.get_results()
		if results and out:
			write_file(jdump(results), out)
		print(("Script has finished in {0}").format(datetime.datetime.now() - start))

if __name__ == "__main__":
	main()
