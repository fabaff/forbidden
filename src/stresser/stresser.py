#!/usr/bin/env python3

import argparse, colorama, concurrent.futures, copy, datetime, io, json, os, pycurl, random, regex as re, requests, socket, subprocess, sys, tabulate, tempfile, termcolor, threading, urllib.parse

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

default_user_agent = "Stresser/10.4"

def get_all_user_agents():
	tmp = []
	file = os.path.join(os.path.abspath(os.path.split(__file__)[0]), "user_agents.txt")
	if os.path.isfile(file) and os.access(file, os.R_OK) and os.stat(file).st_size > 0:
		with open(file, "r", encoding = default_encoding) as stream:
			for line in stream:
				line = line.strip()
				if line:
					tmp.append(line)
	if not tmp:
		tmp.append(default_user_agent)
	return unique(tmp)

def get_random_user_agent():
	tmp = get_all_user_agents()
	return tmp[random.randint(0, len(tmp) - 1)]

# ----------------------------------------

class Stresser:

	def __init__(self, url, ignore_qsf, ignore_curl, force, ignore, content_lengths, repeat, threads, user_agents, proxy, directory, debug):
		# --------------------------------
		# NOTE: User-controlled input.
		self.__url             = self.__parse_url(url, bool(ignore_qsf))
		self.__force           = force
		self.__ignore          = ignore
		self.__content_lengths = content_lengths
		self.__repeat          = repeat
		self.__threads         = threads
		self.__user_agents     = user_agents
		self.__user_agents_len = len(self.__user_agents)
		self.__proxy           = proxy
		self.__directory       = directory
		self.__debug           = debug
		# --------------------------------
		# NOTE: Python cURL configuration.
		self.__curl            = not ignore_curl
		self.__verify          = False # NOTE: Ignore SSL/TLS verification.
		self.__allow_redirects = True
		self.__max_redirects   = 10
		self.__connect_timeout = 60
		self.__read_timeout    = 90
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
		self.__validate_inaccessible_url()
		if not self.__error:
			self.__fetch_inaccessible_ip()
			if not self.__error:
				self.__set_allowed_http_methods()
				self.__prepare_collection()
				if not self.__collection:
					print("No test records were created")
				else:
					print_cyan(("Number of created test records: {0}").format(len(self.__collection)))
					self.__run_tests()
					self.__validate_results()

	def __validate_inaccessible_url(self):
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

	def __fetch_inaccessible_ip(self):
		# --------------------------------
		print_time("Fetching the IP of inaccessible URL...")
		self.__url = self.__parse_ip(copy.deepcopy(self.__url))
		if not self.__url["ip_no_port"]:
			self.__print_error("Cannot fetch the IP of inaccessible URL, script will exit shortly...")
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
				# TO DO: Brute-force allowed HTTP methods.
			else:
				print_green(("Allowed HTTP methods: [{0}]").format((", ").join(self.__allowed_methods)))
		# --------------------------------

	def __fetch(self, url, method = None, headers = None, body = None, user_agent = None, proxy = None, curl = None, passthrough = True):
		record = self.__record("SYSTEM-0", url, method, headers, body, user_agent, proxy, curl)
		return self.__send_curl(record, passthrough) if record["curl"] else self.__send_request(record, passthrough)

	def __records(self, identifier, urls, methods = None, headers = None, body = None, user_agent = None, proxy = None, curl = None, repeat = None):
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
							self.__collection.append(self.__record(identifier, url, method, header, body, user_agent, proxy, curl))
		else:
			for url in urls:
				for method in methods:
					for i in range(repeat):
						self.__collection.append(self.__record(identifier, url, method, [], body, user_agent, proxy, curl))

	def __record(self, identifier, url, method, headers, body, user_agent, proxy, curl):
		self.__identifier += 1
		# identifier = ("{0}-{1}").format(self.__identifier, identifier)
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
			record["id"] = ("{0}-{1}-{2}").format(record["code"], record["length"], record["id"])
			content = response.getvalue()
			if passthrough:
				record["response_headers"] = self.__decode(headers.getvalue())
				# record["response"] = self.__decode(content)
			elif record["length"] in self.__content_lengths or (self.__ignore and re.search(self.__ignore, self.__decode(content), self.__regex_flags)):
				record["code"] = -1
			# NOTE: Additional validation to prevent congestion from writing large and usless data to files.
			elif record["code"] >= 200 and record["code"] < 400:
				file = os.path.join(self.__directory, ("{0}.txt").format(record["id"]))
				if not os.path.exists(file):
					open(file, "wb").write(content)
			# ----------------------------
		except (pycurl.error, FileNotFoundError) as ex:
			# --------------------------------
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
			record["id"] = ("{0}-{1}-{2}").format(record["code"], record["length"], record["id"])
			content = response.content
			if passthrough:
				record["response_headers"] = dict(response.headers)
				# record["response"] = self.__decode(content)
			elif record["length"] in self.__content_lengths or (self.__ignore and re.search(self.__ignore, self.__decode(content), self.__regex_flags)):
				record["code"] = -1
			# NOTE: Additional validation to prevent congestion from writing large and usless data to files.
			elif record["code"] >= 200 and record["code"] < 400:
				file = os.path.join(self.__directory, ("{0}.txt").format(record["id"]))
				if not os.path.exists(file):
					open(file, "wb").write(content)
			# ----------------------------
		except (requests.packages.urllib3.exceptions.LocationParseError, requests.exceptions.RequestException, FileNotFoundError) as ex:
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
		print("Stresser v10.4 ( github.com/ivan-sincek/forbidden )")
		print("")
		print("Usage:   stresser -u url                        -dir directory -r repeat -th threads [-f force] [-o out         ]")
		print("Example: stresser -u https://example.com/secret -dir results   -r 1000   -th 200     [-f GET  ] [-o results.json]")
		print("")
		print("DESCRIPTION")
		print("    Bypass 4xx HTTP response status codes with stress testing")
		print("URL")
		print("    Inaccessible URL")
		print("    -u, --url = https://example.com/secret | etc.")
		print("IGNORE QUERY STRING AND FRAGMENT")
		print("    Ignore URL query string and fragment")
		print("    -iqsf, --ignore-query-string-and-fragment")
		print("IGNORE CURL")
		print("    Ignore PycURL, use Python Requests instead")
		print("    -ic, --ignore-curl")
		print("FORCE")
		print("    Force an HTTP method for all non-specific test cases")
		print("    -f, --force = GET | POST | CUSTOM | etc.")
		print("IGNORE")
		print("    Filter out 200 OK false positive results with RegEx")
		print("    Spacing will be stripped")
		print("    -i, --ignore = Inaccessible | \"Access Denied\" | etc.")
		print("CONTENT LENGTHS")
		print("    Filter out 200 OK false positive results by HTTP response content lengths")
		print("    Specify 'base' to ignore content length of the base HTTP response")
		print("    Use comma-separated values")
		print("    -l, --content-lengths = 12 | base | etc.")
		print("REPEAT")
		print("    Number of total HTTP requests to send for each test case")
		print("    -r, --repeat = 1000 | etc.")
		print("THREADS")
		print("    Number of parallel threads to run")
		print("    -th, --threads = 20 | etc.")
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
		print("DIRECTORY")
		print("    Output directory")
		print("    All valid and unique HTTP responses will be saved in this directory")
		print("    -dir, --directory = results | etc.")
		print("DEBUG")
		print("    Debug output")
		print("    -dbg, --debug")

	def error(self, message):
		if len(sys.argv) > 1:
			print("Missing a mandatory option (-u, -dir, -r, -th) and/or optional (-iqsf, -ic, -f, -i, -l, -a, -x, -o, -dbg)")
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
		self.__parser.add_argument("-f"   , "--force"                           , required = False, type   = str.upper   , default = ""   )
		self.__parser.add_argument("-i"   , "--ignore"                          , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-l"   , "--content-lengths"                 , required = False, type   = str.lower   , default = ""   )
		self.__parser.add_argument("-r"   , "--repeat"                          , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-th"  , "--threads"                         , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-a"   , "--user-agent"                      , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-x"   , "--proxy"                           , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-o"   , "--out"                             , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-dir" , "--directory"                       , required = False, type   = str         , default = ""   )
		self.__parser.add_argument("-dbg" , "--debug"                           , required = False, action = "store_true", default = False)

	def run(self):
		self.__args                 = self.__parser.parse_args()
		self.__args.url             = self.__parse_url(self.__args.url, "url")                  # required
		self.__args.ignore          = self.__parse_ignore(self.__args.ignore)                   if self.__args.ignore          else ""
		self.__args.content_lengths = self.__parse_content_lengths(self.__args.content_lengths) if self.__args.content_lengths else []
		self.__args.repeat          = self.__parse_repeat(self.__args.repeat)                   # required
		self.__args.threads         = self.__parse_threads(self.__args.threads)                 # required
		self.__args.user_agent      = self.__parse_user_agent(self.__args.user_agent)           if self.__args.user_agent      else [default_user_agent]
		self.__args.proxy           = self.__parse_url(self.__args.proxy, "proxy")              if self.__args.proxy           else ""
		self.__args.directory       = self.__parse_directory(self.__args.directory)             # required
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
			elif entry in ["base"]:
				tmp.append(entry)
			elif not entry.isdigit() or int(entry) < 0:
				self.__error("Content lengths must be either 'base' or numeric equal or greater than zero")
				break
			else:
				tmp.append(int(entry))
		return unique(tmp)

	def __parse_repeat(self, value):
		if not value.isdigit():
			self.__error("Number of total HTTP requests to send must be numeric")
		else:
			value = int(value)
			if value <= 0:
				self.__error("Number of total HTTP requests to send must be greater than zero")
		return value

	def __parse_threads(self, value):
		if not value.isdigit():
			self.__error("Number of parallel threads to run must be numeric")
		else:
			value = int(value)
			if value <= 0:
				self.__error("Number of parallel threads to run must be greater than zero")
		return value

	def __parse_user_agent(self, value):
		lower = value.lower()
		if lower == "random-all":
			return get_all_user_agents()
		elif lower == "random":
			return [get_random_user_agent()]
		else:
			return [value]

	def __parse_directory(self, value):
		if not os.path.isdir(value):
			self.__error("Output directory does not exists or is not a directory")
		return value

# ----------------------------------------

def main():
	validate = Validate()
	if validate.run():
		print("##########################################################################")
		print("#                                                                        #")
		print("#                             Stresser v10.4                             #")
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
			validate.get_arg("ignore_query_string_and_fragment"),
			validate.get_arg("ignore_curl"),
			validate.get_arg("force"),
			validate.get_arg("ignore"),
			validate.get_arg("content_lengths"),
			validate.get_arg("repeat"),
			validate.get_arg("threads"),
			validate.get_arg("user_agent"),
			validate.get_arg("proxy"),
			validate.get_arg("directory"),
			validate.get_arg("debug")
		)
		stresser.run()
		results = stresser.get_results()
		if results and out:
			write_file(jdump(results), out)
		stopwatch.stop()

if __name__ == "__main__":
	main()
