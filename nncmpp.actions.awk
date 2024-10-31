# nncmpp.actions.awk: produce C code for a list of user actions
#
# Copyright (c) 2022 - 2024, Přemysl Eric Janouch <p@janouch.name>
# SPDX-License-Identifier: 0BSD
#
# Usage: env LC_ALL=C A=0 B=1 awk -f nncmpp.actions.awk \
#  nncmpp.actions > nncmpp-actions.h

# --- Preprocessor -------------------------------------------------------------

function fatal(message) {
	print "// " FILENAME ":" FNR ": fatal error: " message
	print FILENAME ":" FNR ": fatal error: " message > "/dev/stderr"
	exit 1
}

function condition(pass,    passing, a, i) {
	split(substr($0, RSTART + RLENGTH), a, /[[:space:]]+/)
	if (!(1 in a))
		fatal("missing condition")

	passing = 0
	for (i in a)
		if (a[i] && !pass == !ENVIRON[a[i]])
			passing = 1

	while (getline > 0) {
		if (match($0, /^[[:space:]]*[.]endif[[:space:]]*$/))
			return 1

		if (match($0, /^[[:space:]]*[.]else[[:space:]]*$/))
			passing = !passing
		else if (!directive() && passing)
			process()
	}

	fatal("unterminated condition body")
}

# Multiple arguments mean logical OR, multiple directives mean logical AND.
# Similar syntax is also used by Exim, BSD make, or various assemblers.
#
# Looking at what others have picked for their preprocessor syntax:
# {OpenGL, FreeBASIC} reuse #ifdef, which would be confusing with C code around,
# {Mental Ray, RapidQ and UniVerse BASIC} use $ifdef, NSIS has !ifdef,
# and Verilog went for `ifdef.  Not much more can be easily found.
function directive() {
	sub(/#.*/, "")
	if (match($0, /^[[:space:]]*[.]ifdef[[:space:]]+/))
		return condition(1)
	if (match($0, /^[[:space:]]*[.]ifndef[[:space:]]+/))
		return condition(0)
	if (/^[[:space:]]*[.]/)
		fatal("unexpected or unsupported directive")
	return 0
}

!directive() {
	process()
}

# --- Postprocessor ------------------------------------------------------------

function strip(string) {
	gsub(/^[[:space:]]*|[[:space:]]*$/, "", string)
	return string
}

function process(    constant, name, description) {
	if (match($0, /,/)) {
		constant = name = strip(substr($0, 1, RSTART - 1))
		description = strip(substr($0, RSTART + RLENGTH))
		gsub(/_/, "-", name)

		N++
		Constants[N] = constant
		Names[N] = tolower(name)
		Descriptions[N] = description
	} else if (/[^[:space:]]/) {
		fatal("invalid action definition syntax")
	}
}

function tocstring(string) {
	gsub(/\\/, "\\\\", string)
	gsub(/"/, "\\\"", string)
	return "\"" string "\""
}

END {
	print "enum action {"
	for (i in Constants)
		print "\t" "ACTION_" Constants[i] ","
	print "\t" "ACTION_USER_0"
	print "};"
	print ""
	print "static const char *g_action_names[] = {"
	for (i in Names)
		print "\t" tocstring(Names[i]) ","
	print "};"
	print ""
	print "static const char *g_action_descriptions[] = {"
	for (i in Descriptions)
		print "\t" tocstring(Descriptions[i]) ","
	print "};"
}
