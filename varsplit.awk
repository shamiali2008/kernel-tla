#!/usr/bin/gawk -f

function parse_vars(vars_set)
{
	print

	# read subsequent lines if the current one finishes with a comma
	line = $0
	while (/,[ \t]*/) {
		if ((getline) > 0) {
			print
			line = line $0
		}
	}

	# extract the variable names and build a set
	n = split(line, vars, /[, \t]+/)
	for (i = 2; i <= n; i++)
		vars_set[vars[i]] = ""
}

function print_vars(name, vars_set)
{
	len = length(vars_set)
	i = 1
	printf("%s == << ", name)
	for (v in vars_set) {
		printf("%s", v)
		if (i < len)
			printf(", ")
		i++
	}
	printf(" >>\n")
}

BEGIN {
	mode = ""
}

# Only transform the PlusCal generated code
/^\\\* BEGIN TRANSLATION/ {
	mode = "gvars"
}

# Global variable parsing (first encounter)
mode == "gvars" && /^VARIABLE/ {
	parse_vars(global_vars)

	# delete pc and stack
	delete global_vars["pc"]
	delete global_vars["stack"]

	mode = "lvars"
	next
}

# Local variable parsing (second encounter)
mode == "lvars" && /^VARIABLE/ {
	parse_vars(local_vars)

	mode = "vars"
	next
}

# Replace the "vars" definition
mode == "vars" && /^vars[ \t]*==[ \t]*<</ {
	# find the end angle brackets
	while ($0 !~ />>/) {
		if ((getline) <=0)
			break
	}

	# print the new var definitions
	print_vars("global_vars", global_vars)
	print_vars("local_vars", local_vars)
	print "vars == << global_vars, local_vars, pc, stack >>"

	mode = ""
	next
}

# Default mode, print everything
{
	print
}
