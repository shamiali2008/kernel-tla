#!/bin/bash

set -e
shopt -s expand_aliases

export CLASSPATH=~/tla

alias tlc="java --add-modules=java.activation tlc2.TLC"
alias tla2sany="java tla2sany.SANY"
alias pcal="java pcal.trans"
alias tla2tex="java tla2tex.TLA"

SPEC=$1
shift

# Insert ProcessEnabled() for each label, if found in $SPEC.tla
grep -q -e "--algorithm" $SPEC.tla && pcal -nocfg $SPEC.tla | tee $SPEC.log
if grep -q -e "^\s*ProcessEnabled(self)\s*==" $SPEC.tla; then
	sed -i -e 's%pc\[self\] = ".*"$%& /\\\ ProcessEnabled(self)%' $SPEC.tla
fi

# Split << pc, stack >> out of the default vars and generate proc_vars
sed -i -e "/^vars\s*==/,/>>/{s/\<vars\>/proc_vars/;s/\<pc,\s*\|\<stack,\s*//g;s/>>/>>\n\nvars == << proc_vars, pc, stack >>/}" $SPEC.tla

tlc -workers $(nproc) $@ $SPEC.tla | tee -a $SPEC.log
