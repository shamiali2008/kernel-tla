#!/bin/bash

set -e
shopt -s expand_aliases

export CLASSPATH=~/tla
# Uncomment if TLC causes an exception in javax.activation.DataSource
#export _JAVA_OPTIONS="--add-modules=java.activation"

alias tlc="java tlc2.TLC"
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

# Generate{global,local}_vars
gawk -i inplace -f varsplit.awk $SPEC.tla

tlc -workers $(nproc) $@ $SPEC.tla | tee -a $SPEC.log
