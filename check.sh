#!/bin/bash

# Download and install the TLA+ Tools wrapper scripts from
# https://github.com/pmer/tla-bin.git

set -e
shopt -s expand_aliases

SPEC=$1
shift

# Insert ProcessEnabled() for each label, if found in $SPEC.tla
grep -q -e "--algorithm" $SPEC.tla && pcal -nocfg $SPEC.tla | tee $SPEC.log
if grep -q -e "^\s*ProcessEnabled(self)\s*==" $SPEC.tla; then
	sed -i -e 's%pc\[self\] = ".*"$%& /\\\ ProcessEnabled(self)%' $SPEC.tla
fi

# Split vars into {global,local}_vars tuples
gawk -i inplace -f varsplit.awk $SPEC.tla

tlc -workers $(nproc) $@ $SPEC.tla | tee -a $SPEC.log
