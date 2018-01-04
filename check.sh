#!/bin/bash

set -e
shopt -s expand_aliases

export CLASSPATH=~/tla

alias tlc="java tlc2.TLC"
alias tla2sany="java tla2sany.SANY"
alias pcal="java pcal.trans"
alias tla2tex="java tla2tex.TLA"

SPEC=$1
shift

pcal $SPEC | tee $SPEC.log
tlc -workers $(nproc) -cleanup $@ $SPEC | tee -a $SPEC.log
