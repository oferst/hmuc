#!/bin/sh
export MROOT=~/hmuc
echo $MROOT
cd simp
gmake clean
gmake  rs
cp minisat_static ../hmuc