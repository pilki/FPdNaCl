#!/bin/bash
for file in *.tst
do
  echo "Check file $file"
  ../../assembly/asm.native < $file | ../../validator;
done
