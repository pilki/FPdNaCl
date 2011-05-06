#!/bin/bash
for file in *.tst
do
  echo "Check file $file"
  if !(../../assembly/asm < $file | ../../validator)
  then
      echo "#############################################"
      echo "ECHEC"
      echo "#############################################"
      exit 1
  fi
done
echo "#############################################"
echo "All the test passed"
echo "#############################################"
exit 0
