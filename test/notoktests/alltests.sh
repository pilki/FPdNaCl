#!/bin/bash
for file in *.tst
do
  echo "Check file $file"
  if (../../assembly/asm < $file | ../../validator)
  then
      echo "#############################################"
      echo "This test should have failed"
      echo "#############################################"
      exit 1
  fi
done
echo "#############################################"
echo "All the test failed (which is a success!)"
echo "#############################################"
exit 0
