#!/bin/sh

echo 'generating epydoc'
epydoc -o docs ctl checker
echo 'cleaning *.pyc files'
rm *.pyc
echo 'cleaning backup files'
rm -r *~
echo 'done, have a nice day'
