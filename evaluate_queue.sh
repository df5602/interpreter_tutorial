#!/bin/bash
cargo build
cd out/queue/
for i in *; do
	echo "------------------------------------------------------------------"
	echo file: $i
	echo
	cat -v $i
	echo "------------------------------------------------------------------"
	hexdump -C $i
	echo "------------------------------------------------------------------"
	../../target/debug/interpreter_tutorial $i
	echo "------------------------------------------------------------------"
	read IN
	if [ "$IN" = "bug" ]; then
		cp $i ../../tmp/bugs/$i
		echo copied to tmp/bugs/$i
	else
		mv $i ok/$i
	fi
done
cd ../../
