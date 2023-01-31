# watch for changes in the spark-ml parser and print the parser tree for the test input
watch_parser input:
    watchexec --no-vcs-ignore -w spark-ml/src/grammar/spark-ml.pest -w {{input}} -c "cargo run -q --bin tree -- {{input}}"
