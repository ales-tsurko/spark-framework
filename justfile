# watch for changes in the spark-ml parser and print the parser tree for the test input
watch_parser input:
    cargo build --release --bin tree
    watchexec --no-vcs-ignore -w "spark-ml/src/grammar/spark-ml.pest" -w {{input}} ./target/release/tree {{input}}
