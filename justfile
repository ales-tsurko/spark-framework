# watch for changes in the spark-ml parser and print the parser tree for the test input
watch_parser input:
    cargo build --release --bin tree
    watchexec --no-vcs-ignore -w spark-ml/src/grammar/spark-ml.pest -w {{input}} -c "cargo rustc -q -p spark-ml -- -A warnings && ./target/release/tree {{input}}"
