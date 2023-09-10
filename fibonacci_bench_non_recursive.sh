#!/bin/sh
RUSTFLAGS='-C target-cpu=native' cargo +nightly test --release -- --ignored --nocapture test_fibonacci_case1