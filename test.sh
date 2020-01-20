#!/bin/sh

set -ex

cargo clean
cargo fmt -- --check
cargo clippy -- -Dwarnings
cargo test
cargo miri test
