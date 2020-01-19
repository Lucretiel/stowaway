#!/bin/sh

set -ex

cargo fmt -- --check
cargo clippy -- -Dwarnings
cargo test
