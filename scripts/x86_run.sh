#!/bin/sh
# The x86-64-v3 build (cargo build --release --target x86_64-apple-darwin), under Rosetta on a Mac.
exec env DATA_DIR="$1" OUTPUT_DIR="$2" NCPU="${NCPU:-8}" "$(dirname "$0")/../target/x86_64-apple-darwin/release/sessions"
