#!/bin/sh
# Run the native binary the way run_fixtures.py expects: native_run.sh DATA_DIR OUTPUT_DIR
exec env DATA_DIR="$1" OUTPUT_DIR="$2" NCPU="${NCPU:-8}" "$(dirname "$0")/../target/release/sessions"
