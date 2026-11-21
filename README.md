# dbx-sessions

Shopping Sessions buildathon track, in Rust with no dependencies. `rules.md` is the spec.

    make native-fixtures   # 36 edge-case fixtures, native binary
    make native-dev        # 1M-event dev set vs dev-answer/
    make build fixtures    # same through the scorer's Docker flags (linux/amd64)
    make test              # unit tests

Pipeline: `src/main.rs` (stages in its header). `src/scan.rs` is the SIMD CSV scanner,
`src/key.rs` the order-preserving ID keys, `src/ts.rs` timestamps, `src/parquet.rs` the writer.
`lean/` holds the Lean spec and proofs that the fast paths match it.
