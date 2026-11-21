# syntax=docker/dockerfile:1
# Build has network; the run has none. Scorers are linux/amd64 GCP n2 (Cascade Lake or newer).
# No platform pinned: `make build PLATFORM=linux/arm64` gives a native image on Apple silicon.
FROM rust:1.91-slim-bookworm AS build
ARG TARGETARCH
WORKDIR /src
# Tune the amd64 binary for the scorer independently of the build host.
RUN if [ "$TARGETARCH" = "arm64" ]; then echo "" > /rustflags; else echo "-C target-cpu=cascadelake" > /rustflags; fi
COPY Cargo.toml Cargo.lock ./
COPY src ./src
RUN RUSTFLAGS="$(cat /rustflags)" cargo build --release --locked

# distroless/cc: glibc and libgcc only, so the container starts fast.
FROM gcr.io/distroless/cc-debian12:nonroot
COPY --from=build /src/target/release/sessions /sessions
USER 1000:1000
ENTRYPOINT ["/sessions"]
