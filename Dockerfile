FROM docker.io/rust:1.56.0-slim


WORKDIR /home

RUN cargo generate-lockfile


