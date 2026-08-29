# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.

FROM mcr.microsoft.com/devcontainers/base:resolute

# md4c is the differential-testing oracle for the LaTeX math extension, and is built from
# source at a pinned tag rather than installed. The base image already provides gcc and make;
# cmake is md4c's build system and is the only piece missing.
RUN apt-get update \
 && apt-get install -y --no-install-recommends cmake \
 && rm -rf /var/lib/apt/lists/*

USER vscode
ENV PATH="/home/vscode/.local/bin:/home/vscode/.elan/bin:${PATH}"
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
RUN elan toolchain install stable
RUN curl -fsSL https://claude.ai/install.sh | bash
RUN curl -LsSf https://astral.sh/uv/install.sh | sh
