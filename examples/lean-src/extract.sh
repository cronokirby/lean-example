#!/bin/sh
# Regenerates Examples/Gen from the examples crate. Needs charon and aeneas on
# PATH, from the aeneas release matching the rev in lakefile.toml (its tarball
# ships the pinned charon).
set -eu
cd "$(dirname "$0")"
llbc=../../target/llbc/examples.llbc
(cd .. && charon cargo --preset=aeneas --dest-file "../target/llbc/examples.llbc")
rm -rf Examples/Gen
aeneas -backend lean -split-files -loops-to-rec -dest . -subdir Examples/Gen "$llbc"
