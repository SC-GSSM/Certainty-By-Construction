# Certainty By Construction
Working through the text

## Agda setup

This project uses a local Agda configuration in `.agda/` and a local checkout of
the Agda standard library in `deps/agda-stdlib/`.

The included standard library checkout is pinned to `v2.3`, which supports Agda
`2.7.0.1`.

To type check a chapter with the project-local library config:

```sh
./scripts/agda Chapter7-Structures.agda
```

To recreate the local dependency checkout:

```sh
mkdir -p deps
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git deps/agda-stdlib
```
