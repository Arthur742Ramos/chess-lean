# Contributing

This repository is a standalone Lean 4 development. Keep the executable and
logical layers explicit, preserve the source-to-module provenance in
`formalization.yaml`, and keep `Challenge.lean` limited to the advertised
statement surface.

## Local workflow

The checked-in `lean-toolchain`, `lakefile.toml`, and both Lake manifests are
the reproducibility boundary. After changing dependencies, regenerate and
review both manifests. Build the project with:

```text
lake exe cache get
lake build
(cd docbuild && lake build Chess:docs)
```

Run the metadata, wrapper, and Comparator checks before opening a change:

```text
ruby test/validate_formalization_test.rb
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
./scripts/verify-comparator.sh
```

The Comparator script checks out exact tool revisions, enables the NanoDa
replay, and runs both NanoDa and the default Lean kernel. Its cache and all
`.lake/` output are local build products and must not be committed.

## Architecture

The `Chess/` modules contain the chess semantics and executable regressions.
`Challenge.lean` imports only the public statement dependencies and keeps its
advertised theorem as a declaration with `sorry`; `Solution.lean` imports the
completed library and proves the matching declaration. Keep this split intact
so the registry comparison remains independently auditable.

## Attribution and submission

Changes that alter the modeled rule scope, source alignment, authorship, or
review status must update `README.md` and `formalization.yaml` together. The
authors of this repository are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. Palomar intake is a
separate action: record the exact public repository, immutable commit,
Comparator configuration, author relationship, and review evidence before
using the submission form.
