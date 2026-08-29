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

The `Chess/` modules contain the full orthodox-rule semantics and executable
regressions. `Challenge.lean` is a self-contained copy of the complete
production rule kernel needed for the advertised generalized-record theorem:
its position state has castling and en-passant state, and its move type has
promotions, en-passant captures, and all four castling moves. The theorem is
deliberately universal over the represented `Position` records, including
potentially malformed or unreachable records; it does not assume
`positionInvariant` or reachability. It keeps `Chess.legalMoves_correct` as
the deliberate Challenge proof hole.
`Solution.lean` repeats that same full rule-kernel surface and supplies the
production proof. Keeping both files source-equivalent apart from that proof
lets the registry comparison remain independently auditable without relying
on local compiled modules.

## Attribution and submission

Changes that alter the modeled rule scope, source alignment, authorship, or
review status must update `README.md` and `formalization.yaml` together. The
authors of this repository are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. Palomar intake is a
separate action: record the exact public repository, immutable commit,
Comparator configuration, author relationship, and review evidence before
using the submission form. The adapted Isabelle source is pinned at revision
`a81eecf7b7a77064380bdf1f8915d73ee9955fa3`, path
`projects/chess-isabelle`, and the complete source snapshot is included at
`artifacts/isabelle/chess-isabelle` for public inspection.
