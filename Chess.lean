import Chess.Kernel
import Chess.Invariant

/-!
# Verified executable chess kernel

This root module exposes the complete Lean development.  The individual
modules separate the finite state model, rule semantics, history and draw
policies, notation, mate certificates, symmetry, executable regressions, and
structural reachability invariants; `Chess.kernel_correct` records the public
correctness bundle.
-/
