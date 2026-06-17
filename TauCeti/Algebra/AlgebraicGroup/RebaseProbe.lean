import Mathlib.Tactic

namespace TauCeti

/-- Rebase fixture: a trivial probe so this PR adds an import line into the `TauCeti.lean`
aggregator's `Algebra.AlgebraicGroup` block, colliding with an import main added there
(`RootsOfUnity`). This exercises the worker's rebase (import-union) workflow. Safe to delete. -/
theorem rebase_probe : True := trivial

end TauCeti
