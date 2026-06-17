import Mathlib.Tactic

namespace TauCeti

/-- Fix-ci fixture: the proof below is deliberately broken (references a non-existent lemma) so the
`build` check is red. The worker's fix-ci round should repair it to a correct proof and push green.
Safe to delete. -/
theorem fixci_probe (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

end TauCeti
