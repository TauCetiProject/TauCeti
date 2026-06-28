module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Iterated shifts on one-sided path space

This file records the Layer 2 path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`: the coordinate formula `shift_iterate_apply`, block formulas
after iterated shifts, and measurability of iterated shifts.

These declarations advance the `TauCetiRoadmap/Exchangeability/README.md` Layer 2
path-space dynamics target `shift_iterate_measurable`; they use the existing Tau Ceti
Layer 0 path-law and shift definitions rather than introducing a parallel shift.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The `r`-fold one-sided shift reads coordinate `n + r`. -/
@[simp]
theorem shift_iterate_apply (r : ℕ) (x : ℕ → α) (n : ℕ) :
    (shift α)^[r] x n = x (n + r) := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply]
      simp [ih, Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Iterated shift composed with a prefix projection selects a consecutive finite block. -/
@[simp]
theorem prefixProj_shift_iterate_apply (r n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n ((shift α)^[r] x) i = x (i.val + r) := by
  simp [prefixProj]

/-- The `r`-fold one-sided shift is measurable. -/
theorem measurable_shift_iterate (r : ℕ) : Measurable ((shift α)^[r]) :=
  measurable_shift.iterate r

end Probability

end TauCeti
