module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Iterated shifts on one-sided path space

This file records the Layer 2 path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`: the coordinate formula `shift_iterate_apply` and block formulas
after iterated shifts, together with the named measurability theorem for iterated shifts.

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
theorem shift_iterate_measurable (r : ℕ) : Measurable ((shift α)^[r]) :=
  measurable_shift.iterate r

/-- Pushing the path law forward by the `r`-fold shift is the path law of the time-shifted
process. -/
theorem map_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r : ℕ) :
    (pathLaw μ X).map ((shift α)^[r]) = pathLaw μ (fun n ω => X (n + r) ω) := by
  rw [pathLaw_apply, pathLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable (shift_iterate_measurable r).aemeasurable
    (aemeasurable_pi_lambda _ hX)]
  congr 1
  funext ω n
  simp

/-- Projecting the `r`-fold shifted path law onto its first `n` coordinates gives the block law
of the consecutive block starting at `r`. -/
theorem map_prefixProj_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r n : ℕ) :
    ((pathLaw μ X).map ((shift α)^[r])).map (prefixProj α n) =
      blockLaw μ X (fun i : Fin n => i.val + r) := by
  rw [map_shift_iterate_pathLaw μ hX r,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ fun i => hX (i + r)) n]
  rfl

end Probability

end TauCeti
