module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Iterated shifts on one-sided path space

This file records the Layer 2 path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`.  The main declarations are the coordinate formula
`shift_iterate_apply`, measurability of all iterates, and the corresponding pushforward
identity for process path laws.

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
/-- Applying `r + s` shifts is the same as applying `s` shifts and then `r` more. -/
theorem shift_iterate_add_apply (r s : ℕ) (x : ℕ → α) :
    (shift α)^[r + s] x = (shift α)^[r] ((shift α)^[s] x) := by
  ext n
  simp [Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Iterated shift composed with a prefix projection selects a consecutive finite block. -/
@[simp]
theorem prefixProj_shift_iterate_apply (r n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n ((shift α)^[r] x) i = x (i.val + r) := by
  simp [prefixProj]

/-- Every iterate of the one-sided path-space shift is measurable. -/
theorem measurable_shift_iterate (r : ℕ) : Measurable ((shift α)^[r]) :=
  measurable_shift.iterate r

/-- A shift-preserving path-space measure is preserved by every iterated shift. -/
theorem MeasurePreserving.shift_iterate {ν : Measure (ℕ → α)}
    (hν : MeasurePreserving (shift α) ν ν) (r : ℕ) :
    MeasurePreserving ((shift α)^[r]) ν ν :=
  hν.iterate r

/-- The coordinate map `x ↦ x (n + r)` is measurable on path space. -/
theorem measurable_shifted_eval (r n : ℕ) : Measurable fun x : ℕ → α => x (n + r) :=
  measurable_pi_apply (n + r)

/-- The map selecting a finite consecutive block starting at `r` is measurable. -/
theorem measurable_prefixProj_shift_iterate (r n : ℕ) :
    Measurable fun x : ℕ → α => prefixProj α n ((shift α)^[r] x) :=
  (measurable_prefixProj n).comp (measurable_shift_iterate r)

/-- Mapping a path law by the `r`-fold shift gives the path law of the time-shifted process. -/
theorem map_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r : ℕ) :
    (pathLaw μ X).map ((shift α)^[r]) = pathLaw μ (fun n ω => X (n + r) ω) := by
  rw [pathLaw_apply, pathLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_shift_iterate r).aemeasurable
    (aemeasurable_pi_lambda _ hX)]
  congr 1
  funext ω n
  simp

/-- The prefix projection after `r` shifts gives the finite block beginning at time `r`. -/
theorem map_prefixProj_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r n : ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => prefixProj α n ((shift α)^[r] x)) =
      blockLaw μ X (fun i : Fin n => i.val + r) := by
  rw [pathLaw_apply, blockLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable
    (measurable_prefixProj_shift_iterate r n).aemeasurable
    (aemeasurable_pi_lambda _ hX)]
  congr 1
  funext ω i
  simp

end Probability

end TauCeti
