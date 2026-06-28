module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Iterated shifts on one-sided path space

This file records the Layer 2 path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`: the coordinate formula `shift_iterate_apply` and the corresponding
measurability, path-law, and finite-prefix normal forms.

These declarations advance the `TauCetiRoadmap/Exchangeability/README.md` Layer 2
path-space dynamics target `shift_iterate_measurable`.
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

/-- The `r`-fold one-sided shift is measurable. -/
theorem measurable_shift_iterate (r : ℕ) : Measurable ((shift α)^[r]) :=
  measurable_shift.iterate r

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Iterated shift composed with a prefix projection selects a consecutive finite block. -/
@[simp]
theorem prefixProj_shift_iterate_apply (r n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n ((shift α)^[r] x) i = x (i.val + r) := by
  simp [prefixProj]

/-- Mapping a path law by the `r`-fold shift gives the path law of the shifted process. -/
theorem map_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r : ℕ) :
    (pathLaw μ X).map ((shift α)^[r]) =
      pathLaw μ (fun k ω => X (k + r) ω) := by
  rw [pathLaw_apply, pathLaw_apply,
    AEMeasurable.map_map_of_aemeasurable (measurable_shift_iterate r).aemeasurable
      (aemeasurable_pi_lambda _ hX)]
  congr 1
  funext ω k
  simp

/-- Mapping a path law by the `r`-fold shift and then taking the first `n` coordinates gives the
law of the consecutive block starting at `r`. -/
theorem map_prefixProj_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r n : ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => prefixProj α n ((shift α)^[r] x)) =
      blockLaw μ X (fun i : Fin n => i.val + r) := by
  rw [pathLaw_apply, blockLaw_apply]
  have hprefix :
      AEMeasurable (fun x : ℕ → α => prefixProj α n ((shift α)^[r] x))
        (Measure.map (fun ω => fun i => X i ω) μ) :=
    ((measurable_prefixProj n).comp (measurable_shift_iterate r)).aemeasurable
  rw [AEMeasurable.map_map_of_aemeasurable hprefix (aemeasurable_pi_lambda _ hX)]
  congr 1
  funext ω i
  simp

end Probability

end TauCeti
