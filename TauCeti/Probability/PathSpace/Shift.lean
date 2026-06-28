module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Iterated shifts on one-sided path space

This file records the Layer 2 path-space API for iterating the one-sided shift
`TauCeti.Probability.shift`: the coordinate formula `shift_iterate_apply`, block formulas
after iterated shifts, and the corresponding pushforward identity for process path laws.

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

/-- The map selecting a finite consecutive block starting at `r` is measurable. -/
theorem measurable_prefixProj_shift_iterate (r n : ℕ) :
    Measurable fun x : ℕ → α => prefixProj α n ((shift α)^[r] x) :=
  (measurable_prefixProj n).comp (measurable_shift_iterate r)

private theorem map_reindex_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k)) =
      pathLaw μ (fun k ω => X (φ k) ω) := by
  have hφ_meas : Measurable (fun x : ℕ → α => fun k => x (φ k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (φ k)
  rw [pathLaw_apply, pathLaw_apply,
    AEMeasurable.map_map_of_aemeasurable hφ_meas.aemeasurable
      (aemeasurable_pi_lambda _ hX)]
  rfl

private theorem map_reindex_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) (n : ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => prefixProj α n (fun k => x (φ k))) =
      blockLaw μ X (fun i : Fin n => φ i.val) := by
  rw [pathLaw_apply, blockLaw_apply]
  change Measure.map ((prefixProj α n) ∘ (fun x : ℕ → α => fun k => x (φ k)))
      (Measure.map (fun ω => fun i => X i ω) μ) =
    Measure.map (fun ω i => X (φ i.val) ω) μ
  rw [AEMeasurable.map_map_of_aemeasurable
    ((measurable_prefixProj n).comp
      (measurable_pi_lambda _ fun k => measurable_pi_apply (φ k))).aemeasurable
    (aemeasurable_pi_lambda _ hX)]
  rfl

/-- Mapping a path law by the `r`-fold shift gives the path law of the time-shifted process. -/
theorem map_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r : ℕ) :
    (pathLaw μ X).map ((shift α)^[r]) = pathLaw μ (fun n ω => X (n + r) ω) := by
  have hshift : ((shift α)^[r]) = fun x : ℕ → α => fun n => x (n + r) := by
    funext x n
    simp
  rw [hshift]
  exact map_reindex_pathLaw μ hX (fun n => n + r)

/-- The prefix projection after `r` shifts gives the finite block beginning at time `r`. -/
theorem map_prefixProj_shift_iterate_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (r n : ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => prefixProj α n ((shift α)^[r] x)) =
      blockLaw μ X (fun i : Fin n => i.val + r) := by
  have hshift :
      (fun x : ℕ → α => prefixProj α n ((shift α)^[r] x)) =
        fun x : ℕ → α => prefixProj α n (fun k => x (k + r)) := by
    funext x i
    simp
  rw [hshift]
  exact map_reindex_prefixProj_pathLaw μ hX (fun k => k + r) n

end Probability

end TauCeti
