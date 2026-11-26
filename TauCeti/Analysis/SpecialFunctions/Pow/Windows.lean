/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Windows of scales

A set has windows of exponent `L` if it contains `[Y, Y ^ L]` for arbitrarily large `Y ≥ 1`.
Under the exponential map these become the intervals `[U, L * U]` with `U ≥ 0`, the
coordinates used to localize Laplace integrals.

The scale-window predicate is from Levent Alpöge's Dirichlet L-function formalization,
`Formalism.HC.HasWindows` in `TotientGaloisClasses/Window.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Filter Set

namespace TauCeti

/-- The set `S` contains the windows `[Y, Y ^ L]` at arbitrarily large scales `Y ≥ 1`.
In applications `1 < L`, so the windows grow with `Y`. -/
def HasWindows (S : Set ℝ) (L : ℝ) : Prop :=
  ∃ᶠ Y in atTop, 1 ≤ Y ∧ Icc Y (Y ^ L) ⊆ S

/-- A window can be chosen beyond any prescribed lower bound on its starting point. -/
theorem hasWindows_iff {S : Set ℝ} {L : ℝ} :
    HasWindows S L ↔ ∀ Y₀, ∃ Y, max Y₀ 1 ≤ Y ∧ Icc Y (Y ^ L) ⊆ S := by
  simp only [HasWindows, frequently_atTop, max_le_iff, and_assoc]

/-- Enlarging a set above a fixed cutoff preserves its windows. -/
theorem HasWindows.mono_of_inter_subset {S T : Set ℝ} {L x₀ : ℝ} (h : HasWindows S L)
    (hst : S ∩ Ici x₀ ⊆ T) : HasWindows T L := by
  rw [HasWindows] at h ⊢
  refine (h.and_eventually (eventually_ge_atTop x₀)).mono ?_
  rintro Y ⟨⟨hY₁, hY⟩, hx₀⟩
  exact ⟨hY₁, fun _ hx ↦ hst ⟨hY hx, hx₀.trans hx.1⟩⟩

/-- A superset of a set with windows has the same windows. -/
theorem HasWindows.mono {S T : Set ℝ} {L : ℝ} (h : HasWindows S L) (hst : S ⊆ T) :
    HasWindows T L :=
  h.mono_of_inter_subset (inter_subset_left.trans hst : S ∩ Ici 1 ⊆ T)

/-- Decreasing the exponent preserves the window property. -/
theorem HasWindows.of_le {S : Set ℝ} {L L' : ℝ} (h : HasWindows S L) (hle : L' ≤ L) :
    HasWindows S L' := by
  rw [HasWindows] at h ⊢
  exact h.mono fun _ ⟨hY, hYS⟩ ↦
    ⟨hY, (Icc_subset_Icc_right (Real.rpow_le_rpow_of_exponent_le hY hle)).trans hYS⟩

/-- Every upper ray contains windows. -/
@[simp]
theorem hasWindows_Ici (x₀ L : ℝ) : HasWindows (Ici x₀) L := by
  exact (((eventually_ge_atTop (1 : ℝ)).and (eventually_ge_atTop x₀)).mono
    fun _ ⟨hY, hx₀⟩ ↦ ⟨hY, fun _ hx ↦ hx₀.trans hx.1⟩).frequently

/-- Exponentiation takes the logarithmic windows `[U, L * U]` to `[Y, Y ^ L]`. -/
theorem hasWindows_iff_frequently_exp {S : Set ℝ} {L : ℝ} :
    HasWindows S L ↔ ∃ᶠ U in atTop, 0 ≤ U ∧ Icc U (L * U) ⊆ Real.exp ⁻¹' S := by
  rw [HasWindows]
  nth_rw 1 [← Real.map_exp_atTop]
  rw [frequently_map]
  refine frequently_congr (Eventually.of_forall fun U ↦ ?_)
  rw [← image_subset_iff, Real.image_exp_Icc, mul_comm L U, Real.exp_mul,
    Real.one_le_exp_iff]

end TauCeti
