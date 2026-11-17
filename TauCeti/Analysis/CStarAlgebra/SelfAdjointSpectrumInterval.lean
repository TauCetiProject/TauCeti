/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Tactic.Linarith

/-!
# Spectral intervals of self-adjoint elements

Let `a` be a self-adjoint element of a real normed star algebra with an isometric continuous
functional calculus for self-adjoint elements, for instance a C⋆-algebra or `X →L[ℝ] X`. Every
point of the real spectrum of `a` has absolute value at most `‖a‖`
(`IsometricContinuousFunctionalCalculus.norm_spectrum_le`). When the algebra is nontrivial, `‖a‖`
is attained as the largest such absolute value
(`IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum`); in a trivial algebra the
spectrum is empty and `‖a‖ = 0`. In either case, for `0 ≤ r`, `‖a‖ ≤ r` exactly when the real
spectrum of `a` lies in the interval `[-r, r]`; this turns spectral localisation into norm bounds
and back.

Centering an arbitrary interval `[m, M]` at `c = (m + M) / 2` with radius `r = (M - m) / 2` turns
asymmetric real-spectrum inclusions `spectrum ℝ a ⊆ [m, M]` into norm bounds
`‖a - algebraMap ℝ A c‖ ≤ r`, so spectral interval bounds add across binary and finite sums of
self-adjoint elements without requiring a complex C⋆-algebra structure or an ambient `PartialOrder`.

If instead the spectrum has a gap around zero of radius `r > 0`, then `a` is invertible and its
canonical ring inverse has norm at most `r⁻¹`; this is
`IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le` in
`TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.GapInverse`, which applies to `a`
and its real spectrum directly.

## Main results

* `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: for `0 ≤ r`, `‖a‖ ≤ r` if and only if
  `spectrum ℝ a ⊆ Set.Icc (-r) r`.
* `IsSelfAdjoint.norm_sub_algebraMap_le_iff_spectrum_subset_Icc`: for `0 ≤ r`,
  `‖a - algebraMap ℝ A c‖ ≤ r` if and only if `spectrum ℝ a ⊆ Set.Icc (c - r) (c + r)`.
* `IsSelfAdjoint.spectrum_add_subset_Icc`: real-spectrum interval bounds add for two self-adjoint
  elements under an isometric continuous functional calculus.
* `TauCeti.spectrum_sum_subset_Icc`: real-spectrum interval bounds add across any finite sum of
  self-adjoint elements under an isometric continuous functional calculus.
-/

public section

namespace IsSelfAdjoint

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A} {r : ℝ}

/-- The norm of a self-adjoint element is at most `r ≥ 0` exactly when its real spectrum lies
in the interval `[-r, r]`. -/
theorem norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  simpa [Set.subset_def, abs_le, cfc_id' ℝ a] using norm_cfc_le_iff (id : ℝ → ℝ) a hr

/-- The distance of a self-adjoint element from a real scalar `c` is at most `r ≥ 0` exactly when
its real spectrum lies in `[c - r, c + r]`. -/
theorem norm_sub_algebraMap_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (c : ℝ)
    (hr : 0 ≤ r) : ‖a - algebraMap ℝ A c‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (c - r) (c + r) := by
  have hcfc : cfc (fun x : ℝ => x - c) a = a - algebraMap ℝ A c := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ => c) a, cfc_id' ℝ a, cfc_const c a]
  rw [← hcfc, norm_cfc_le_iff _ a hr]
  exact forall₂_congr fun _ _ => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> intro ⟨_, _⟩ <;> constructor <;> linarith

/-- If two self-adjoint elements have real spectra in `[m₁, M₁]` and `[m₂, M₂]`, then the real
spectrum of their sum lies in `[m₁ + m₂, M₁ + M₂]`. -/
theorem spectrum_add_subset_Icc {b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    {m₁ M₁ m₂ M₂ : ℝ} (haI : spectrum ℝ a ⊆ Set.Icc m₁ M₁) (hbI : spectrum ℝ b ⊆ Set.Icc m₂ M₂) :
    spectrum ℝ (a + b) ⊆ Set.Icc (m₁ + m₂) (M₁ + M₂) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · simp
  obtain ⟨x₁, hx₁⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) a ha
  obtain ⟨x₂, hx₂⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) b hb
  set c₁ := (m₁ + M₁) / 2 with hc₁; set r₁ := (M₁ - m₁) / 2 with hr₁_def
  set c₂ := (m₂ + M₂) / 2 with hc₂; set r₂ := (M₂ - m₂) / 2 with hr₂_def
  have hr₁ : 0 ≤ r₁ := by linarith [(haI hx₁).1, (haI hx₁).2]
  have hr₂ : 0 ≤ r₂ := by linarith [(hbI hx₂).1, (hbI hx₂).2]
  have hI₁ : Set.Icc (c₁ - r₁) (c₁ + r₁) = Set.Icc m₁ M₁ := by congr 1 <;> linarith
  have hI₂ : Set.Icc (c₂ - r₂) (c₂ + r₂) = Set.Icc m₂ M₂ := by congr 1 <;> linarith
  have h₁ : ‖a - algebraMap ℝ A c₁‖ ≤ r₁ :=
    (ha.norm_sub_algebraMap_le_iff_spectrum_subset_Icc c₁ hr₁).mpr (hI₁.symm ▸ haI)
  have h₂ : ‖b - algebraMap ℝ A c₂‖ ≤ r₂ :=
    (hb.norm_sub_algebraMap_le_iff_spectrum_subset_Icc c₂ hr₂).mpr (hI₂.symm ▸ hbI)
  have hsub : (a + b) - algebraMap ℝ A (c₁ + c₂) =
      (a - algebraMap ℝ A c₁) + (b - algebraMap ℝ A c₂) := by rw [map_add]; abel
  have hI₁₂ : Set.Icc (c₁ + c₂ - (r₁ + r₂)) (c₁ + c₂ + (r₁ + r₂)) =
      Set.Icc (m₁ + m₂) (M₁ + M₂) := by congr 1 <;> linarith
  exact hI₁₂ ▸ ((ha.add hb).norm_sub_algebraMap_le_iff_spectrum_subset_Icc (c₁ + c₂)
    (add_nonneg hr₁ hr₂)).mp (hsub ▸ (norm_add_le _ _).trans (add_le_add h₁ h₂))

end IsSelfAdjoint

namespace TauCeti

open Finset

/-- If self-adjoint elements `a i` (`i ∈ s`) have real spectra in `[m i, M i]`, then
`spectrum ℝ (∑ i ∈ s, a i) ⊆ [∑ i ∈ s, m i, ∑ i ∈ s, M i]` (including `s = ∅`). -/
theorem spectrum_sum_subset_Icc {A ι : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] (s : Finset ι) {a : ι → A}
    {m M : ι → ℝ} (ha : ∀ i ∈ s, IsSelfAdjoint (a i))
    (hI : ∀ i ∈ s, spectrum ℝ (a i) ⊆ Set.Icc (m i) (M i)) :
    spectrum ℝ (∑ i ∈ s, a i) ⊆ Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rcases subsingleton_or_nontrivial A with _ | _ <;> simp
  | @insert i s hi ih =>
      rw [sum_insert hi, sum_insert hi, sum_insert hi]
      exact (ha i (mem_insert_self i s)).spectrum_add_subset_Icc
        (isSelfAdjoint_sum s fun j hj => ha j (mem_insert_of_mem hj))
        (hI i (mem_insert_self i s))
        (ih (fun j hj => ha j (mem_insert_of_mem hj)) (fun j hj => hI j (mem_insert_of_mem hj)))

end TauCeti
