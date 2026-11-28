/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Spectral intervals of a self-adjoint element

Let `a` be a self-adjoint element of a real normed star algebra with an isometric continuous
functional calculus for self-adjoint elements, for instance a C⋆-algebra. Every point of the real
spectrum of `a` has absolute value at most `‖a‖`
(`IsometricContinuousFunctionalCalculus.norm_spectrum_le`). When the algebra is nontrivial, `‖a‖`
is attained as the largest such absolute value
(`IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum`); in a trivial algebra the
spectrum is empty and `‖a‖ = 0`. In either case, for `0 ≤ r`, `‖a‖ ≤ r` exactly when the real
spectrum of `a` lies in the interval `[-r, r]`; this turns spectral localisation into norm bounds
and back.

For a self-adjoint element `a` in a normed algebra with summable geometric series and continuous
functional calculus, we also record the spectral inclusion
`spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1` and its strict positivity when `‖a‖ < 1`.

If instead the spectrum has a gap around zero of radius `r > 0`, then `a` is invertible and its
canonical ring inverse has norm at most `r⁻¹`; this is
`IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le` in
`TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.GapInverse`, which applies to `a`
and its real spectrum directly.

## Main results

* `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: for `0 ≤ r`, `‖a‖ ≤ r` if and only if
  `spectrum ℝ a ⊆ Set.Icc (-r) r`.
* `IsSelfAdjoint.spectrum_one_sub_sq_subset_Icc`:
  `spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1`.
* `IsSelfAdjoint.pos_of_mem_spectrum_one_sub_sq`: strict positivity on `spectrum ℝ (1 - a ^ 2)`
  when `‖a‖ < 1`.
-/

public section

namespace IsSelfAdjoint

section Isometric

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A} {r : ℝ}

/-- The norm of a self-adjoint element is at most `r ≥ 0` exactly when its real spectrum lies
in the interval `[-r, r]`. -/
theorem norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  simpa [Set.subset_def, abs_le, cfc_id' ℝ a] using norm_cfc_le_iff (id : ℝ → ℝ) a hr

end Isometric

section Spectrum

open scoped ContinuousFunctionalCalculus

/-- For a self-adjoint element `a` in a normed algebra with continuous functional calculus and
summable geometric series, `spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1`. -/
theorem spectrum_one_sub_sq_subset_Icc {A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [HasSummableGeomSeries A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1 := by
  intro x hx
  rcases subsingleton_or_nontrivial A with _ | _
  · exact (hx (isUnit_of_subsingleton _)).elim
  have hcfc : cfc (fun t : ℝ ↦ 1 - t ^ 2) a = 1 - a ^ 2 := by
    rw [cfc_sub _ _ a, cfc_const_one ℝ _ ha, cfc_pow _ 2 a, cfc_id' ℝ _ ha]
  rw [← hcfc, cfc_map_spectrum (fun t : ℝ ↦ 1 - t ^ 2) a ha (by fun_prop)] at hx
  rcases hx with ⟨t, ht, rfl⟩
  have ht_abs : |t| ≤ ‖a‖ := by
    simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem ht
  have ht_sq : t ^ 2 ≤ ‖a‖ ^ 2 := (sq_abs t).symm ▸ pow_le_pow_left₀ (abs_nonneg t) ht_abs 2
  exact ⟨by linarith, by linarith [sq_nonneg t]⟩

/-- For self-adjoint `a` with `‖a‖ < 1`, every element of `spectrum ℝ (1 - a ^ 2)` is
strictly positive. -/
theorem pos_of_mem_spectrum_one_sub_sq {A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [HasSummableGeomSeries A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a) (h : ‖a‖ < 1) {x : ℝ} (hx : x ∈ spectrum ℝ (1 - a ^ 2)) :
    0 < x := by
  have hmem := ha.spectrum_one_sub_sq_subset_Icc hx
  nlinarith [norm_nonneg a, hmem.1]

end Spectrum

end IsSelfAdjoint
