/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Products and quadratic spectra in the unital continuous functional calculus

For an element `a` satisfying the predicate of a continuous functional calculus and a function `f`
continuous on its spectrum, multiplying `cfc f a` by `a` on either side is the functional calculus
of `f` multiplied by the identity on the same side. These are the cases `g = id` of Mathlib's
`cfc_mul`, stated in the form of `cfc_pow_id` and `cfc_smul_id`.

For a self-adjoint element `a` in a normed algebra with summable geometric series and continuous
functional calculus, we also record the spectral inclusion
`spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1` and its strict positivity when `‖a‖ < 1`.

## Main results

* `TauCeti.cfc_id_mul`: `cfc (fun x ↦ x * f x) a = a * cfc f a`.
* `TauCeti.cfc_mul_id`: `cfc (fun x ↦ f x * x) a = cfc f a * a`.
* `IsSelfAdjoint.spectrum_one_sub_sq_subset_Icc`:
  `spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1`.
* `IsSelfAdjoint.pos_of_mem_spectrum_one_sub_sq`: strict positivity on `spectrum ℝ (1 - a ^ 2)`
  when `‖a‖ < 1`.
-/

public section

namespace TauCeti

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- The functional calculus of `x ↦ x * f x` at `a` is `a * cfc f a`. -/
theorem cfc_id_mul (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (fun x ↦ x * f x) a = a * cfc f a := by
  rw [cfc_mul (fun x ↦ x) f a, cfc_id' R a]

/-- The functional calculus of `x ↦ f x * x` at `a` is `cfc f a * a`. -/
theorem cfc_mul_id (f : R → R) (a : A) (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : cfc (fun x ↦ f x * x) a = cfc f a * a := by
  rw [cfc_mul f (fun x ↦ x) a, cfc_id' R a]

end TauCeti

section Spectrum

open scoped ContinuousFunctionalCalculus

/-- For a self-adjoint element `a` in a normed algebra with continuous functional calculus and
summable geometric series, `spectrum ℝ (1 - a ^ 2) ⊆ Set.Icc (1 - ‖a‖ ^ 2) 1`. -/
theorem IsSelfAdjoint.spectrum_one_sub_sq_subset_Icc {A : Type*} [NormedRing A] [StarRing A]
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
theorem IsSelfAdjoint.pos_of_mem_spectrum_one_sub_sq {A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [HasSummableGeomSeries A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a) (h : ‖a‖ < 1) {x : ℝ} (hx : x ∈ spectrum ℝ (1 - a ^ 2)) :
    0 < x := by
  have hmem := ha.spectrum_one_sub_sq_subset_Icc hx
  nlinarith [norm_nonneg a, hmem.1]

end Spectrum
