/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt

/-!
# Contractions and symmetries in the continuous functional calculus

For a contraction `a` of a unital C⋆-algebra, `1 - a⋆a` is positive
(`CStarAlgebra.one_sub_star_mul_self_nonneg`); for a self-adjoint contraction this is `1 - a²`
(`IsSelfAdjoint.one_sub_mul_self_nonneg`), so `a` has the positive square root `√(1 - a²)`, which
commutes with `a` (`Commute.cfcSqrt_one_sub_mul_self`). These are the entries of the self-adjoint
unitary `[[a, √(1 - a²)], [√(1 - a²), -a]]` dilating `a`.

A unitary `u` that anticommutes with a self-adjoint `a` conjugates `a` to `-a`, so it
anticommutes with `f(a)` for every odd real function `f` (`Unitary.mul_cfc_eq_neg_cfc_mul`).
This is how a grading passes through the functional calculus of an odd operator.
-/

public section

variable {A : Type*} [CStarAlgebra A]

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- For a contraction `a`, the element `1 - a⋆a` is positive. -/
theorem CStarAlgebra.one_sub_star_mul_self_nonneg {a : A} (ha : ‖a‖ ≤ 1) :
    0 ≤ 1 - star a * a := by
  rw [sub_nonneg]
  refine (star_mul_le_algebraMap_norm_sq a).trans ?_
  rw [← sub_nonneg, ← map_one (algebraMap ℝ A), ← map_sub]
  exact algebraMap_nonneg A (sub_nonneg.2 (pow_le_one₀ (norm_nonneg a) ha))

/-- For a self-adjoint contraction `a`, the element `1 - a²` is positive. -/
theorem IsSelfAdjoint.one_sub_mul_self_nonneg {a : A} (ha : IsSelfAdjoint a) (ha₁ : ‖a‖ ≤ 1) :
    0 ≤ 1 - a * a := by
  simpa only [ha.star_eq] using CStarAlgebra.one_sub_star_mul_self_nonneg ha₁

end Order

namespace Unitary

/-- **A unitary anticommuting with `a` anticommutes with odd functions of `a`.** If `u` is a
unitary that anticommutes with a self-adjoint `a`, then `u` anticommutes with `f(a)` for every odd
real function `f`. -/
theorem mul_cfc_eq_neg_cfc_mul {u a : A} (hu : u ∈ unitary A) (ha : IsSelfAdjoint a)
    (hua : u * a = -(a * u)) {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    u * cfc f a = -(cfc f a * u) := by
  set φ := Unitary.conjStarAlgAut ℂ A ⟨u, hu⟩
  have hφ (x : A) : φ x = u * x * star u := by simp [φ]
  have hφa : φ a = -a := by
    rw [hφ, hua, neg_mul, mul_assoc, Unitary.mul_star_self_of_mem hu, mul_one]
  have hφc : Continuous φ := by
    rw [show (φ : A → A) = fun x => u * x * star u from funext hφ]
    fun_prop
  have h : φ (cfc f a) = -cfc f a := by
    by_cases hfc : ContinuousOn f (spectrum ℝ a)
    · have hfc' : ContinuousOn f ((-·) '' spectrum ℝ a) := by
        refine ((hfc.comp continuous_neg.continuousOn ?_).neg).congr fun y _ => ?_
        · rintro _ ⟨x, hx, rfl⟩
          simpa using hx
        · simp [hf]
      rw [StarAlgHomClass.map_cfc (S := ℂ) φ f a hfc hφc ha (hφa ▸ ha.neg), hφa,
        ← cfc_comp_neg f a hfc', ← cfc_neg ..]
      exact cfc_congr fun x _ => hf x
    · rw [cfc_apply_of_not_continuousOn a hfc, map_zero, neg_zero]
  rw [hφ] at h
  calc u * cfc f a = u * cfc f a * star u * u := by
        rw [mul_assoc _ (star u), Unitary.star_mul_self_of_mem hu, mul_one]
    _ = -(cfc f a * u) := by rw [h, neg_mul]

end Unitary
