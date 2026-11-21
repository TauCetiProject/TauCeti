/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Self-adjoint contractions and symmetries in the continuous functional calculus

For a self-adjoint contraction `a` of a unital C⋆-algebra, `1 - a²` is positive
(`IsSelfAdjoint.one_sub_mul_self_nonneg`), so it has a positive square root `√(1 - a²)`. The
square root `CFC.sqrt x` of any element commutes with every element commuting with `x`
(`Commute.cfcSqrt`), so `√(1 - a²)` commutes with `a`. These are the entries of the self-adjoint
unitary `[[a, √(1 - a²)], [√(1 - a²), -a]]` dilating `a`.

A self-adjoint unitary `γ` that anticommutes with a self-adjoint `a` conjugates `a` to `-a`, so it
anticommutes with `f(a)` for every odd real function `f` (`IsSelfAdjoint.mul_cfc_eq_neg_cfc_mul`).
This is how a grading passes through the functional calculus of an odd operator.
-/

public section

/-- The square root `CFC.sqrt x` commutes with every element that commutes with `x`. -/
protected theorem Commute.cfcSqrt {B : Type*} [PartialOrder B] [NonUnitalRing B]
    [TopologicalSpace B] [StarRing B] [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]
    [StarOrderedRing B] [NonUnitalContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
    [NonnegSpectrumClass ℝ B] [IsTopologicalRing B] [T2Space B] {x b : B} (h : Commute x b) :
    Commute (CFC.sqrt x) b :=
  h.cfcₙ_nnreal NNReal.sqrt

variable {A : Type*} [CStarAlgebra A]

namespace IsSelfAdjoint

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- For a self-adjoint contraction `a`, the element `1 - a²` is positive. -/
theorem one_sub_mul_self_nonneg {a : A} (ha : IsSelfAdjoint a) (ha₁ : ‖a‖ ≤ 1) :
    0 ≤ 1 - a * a := by
  rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg (a * a) ha.mul_self_nonneg,
    ha.norm_mul_self]
  nlinarith [norm_nonneg a]

end Order

/-- **A symmetry anticommutes with odd functions.** If `γ` is a self-adjoint unitary that
anticommutes with a self-adjoint `a`, then `γ` anticommutes with `f(a)` for every odd real
function `f`. -/
theorem mul_cfc_eq_neg_cfc_mul {γ a : A} (hγ : IsSelfAdjoint γ) (hγγ : γ * γ = 1)
    (ha : IsSelfAdjoint a) (hγa : γ * a = -(a * γ)) {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) :
    γ * cfc f a = -(cfc f a * γ) := by
  have hγu : γ ∈ unitary A := by rw [Unitary.mem_iff, hγ.star_eq, hγγ, and_self]
  set φ := Unitary.conjStarAlgAut ℂ A ⟨γ, hγu⟩
  have hφ (x : A) : φ x = γ * x * γ := by simp [φ, hγ.star_eq]
  have hφa : φ a = -a := by rw [hφ, hγa, neg_mul, mul_assoc, hγγ, mul_one]
  have hφc : Continuous φ := by
    rw [show (φ : A → A) = fun x => γ * x * γ from funext hφ]
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
  calc γ * cfc f a = γ * cfc f a * γ * γ := by rw [mul_assoc _ γ, hγγ, mul_one]
    _ = -(cfc f a * γ) := by rw [h, neg_mul]

end IsSelfAdjoint
