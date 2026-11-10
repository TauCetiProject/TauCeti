/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Bochner.CharFun.PosDef
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Characteristic functions as positive-definite functions

This file connects the quadratic-form positivity calculation for characteristic functions to
Tau Ceti's generic positive-definite-function predicate. If the involution on an additive group is
negation, then Mathlib's characteristic function `MeasureTheory.charFun μ` of a measure is
`TauCeti.IsPositiveDefinite`.

Together with Mathlib's continuity theorem for characteristic functions, this shows that the
characteristic function of a finite measure is continuous and positive definite, the easy
direction of Bochner's theorem.

## Main declarations

* `TauCeti.charFun_isPositiveDefinite_of_star_eq_neg`: `charFun μ` is positive definite for any
  explicit `star = -` involution.
* `TauCeti.continuous_charFun_and_isPositiveDefinite_of_star_eq_neg`: the paired continuity and
  positive-definiteness package.
* `TauCeti.isPositiveDefiniteSub_charFun`: `charFun μ` is positive definite in the
  subtraction form `TauCeti.IsPositiveDefiniteSub`, with no choice of involution.
-/

public section

open MeasureTheory

namespace TauCeti

open scoped ComplexOrder

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- The characteristic function of a measure is positive definite for any additive-group
involution that is explicitly negation. This is the generic-predicate form of
`charFun_sum_mul_conj_nonneg`, using
`F (vᵢ + star vⱼ) = charFun μ (vᵢ - vⱼ)`. -/
theorem charFun_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E] (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefinite (MeasureTheory.charFun μ) := by
  intro n c v
  refine le_of_le_of_eq (charFun_sum_mul_conj_nonneg (μ := μ) Finset.univ c v) ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [hstar, sub_eq_add_neg]

/-- The characteristic function of a measure is positive definite in the subtraction form:
`∑ i, ∑ j, c i * conj (c j) * charFun μ (v i - v j)` is nonnegative. -/
theorem isPositiveDefiniteSub_charFun : IsPositiveDefiniteSub (MeasureTheory.charFun μ) :=
  isPositiveDefiniteSub_iff_posSemidef.mpr posSemidef_charFun

/-- The characteristic function of a measure on a real inner product space is continuous and
positive definite, provided the chosen involution is negation. This is the forward bridge toward
Bochner's theorem in the language of `TauCeti.IsPositiveDefinite`. For a measure that is not
finite, `charFun μ` vanishes. -/
theorem continuous_charFun_and_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    Continuous (MeasureTheory.charFun μ) ∧ IsPositiveDefinite (MeasureTheory.charFun μ) := by
  refine ⟨?_, charFun_isPositiveDefinite_of_star_eq_neg hstar⟩
  by_cases hμ : IsFiniteMeasure μ
  · -- dominated convergence, with the constant bound `1` for the kernel
    simp_rw [funext charFun_apply]
    refine continuous_of_dominated (bound := fun _ ↦ 1)
      (fun t ↦ ?_) (fun t ↦ ?_) (integrable_const 1) (ae_of_all _ fun x ↦ ?_)
    · exact (by fun_prop : Continuous fun x : E ↦
        Complex.exp (inner ℝ x t * Complex.I)).aestronglyMeasurable
    · exact ae_of_all _ fun x ↦ (Complex.norm_exp_ofReal_mul_I _).le
    · fun_prop
  · rw [charFun_of_not_isFiniteMeasure hμ]
    exact continuous_zero

end Seminormed

end TauCeti
