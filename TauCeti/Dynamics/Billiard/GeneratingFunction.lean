/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.NextCollision
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The generating function of a strictly convex billiard table

For a strictly convex billiard table with boundary parametrization `χ`, the *generating function*
of the billiard map is `S(s, t) = -‖χ(t) - χ(s)‖`, minus the length of the chord from `χ(s)` to
`χ(t)`. The roadmap considers it on `{(s, t) : s < t < s + L}`, where `χ(t) ≠ χ(s)`; the
statements here hold wherever `χ(t) ≠ χ(s)`. This file proves that it generates the next-collision
map `(s, v) ↦ (t, w)` and that it satisfies the twist condition:

* `S` is invariant under translating both arguments by the period `L`
  (`generatingFunction_add_period`);
* its partial derivatives at a chord are the tangential components of the unit chord vector, so
  at the next collision `v = ∂_s S(s, t)` and `w = -∂_t S(s, t)`
  (`hasDerivAt_generatingFunction_fst_nextParam`, `hasDerivAt_generatingFunction_snd_nextParam`);
* its mixed partial derivative is `∂_s ∂_t S(s, t) = ω(d, χ'(s)) ω(d, χ'(t)) / ‖d‖ ^ 3` with
  `d = χ(t) - χ(s)`, in either order of differentiation
  (`hasDerivAt_deriv_generatingFunction_snd`, `hasDerivAt_deriv_generatingFunction_fst`);
* the twist condition `∂_s ∂_t S < 0` holds at every chord, by strict convexity
  (`deriv_deriv_generatingFunction_snd_neg`), and at the next collision
  `∂_s ∂_t S = -√(1 - v ^ 2) √(1 - w ^ 2) / ‖χ(t) - χ(s)‖`
  (`hasDerivAt_deriv_generatingFunction_snd_nextParam`).

The mixed partial derivative involves only first derivatives of `χ`, since each variable enters
`∂_t S` and `∂_s S` once through `χ` and once through `χ'` at the other variable. So none of these
statements needs more smoothness than the unit-speed derivative of a
`StrictConvexBilliardTable`.

## Main definitions

* `TauCeti.StrictConvexBilliardTable.generatingFunction`: the generating function
  `S(s, t) = -‖χ(t) - χ(s)‖`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2.
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Set Filter Topology Module
open scoped RealInnerProductSpace

namespace TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

omit [Fact (finrank ℝ E = 2)] in
/-- The derivative of the norm of a curve at a point where it does not vanish. -/
private theorem hasDerivAt_norm_of_ne_zero {c : ℝ → E} {c' : E} {x : ℝ} (hc : HasDerivAt c c' x)
    (h0 : c x ≠ 0) : HasDerivAt (fun y ↦ ‖c y‖) (⟪c x, c'⟫ / ‖c x‖) x := by
  have h := hc.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.2 h0))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  rw [mul_div_mul_left _ _ two_ne_zero]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-- The generating function `S(s, t) = -‖χ(t) - χ(s)‖` of the billiard map: minus the length of
the chord from `χ(s)` to `χ(t)`. It is meaningful as a generating function where
`χ(t) ≠ χ(s)`, for instance on `{(s, t) : s < t < s + L}`. -/
def generatingFunction (s t : ℝ) : ℝ :=
  -‖χ t - χ s‖

theorem generatingFunction_def (s t : ℝ) : χ.generatingFunction s t = -‖χ t - χ s‖ :=
  (rfl)

/-- The generating function is invariant under translating both arguments by the period. -/
@[simp]
theorem generatingFunction_add_period (s t : ℝ) :
    χ.generatingFunction (s + χ.period) (t + χ.period) = χ.generatingFunction s t := by
  simp [generatingFunction_def, χ.periodic s, χ.periodic t]

/-! ### First derivatives -/

/-- The partial derivative `∂_s S(s, t) = ⟪d, χ'(s)⟫ / ‖d‖` with `d = χ(t) - χ(s)`: the
tangential component at `χ(s)` of the unit chord vector. -/
theorem hasDerivAt_generatingFunction_fst {s t : ℝ} (h : χ t ≠ χ s) :
    HasDerivAt (fun s' ↦ χ.generatingFunction s' t)
      (⟪χ t - χ s, deriv χ s⟫ / ‖χ t - χ s‖) s := by
  have hd := hasDerivAt_norm_of_ne_zero ((χ.differentiableAt s).hasDerivAt.const_sub (χ t))
    (sub_ne_zero.2 h)
  exact hd.neg.congr_deriv (by rw [inner_neg_right, neg_div, neg_neg])

/-- The partial derivative `∂_t S(s, t) = -⟪d, χ'(t)⟫ / ‖d‖` with `d = χ(t) - χ(s)`: minus the
tangential component at `χ(t)` of the unit chord vector. -/
theorem hasDerivAt_generatingFunction_snd {s t : ℝ} (h : χ t ≠ χ s) :
    HasDerivAt (fun t' ↦ χ.generatingFunction s t')
      (-(⟪χ t - χ s, deriv χ t⟫ / ‖χ t - χ s‖)) t :=
  (hasDerivAt_norm_of_ne_zero ((χ.differentiableAt t).hasDerivAt.sub_const (χ s))
    (sub_ne_zero.2 h)).neg

/-- Along the chord of the next collision, the unit chord vector is the outgoing velocity. -/
theorem inner_sub_div_norm_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) (x : E) :
    ⟪χ (χ.nextParam s v) - χ s, x⟫ / ‖χ (χ.nextParam s v) - χ s‖ = ⟪χ.outgoingDir s v, x⟫ := by
  have hr : ‖χ (χ.nextParam s v) - χ s‖ ≠ 0 :=
    norm_ne_zero_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  have h := congrArg (⟪·, x⟫) (χ.sub_eq_norm_smul_outgoingDir (s := s) hv)
  simp only [real_inner_smul_left] at h
  rw [h, mul_div_cancel_left₀ _ hr]

/-- The generating function recovers the tangential component of the initial state:
`v = ∂_s S(s, t)` at the next collision parameter `t`. -/
theorem hasDerivAt_generatingFunction_fst_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt (fun s' ↦ χ.generatingFunction s' (χ.nextParam s v)) v s := by
  convert χ.hasDerivAt_generatingFunction_fst (χ.apply_nextParam_ne hv) using 1
  rw [χ.inner_sub_div_norm_nextParam hv, real_inner_comm, inner_deriv_outgoingDir]

/-- The generating function recovers the tangential component of the next state:
`w = -∂_t S(s, t)` at the next collision parameter `t`. -/
theorem hasDerivAt_generatingFunction_snd_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt (fun t' ↦ χ.generatingFunction s t') (-χ.nextTangential s v) (χ.nextParam s v) := by
  convert χ.hasDerivAt_generatingFunction_snd (χ.apply_nextParam_ne hv) using 2
  rw [χ.inner_sub_div_norm_nextParam hv, nextTangential_def]

theorem deriv_generatingFunction_fst_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    deriv (fun s' ↦ χ.generatingFunction s' (χ.nextParam s v)) s = v :=
  (χ.hasDerivAt_generatingFunction_fst_nextParam hv).deriv

theorem deriv_generatingFunction_snd_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    deriv (fun t' ↦ χ.generatingFunction s t') (χ.nextParam s v) = -χ.nextTangential s v :=
  (χ.hasDerivAt_generatingFunction_snd_nextParam hv).deriv

/-! ### The mixed partial derivative and the twist condition -/

/-- The algebraic identity behind the mixed partial derivative: with `r = ‖d‖`,
`(r ^ 2 ⟪a, b⟫ - ⟪d, a⟫ ⟪d, b⟫) / r ^ 3 = ω(d, a) ω(d, b) / r ^ 3`. -/
private theorem mixed_eq (d a b : E) (hr : ‖d‖ ≠ 0) :
    (⟪a, b⟫ * ‖d‖ - ⟪d, b⟫ * (⟪d, a⟫ / ‖d‖)) / ‖d‖ ^ 2 =
      o.areaForm d a * o.areaForm d b / ‖d‖ ^ 3 := by
  have key := o.inner_mul_inner_add_areaForm_mul_areaForm d a b
  field_simp
  linear_combination -key

/-- The mixed partial derivative `∂_s ∂_t S(s, t) = ω(d, χ'(s)) ω(d, χ'(t)) / ‖d‖ ^ 3`, with
`d = χ(t) - χ(s)`, computed by differentiating `∂_t S` in `s`. -/
theorem hasDerivAt_deriv_generatingFunction_snd {s t : ℝ} (h : χ t ≠ χ s) :
    HasDerivAt (fun s' ↦ deriv (fun t' ↦ χ.generatingFunction s' t') t)
      (o.areaForm (χ t - χ s) (deriv χ s) * o.areaForm (χ t - χ s) (deriv χ t) /
        ‖χ t - χ s‖ ^ 3) s := by
  set T := deriv χ t
  have hc : HasDerivAt (fun s' ↦ χ t - χ s') (-deriv χ s) s :=
    (χ.differentiableAt s).hasDerivAt.const_sub (χ t)
  have h0 : χ t - χ s ≠ 0 := sub_ne_zero.2 h
  have hr : ‖χ t - χ s‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hinner : HasDerivAt (fun s' ↦ ⟪χ t - χ s', T⟫) ⟪-deriv χ s, T⟫ s := by
    simpa using hc.inner ℝ (hasDerivAt_const s T)
  have hq := (hinner.div (hasDerivAt_norm_of_ne_zero hc h0) hr).neg
  have heq : (fun s' ↦ deriv (fun t' ↦ χ.generatingFunction s' t') t) =ᶠ[𝓝 s]
      fun s' ↦ -(⟪χ t - χ s', T⟫ / ‖χ t - χ s'‖) := by
    filter_upwards [χ.continuous.continuousAt.eventually_ne h.symm] with s' hs'
    exact (χ.hasDerivAt_generatingFunction_snd (Ne.symm hs')).deriv
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← mixed_eq (o := o) _ _ _ hr, inner_neg_left, inner_neg_right]
  ring

/-- The mixed partial derivative `∂_t ∂_s S(s, t) = ω(d, χ'(s)) ω(d, χ'(t)) / ‖d‖ ^ 3`, with
`d = χ(t) - χ(s)`, computed by differentiating `∂_s S` in `t`. -/
theorem hasDerivAt_deriv_generatingFunction_fst {s t : ℝ} (h : χ t ≠ χ s) :
    HasDerivAt (fun t' ↦ deriv (fun s' ↦ χ.generatingFunction s' t') s)
      (o.areaForm (χ t - χ s) (deriv χ s) * o.areaForm (χ t - χ s) (deriv χ t) /
        ‖χ t - χ s‖ ^ 3) t := by
  set A := deriv χ s
  have hc : HasDerivAt (fun t' ↦ χ t' - χ s) (deriv χ t) t :=
    (χ.differentiableAt t).hasDerivAt.sub_const (χ s)
  have h0 : χ t - χ s ≠ 0 := sub_ne_zero.2 h
  have hr : ‖χ t - χ s‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hinner : HasDerivAt (fun t' ↦ ⟪χ t' - χ s, A⟫) ⟪deriv χ t, A⟫ t := by
    simpa using hc.inner ℝ (hasDerivAt_const t A)
  have hq := hinner.div (hasDerivAt_norm_of_ne_zero hc h0) hr
  have heq : (fun t' ↦ deriv (fun s' ↦ χ.generatingFunction s' t') s) =ᶠ[𝓝 t]
      fun t' ↦ ⟪χ t' - χ s, A⟫ / ‖χ t' - χ s‖ := by
    filter_upwards [χ.continuous.continuousAt.eventually_ne h] with t' ht'
    exact (χ.hasDerivAt_generatingFunction_fst ht').deriv
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← mixed_eq (o := o) _ _ _ hr, real_inner_comm A]
  ring

/-- At every chord of the table, the mixed partial derivative of the generating function is
negative: `ω(d, χ'(s)) < 0 < ω(d, χ'(t))` for `d = χ(t) - χ(s)`, by strict convexity. -/
theorem areaForm_mul_areaForm_div_neg {s t : ℝ} (h : χ t ≠ χ s) :
    o.areaForm (χ t - χ s) (deriv χ s) * o.areaForm (χ t - χ s) (deriv χ t) /
      ‖χ t - χ s‖ ^ 3 < 0 := by
  have hs := χ.areaForm_pos s t h
  have ht := χ.areaForm_pos t s h.symm
  rw [← neg_sub, map_neg] at ht
  have hr : 0 < ‖χ t - χ s‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
  rw [o.areaForm_swap (χ t - χ s) (deriv χ s), o.areaForm_swap (χ t - χ s) (deriv χ t)]
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- The twist condition: `∂_s ∂_t S(s, t) < 0` at every chord of the table. -/
theorem deriv_deriv_generatingFunction_snd_neg {s t : ℝ} (h : χ t ≠ χ s) :
    deriv (fun s' ↦ deriv (fun t' ↦ χ.generatingFunction s' t') t) s < 0 := by
  rw [(χ.hasDerivAt_deriv_generatingFunction_snd h).deriv]
  exact χ.areaForm_mul_areaForm_div_neg h

/-- At the next collision `(t, w)` of the state `(s, v)`, the mixed partial derivative of the
generating function is `-√(1 - v ^ 2) √(1 - w ^ 2) / ‖χ(t) - χ(s)‖`. -/
theorem hasDerivAt_deriv_generatingFunction_snd_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt (fun s' ↦ deriv (fun t' ↦ χ.generatingFunction s' t') (χ.nextParam s v))
      (-(√(1 - v ^ 2) * √(1 - χ.nextTangential s v ^ 2)) /
        ‖χ (χ.nextParam s v) - χ s‖) s := by
  convert χ.hasDerivAt_deriv_generatingFunction_snd (χ.apply_nextParam_ne hv) using 1
  have hr : ‖χ (χ.nextParam s v) - χ s‖ ≠ 0 :=
    norm_ne_zero_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  have hA : o.areaForm (χ (χ.nextParam s v) - χ s) (deriv χ s) =
      -(‖χ (χ.nextParam s v) - χ s‖ * √(1 - v ^ 2)) := by
    conv_lhs => rw [χ.sub_eq_norm_smul_outgoingDir hv]
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, o.areaForm_swap, areaForm_deriv_outgoingDir,
      mul_neg]
  have hT : o.areaForm (χ (χ.nextParam s v) - χ s) (deriv χ (χ.nextParam s v)) =
      ‖χ (χ.nextParam s v) - χ s‖ * √(1 - χ.nextTangential s v ^ 2) := by
    conv_lhs => rw [χ.sub_eq_norm_smul_outgoingDir hv]
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, o.areaForm_swap,
      χ.areaForm_deriv_nextParam_outgoingDir hv, neg_neg]
  rw [hA, hT]
  field_simp

end StrictConvexBilliardTable

end TauCeti
