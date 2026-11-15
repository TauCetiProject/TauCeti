/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.DAlembert
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive

/-!
# The inhomogeneous one-dimensional wave equation

This file solves the Cauchy problem for the one-dimensional wave equation with a forcing term,

`∂ₜ²u = ∂ₓ²u + G`, `u(0, x) = f(x)`, `∂ₜu(0, x) = g(x)`,

by d'Alembert's formula for the data and **Duhamel's formula** for the forcing,

`u(t, x) = dAlembert f g t x + (1 / 2) ∫_0^t ∫_{x - (t - s)}^{x + (t - s)} G(s, y) dy ds`.

The second term, `dAlembertDuhamel G`, superposes the free waves launched at each time `s` with
zero displacement and velocity `G(s, ·)`
(`TauCeti.PDE.dAlembertDuhamel_eq_integral_dAlembert`); it is the integral of `G / 2` over the
backward characteristic triangle with apex `(t, x)`. The conventions are those of
`TauCeti.Analysis.PDE.Wave.DAlembert`: functions take the time first, take values in a real
Banach space, and classical solutions are `C²` on the whole space-time plane.

* **Existence.** For `G` continuous with a continuous spatial derivative, `dAlembertDuhamel G` is
  `C²`, solves `∂ₜ²u = ∂ₓ²u + G` and has zero initial data; together with d'Alembert's formula it
  solves the Cauchy problem. No derivative of `G` in time is needed.
* **Representation, uniqueness and finite speed of propagation.** Every `C²` solution is the sum
  of d'Alembert's formula for its own data and Duhamel's formula for its forcing. Hence `u(t, x)`
  depends only on the data on `[x - |t|, x + |t|]` and on the forcing on the backward
  characteristic triangle with apex `(t, x)`. Uniqueness for the Cauchy problem needs no
  regularity of `G` at all.
* **Bound.** If `‖G‖ ≤ K` on that triangle, then `‖dAlembertDuhamel G t x‖ ≤ t² K / 2`. The
  constant forcing `G = K`, with solution `u = t² K / 2`, attains it.

## The argument

Writing `P(s, z) = ∫_0^z G(s, y) dy`, Duhamel's formula is half the integral
`∫_0^t (P(s, x + (t - s)) - P(s, x - (t - s))) ds` along the two backward characteristics through
`(t, x)`. Both its integrand and its upper limit depend on `t`, and the Leibniz integral rule
(`intervalIntegral.hasDerivAt_integral_of_hasDerivAt`) differentiates such integrals of the form
`∫_0^t (k(s, x + (t - s)) + c k(s, x - (t - s))) ds`. The derivatives are integrals of the same
form, with `k` replaced by its spatial derivative and, in time, the boundary term
`(1 + c) k(t, x)`. Applied to `P` and then to `G`, this gives

`∂ₜw = (1 / 2) ∫_0^t (G(s, x + (t - s)) + G(s, x - (t - s))) ds`,
`∂ₓw = (1 / 2) ∫_0^t (G(s, x + (t - s)) - G(s, x - (t - s))) ds`,

and, with `G'` the spatial derivative of `G`, `∂ₜ²w = G + (1 / 2) ∫_0^t (G' (…) - G' (…)) ds`
while `∂ₓ²w` is the same integral without the boundary term `G(t, x)`. The partial derivatives are
jointly continuous, so Mathlib's criterion `hasStrictFDerivAt_uncurry_coprod` makes `w` jointly
`C²`. The representation then reduces to the homogeneous equation,
`TauCeti.PDE.eq_dAlembert_of_deriv_deriv_eq`, applied to `u - w`.

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `dAlembertDuhamel`: Duhamel's formula for the forcing, and
  `dAlembertDuhamel_eq_integral_dAlembert`, Duhamel's principle.
* `hasDerivAt_dAlembertDuhamel_time`, `hasDerivAt_dAlembertDuhamel_space`: its first
  derivatives.
* `contDiff_dAlembertDuhamel`, `deriv_deriv_dAlembertDuhamel`, `dAlembertDuhamel_time_zero`,
  `deriv_dAlembertDuhamel_zero`: it is a classical solution with zero initial data.
* `deriv_deriv_dAlembert_add_dAlembertDuhamel`: d'Alembert's and Duhamel's formulas together
  solve the Cauchy problem.
* `eq_dAlembert_add_dAlembertDuhamel_of_deriv_deriv_eq`: every classical solution is given by
  these formulas.
* `eq_of_deriv_deriv_eq_add_of_eqOn`, `eq_of_deriv_deriv_eq_add_of_eq_initial`: the domain of
  dependence and uniqueness.
* `norm_dAlembertDuhamel_le`: the bound `t² K / 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.4.1 (the nonhomogeneous
  problem and Duhamel's principle).
* F. John, *Partial Differential Equations*, 4th ed., Chapter 2, Section 1.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Set Function MeasureTheory intervalIntegral
open scoped Interval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Duhamel's formula -/

section Duhamel

variable {G G' : ℝ → ℝ → F} {t x : ℝ}

/-- **Duhamel's formula** for the one-dimensional wave equation with forcing `G`:
`dAlembertDuhamel G t x = (1 / 2) ∫_0^t ∫_{x - (t - s)}^{x + (t - s)} G(s, y) dy ds`, the integral
of `G / 2` over the backward characteristic triangle with apex `(t, x)`. It solves
`∂ₜ²u = ∂ₓ²u + G` with zero initial data. -/
def dAlembertDuhamel (G : ℝ → ℝ → F) (t x : ℝ) : F :=
  (2 : ℝ)⁻¹ • ∫ s in 0..t, ∫ y in x - (t - s)..x + (t - s), G s y

theorem dAlembertDuhamel_def (G : ℝ → ℝ → F) (t x : ℝ) :
    dAlembertDuhamel G t x =
      (2 : ℝ)⁻¹ • ∫ s in 0..t, ∫ y in x - (t - s)..x + (t - s), G s y :=
  (rfl)

/-- **Duhamel's principle.** Duhamel's formula superposes the solutions of the homogeneous wave
equation started at each time `s` with zero displacement and velocity `G(s, ·)`. -/
theorem dAlembertDuhamel_eq_integral_dAlembert (G : ℝ → ℝ → F) (t x : ℝ) :
    dAlembertDuhamel G t x = ∫ s in 0..t, dAlembert 0 (G s) (t - s) x := by
  simp [dAlembertDuhamel_def, dAlembert_def]

/-- At time zero, Duhamel's formula vanishes. -/
@[simp]
theorem dAlembertDuhamel_time_zero (G : ℝ → ℝ → F) (x : ℝ) : dAlembertDuhamel G 0 x = 0 := by
  simp [dAlembertDuhamel_def]

/-- Without forcing, Duhamel's formula vanishes. -/
@[simp]
theorem dAlembertDuhamel_zero : dAlembertDuhamel (0 : ℝ → ℝ → F) = 0 := by
  ext t x
  simp [dAlembertDuhamel_def]

/-- **The domain of dependence.** Duhamel's formula at `(t, x)` only depends on the forcing on the
backward characteristic triangle with apex `(t, x)`. -/
theorem dAlembertDuhamel_congr
    (hG : ∀ s ∈ uIcc 0 t, EqOn (G s) (G' s) (uIcc (x - (t - s)) (x + (t - s)))) :
    dAlembertDuhamel G t x = dAlembertDuhamel G' t x := by
  rw [dAlembertDuhamel_def, dAlembertDuhamel_def,
    integral_congr fun s hs ↦ integral_congr (hG s hs)]

/-- `∫_0^t |t - s| ds` has absolute value `t² / 2`, for either sign of `t`. -/
private theorem abs_integral_abs_sub (t : ℝ) : |(∫ s in (0 : ℝ)..t, |t - s|)| = t ^ 2 / 2 := by
  rw [integral_comp_sub_left (fun u ↦ |u|), sub_self, sub_zero]
  rcases le_total 0 t with ht | ht
  · rw [integral_congr fun u hu ↦ abs_of_nonneg (uIcc_of_le ht ▸ hu).1, integral_id,
      zero_pow two_ne_zero, sub_zero, abs_of_nonneg (by positivity)]
  · rw [integral_congr fun u hu ↦ abs_of_nonpos (uIcc_of_ge ht ▸ hu).2,
      intervalIntegral.integral_neg, integral_id, zero_pow two_ne_zero, sub_zero, abs_neg,
      abs_of_nonneg (by positivity)]

/-- **A priori bound.** If `‖G‖ ≤ K` on the backward characteristic triangle with apex `(t, x)`,
then `‖dAlembertDuhamel G t x‖ ≤ t² K / 2`. The constant forcing `G = K` attains the bound. -/
theorem norm_dAlembertDuhamel_le {K : ℝ}
    (hG : ∀ s ∈ uIcc 0 t, ∀ y ∈ uIcc (x - (t - s)) (x + (t - s)), ‖G s y‖ ≤ K) :
    ‖dAlembertDuhamel G t x‖ ≤ t ^ 2 / 2 * K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hG t right_mem_uIcc x (by simp))
  have hinner : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ y in x - (t - s)..x + (t - s), G s y‖ ≤ 2 * K * |t - s| := by
    intro s hs
    have h := norm_integral_le_of_norm_le_const
      fun y hy ↦ hG s (uIoc_subset_uIcc hs) y (uIoc_subset_uIcc hy)
    rwa [show x + (t - s) - (x - (t - s)) = 2 * (t - s) by ring, abs_mul, abs_two,
      ← mul_assoc, mul_comm K] at h
  have houter := norm_integral_le_abs_of_norm_le (μ := volume)
    ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ hinner))
    ((by fun_prop : Continuous fun s : ℝ ↦ 2 * K * |t - s|).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity),
    abs_integral_abs_sub] at houter
  rw [dAlembertDuhamel_def, norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith

end Duhamel

/-! ### Integrals along the backward characteristics -/

section Characteristic

/-- The integral `∫_0^t (k(s, x + (t - s)) + c k(s, x - (t - s))) ds` along the two backward
characteristics through `(t, x)`. Duhamel's formula and its first derivatives are of this form. -/
private def charIntegral (c : ℝ) (k : ℝ → ℝ → F) (t x : ℝ) : F :=
  ∫ s in 0..t, (k s (x + (t - s)) + c • k s (x - (t - s)))

private theorem charIntegral_one (k : ℝ → ℝ → F) (t x : ℝ) :
    charIntegral 1 k t x = ∫ s in 0..t, (k s (x + (t - s)) + k s (x - (t - s))) := by
  simp [charIntegral]

private theorem charIntegral_neg_one (k : ℝ → ℝ → F) (t x : ℝ) :
    charIntegral (-1) k t x = ∫ s in 0..t, (k s (x + (t - s)) - k s (x - (t - s))) := by
  simp [charIntegral, sub_eq_add_neg]

variable {k k' : ℝ → ℝ → F}

/-- The integrand of `charIntegral`, as a function of the space-time point and of `s`, is jointly
continuous. -/
private theorem continuous_charIntegrand (c : ℝ) (hk : Continuous (uncurry k)) :
    Continuous fun q : (ℝ × ℝ) × ℝ ↦
      k q.2 (q.1.2 + (q.1.1 - q.2)) + c • k q.2 (q.1.2 - (q.1.1 - q.2)) := by
  have h₁ : Continuous fun q : (ℝ × ℝ) × ℝ ↦ k q.2 (q.1.2 + (q.1.1 - q.2)) :=
    hk.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ ↦ (q.2, q.1.2 + (q.1.1 - q.2)))
  have h₂ : Continuous fun q : (ℝ × ℝ) × ℝ ↦ k q.2 (q.1.2 - (q.1.1 - q.2)) :=
    hk.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ ↦ (q.2, q.1.2 - (q.1.1 - q.2)))
  exact h₁.add (h₂.const_smul c)

private theorem continuous_charIntegral (c : ℝ) (hk : Continuous (uncurry k)) :
    Continuous (uncurry (charIntegral c k)) :=
  continuous_parametric_intervalIntegral_of_continuous (continuous_charIntegrand c hk)
    continuous_fst

variable [CompleteSpace F]

/-- The time derivative of `charIntegral`: the boundary term `(1 + c) k(t, x)` at `s = t` plus the
integral of the time derivative of the integrand. -/
private theorem hasDerivAt_charIntegral_time (c : ℝ) (hk : Continuous (uncurry k))
    (hk' : Continuous (uncurry k')) (hd : ∀ s z, HasDerivAt (k s) (k' s z) z) (t x : ℝ) :
    HasDerivAt (fun r ↦ charIntegral c k r x) ((1 + c) • k t x + charIntegral (-c) k' t x) t := by
  have hderiv (r s : ℝ) : HasDerivAt (fun r ↦ k s (x + (r - s)) + c • k s (x - (r - s)))
      (k' s (x + (r - s)) + (-c) • k' s (x - (r - s))) r := by
    have h₁ : HasDerivAt (fun r ↦ x + (r - s)) 1 r := ((hasDerivAt_id r).sub_const s).const_add x
    have h₂ : HasDerivAt (fun r ↦ x - (r - s)) (-1) r := ((hasDerivAt_id r).sub_const s).const_sub x
    exact (((hd s _).scomp r h₁).add (((hd s _).scomp r h₂).const_smul c)).congr_deriv
      (by module)
  have h := hasDerivAt_integral_of_hasDerivAt
    (f := fun r s ↦ k s (x + (r - s)) + c • k s (x - (r - s)))
    (f' := fun r s ↦ k' s (x + (r - s)) + (-c) • k' s (x - (r - s))) 0
    ((continuous_charIntegrand c hk).comp (by fun_prop :
      Continuous fun q : ℝ × ℝ ↦ ((q.1, x), q.2))) hderiv
    ((continuous_charIntegrand (-c) hk').comp (by fun_prop :
      Continuous fun q : ℝ × ℝ ↦ ((q.1, x), q.2))) (hasDerivAt_id t)
  refine h.congr_deriv ?_
  simp only [id_eq, sub_self, add_zero, sub_zero, one_smul, charIntegral]
  module

/-- The space derivative of `charIntegral`: the integral of the space derivative of the
integrand. -/
private theorem hasDerivAt_charIntegral_space (c : ℝ) (hk : Continuous (uncurry k))
    (hk' : Continuous (uncurry k')) (hd : ∀ s z, HasDerivAt (k s) (k' s z) z) (t x : ℝ) :
    HasDerivAt (charIntegral c k t) (charIntegral c k' t x) x := by
  have hderiv (y s : ℝ) : HasDerivAt (fun y ↦ k s (y + (t - s)) + c • k s (y - (t - s)))
      (k' s (y + (t - s)) + c • k' s (y - (t - s))) y := by
    have h₁ : HasDerivAt (fun y ↦ y + (t - s)) 1 y := (hasDerivAt_id y).add_const _
    have h₂ : HasDerivAt (fun y ↦ y - (t - s)) 1 y := (hasDerivAt_id y).sub_const _
    exact (((hd s _).scomp y h₁).add (((hd s _).scomp y h₂).const_smul c)).congr_deriv
      (by module)
  have h := hasDerivAt_integral_of_hasDerivAt (c := fun _ ↦ t)
    (f := fun y s ↦ k s (y + (t - s)) + c • k s (y - (t - s)))
    (f' := fun y s ↦ k' s (y + (t - s)) + c • k' s (y - (t - s))) 0
    ((continuous_charIntegrand c hk).comp (by fun_prop :
      Continuous fun q : ℝ × ℝ ↦ ((t, q.1), q.2))) hderiv
    ((continuous_charIntegrand c hk').comp (by fun_prop :
      Continuous fun q : ℝ × ℝ ↦ ((t, q.1), q.2))) (hasDerivAt_const x t)
  refine h.congr_deriv ?_
  simp [charIntegral]

/-- `charIntegral` is jointly strictly differentiable, with the partial derivatives of
`hasDerivAt_charIntegral_time` and `hasDerivAt_charIntegral_space`. -/
private theorem hasStrictFDerivAt_charIntegral (c : ℝ) (hk : Continuous (uncurry k))
    (hk' : Continuous (uncurry k')) (hd : ∀ s z, HasDerivAt (k s) (k' s z) z) (p : ℝ × ℝ) :
    HasStrictFDerivAt (uncurry (charIntegral c k))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          ((1 + c) • k p.1 p.2 + charIntegral (-c) k' p.1 p.2) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (charIntegral c k' p.1 p.2)) p := by
  have hc₁ : Continuous fun q : ℝ × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ
      ((1 + c) • k q.1 q.2 + charIntegral (-c) k' q.1 q.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp
      ((hk.const_smul _).add (continuous_charIntegral (-c) hk'))
  have hc₂ : Continuous fun q : ℝ × ℝ ↦
      ContinuousLinearMap.toSpanSingleton ℝ (charIntegral c k' q.1 q.2) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp (continuous_charIntegral c hk')
  have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := charIntegral c k)
    (f₁ := fun t x ↦ ContinuousLinearMap.toSpanSingleton ℝ
      ((1 + c) • k t x + charIntegral (-c) k' t x))
    (f₂ := fun t x ↦ ContinuousLinearMap.toSpanSingleton ℝ (charIntegral c k' t x))
    (Filter.Eventually.of_forall fun q ↦
      (hasDerivAt_charIntegral_time c hk hk' hd q.1 q.2).hasFDerivAt)
    (Filter.Eventually.of_forall fun q ↦
      (hasDerivAt_charIntegral_space c hk hk' hd q.1 q.2).hasFDerivAt)
    hc₁.continuousAt hc₂.continuousAt
  exact h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ by
    simp [Function.HasUncurry.uncurry, smul_add, add_assoc])

/-- `charIntegral` is `C¹` on space-time. -/
private theorem contDiff_charIntegral (c : ℝ) (hk : Continuous (uncurry k))
    (hk' : Continuous (uncurry k')) (hd : ∀ s z, HasDerivAt (k s) (k' s z) z) :
    ContDiff ℝ 1 (uncurry (charIntegral c k)) :=
  contDiff_one_iff_hasFDerivAt.2 ⟨_,
    (contDiff_zero.1 (contDiff_const.smulRight (contDiff_zero.2
        ((hk.const_smul _).add (continuous_charIntegral (-c) hk'))))).add
      (contDiff_zero.1 (contDiff_const.smulRight (contDiff_zero.2
        (continuous_charIntegral c hk')))),
    fun p ↦ (hasStrictFDerivAt_charIntegral c hk hk' hd p).hasFDerivAt⟩

end Characteristic

/-! ### Duhamel's formula solves the forced wave equation -/

section Solution

variable {G : ℝ → ℝ → F}

/-- The spatial primitive `(s, z) ↦ ∫_0^z G(s, y) dy` of a continuous forcing is continuous. -/
private theorem continuous_primitive (hG : Continuous (uncurry G)) :
    Continuous (uncurry fun s z ↦ ∫ y in 0..z, G s y) :=
  continuous_parametric_primitive_of_continuous hG

/-- Duhamel's formula is half the characteristic integral of the spatial primitive of `G`. -/
private theorem dAlembertDuhamel_eq_charIntegral (hG : Continuous (uncurry G)) (t x : ℝ) :
    dAlembertDuhamel G t x =
      (2 : ℝ)⁻¹ • charIntegral (-1) (fun s z ↦ ∫ y in 0..z, G s y) t x := by
  have hGs (s : ℝ) : Continuous (G s) := hG.comp (Continuous.prodMk_right s)
  rw [dAlembertDuhamel_def, charIntegral_neg_one]
  congr 1
  exact integral_congr fun s _ ↦ (integral_interval_sub_left (a := 0)
    ((hGs s).intervalIntegrable _ _) ((hGs s).intervalIntegrable _ _)).symm

variable [CompleteSpace F]

/-- The spatial primitive of a continuous forcing has spatial derivative `G`. -/
private theorem hasDerivAt_primitive (hG : Continuous (uncurry G)) (s z : ℝ) :
    HasDerivAt (fun z ↦ ∫ y in 0..z, G s y) (G s z) z :=
  ((hG.comp (Continuous.prodMk_right s)).integral_hasStrictDerivAt 0 z).hasDerivAt

/-- The time derivative of Duhamel's formula:
`∂ₜw(t, x) = (1 / 2) ∫_0^t (G(s, x + (t - s)) + G(s, x - (t - s))) ds`. -/
theorem hasDerivAt_dAlembertDuhamel_time (hG : Continuous (uncurry G)) (t x : ℝ) :
    HasDerivAt (fun s ↦ dAlembertDuhamel G s x)
      ((2 : ℝ)⁻¹ • ∫ s in 0..t, (G s (x + (t - s)) + G s (x - (t - s)))) t := by
  simp only [dAlembertDuhamel_eq_charIntegral hG]
  refine ((hasDerivAt_charIntegral_time (-1) (continuous_primitive hG) hG
    (hasDerivAt_primitive hG) t x).const_smul (2 : ℝ)⁻¹).congr_deriv ?_
  rw [neg_neg, charIntegral_one, add_neg_cancel, zero_smul, zero_add]

/-- The space derivative of Duhamel's formula:
`∂ₓw(t, x) = (1 / 2) ∫_0^t (G(s, x + (t - s)) - G(s, x - (t - s))) ds`. -/
theorem hasDerivAt_dAlembertDuhamel_space (hG : Continuous (uncurry G)) (t x : ℝ) :
    HasDerivAt (dAlembertDuhamel G t)
      ((2 : ℝ)⁻¹ • ∫ s in 0..t, (G s (x + (t - s)) - G s (x - (t - s)))) x := by
  rw [funext (dAlembertDuhamel_eq_charIntegral hG t), ← charIntegral_neg_one]
  exact (hasDerivAt_charIntegral_space (-1) (continuous_primitive hG) hG
    (hasDerivAt_primitive hG) t x).const_smul _

/-- At time zero, the time derivative of Duhamel's formula vanishes. -/
@[simp]
theorem deriv_dAlembertDuhamel_zero (hG : Continuous (uncurry G)) (x : ℝ) :
    deriv (fun t ↦ dAlembertDuhamel G t x) 0 = 0 := by
  simp [(hasDerivAt_dAlembertDuhamel_time hG 0 x).deriv]

variable (hG : Continuous (uncurry G)) (hGd : ∀ s, Differentiable ℝ (G s))
  (hGd' : Continuous (uncurry fun s ↦ deriv (G s)))
include hG hGd hGd'

/-- If `G` is continuous with a continuous spatial derivative, Duhamel's formula is `C²` on
space-time. No derivative of `G` in time is needed. -/
theorem contDiff_dAlembertDuhamel : ContDiff ℝ 2 (uncurry (dAlembertDuhamel G)) := by
  have hd (s z : ℝ) : HasDerivAt (G s) (deriv (G s) z) z := (hGd s z).hasDerivAt
  refine (contDiff_succ_iff_hasFDerivAt (n := 1)).2 ⟨fun p ↦
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight ((2 : ℝ)⁻¹ • charIntegral 1 G p.1 p.2) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight ((2 : ℝ)⁻¹ • charIntegral (-1) G p.1 p.2),
    (contDiff_const.smulRight ((contDiff_charIntegral 1 hG hGd' hd).const_smul _)).add
      (contDiff_const.smulRight ((contDiff_charIntegral (-1) hG hGd' hd).const_smul _)),
    fun p ↦ ?_⟩
  have h := ((hasStrictFDerivAt_charIntegral (-1) (continuous_primitive hG) hG
    (hasDerivAt_primitive hG) p).const_smul (2 : ℝ)⁻¹).hasFDerivAt
  have heq : uncurry (dAlembertDuhamel G) = fun q ↦ (2 : ℝ)⁻¹ •
      uncurry (charIntegral (-1) fun s z ↦ ∫ y in 0..z, G s y) q :=
    funext fun q ↦ dAlembertDuhamel_eq_charIntegral hG q.1 q.2
  rw [heq]
  exact h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ by simp [smul_comm _ (2 : ℝ)⁻¹])

/-- **Duhamel's formula solves the forced wave equation.** If `G` is continuous with a continuous
spatial derivative, `w = dAlembertDuhamel G` satisfies `∂ₜ²w = ∂ₓ²w + G` everywhere. -/
theorem deriv_deriv_dAlembertDuhamel (t x : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ dAlembertDuhamel G r x) s) t =
      deriv (deriv (dAlembertDuhamel G t)) x + G t x := by
  have hd (s z : ℝ) : HasDerivAt (G s) (deriv (G s) z) z := (hGd s z).hasDerivAt
  have ht : deriv (fun r ↦ dAlembertDuhamel G r x) = fun s ↦ (2 : ℝ)⁻¹ • charIntegral 1 G s x :=
    funext fun s ↦ by rw [(hasDerivAt_dAlembertDuhamel_time hG s x).deriv, charIntegral_one]
  have hx : deriv (dAlembertDuhamel G t) = fun y ↦ (2 : ℝ)⁻¹ • charIntegral (-1) G t y :=
    funext fun y ↦ by rw [(hasDerivAt_dAlembertDuhamel_space hG t y).deriv, charIntegral_neg_one]
  have h₁ : HasDerivAt (fun s ↦ (2 : ℝ)⁻¹ • charIntegral 1 G s x)
      ((2 : ℝ)⁻¹ • (((1 : ℝ) + 1) • G t x + charIntegral (-1) (fun s ↦ deriv (G s)) t x)) t :=
    (hasDerivAt_charIntegral_time 1 hG hGd' hd t x).const_smul _
  have h₂ : HasDerivAt (fun y ↦ (2 : ℝ)⁻¹ • charIntegral (-1) G t y)
      ((2 : ℝ)⁻¹ • charIntegral (-1) (fun s ↦ deriv (G s)) t x) x :=
    (hasDerivAt_charIntegral_space (-1) hG hGd' hd t x).const_smul _
  rw [ht, hx, h₁.deriv, h₂.deriv]
  module

end Solution

/-! ### The Cauchy problem -/

section CauchyProblem

variable {G G' : ℝ → ℝ → F} {u v : ℝ → ℝ → F}

/-- The second derivative of a sum of `C²` functions of one variable: Mathlib's
`iteratedDeriv_fun_add` at order two, written with `deriv`. -/
private theorem deriv_deriv_add_apply {a b : ℝ → F} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (z : ℝ) : deriv (deriv fun y ↦ a y + b y) z = deriv (deriv a) z + deriv (deriv b) z := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    iteratedDeriv_fun_add (n := 2) (x := z) ha.contDiffAt hb.contDiffAt

/-- The second derivative of a difference of `C²` functions of one variable: Mathlib's
`iteratedDeriv_fun_sub` at order two, written with `deriv`. -/
private theorem deriv_deriv_sub_apply {a b : ℝ → F} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (z : ℝ) : deriv (deriv fun y ↦ a y - b y) z = deriv (deriv a) z - deriv (deriv b) z := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    iteratedDeriv_fun_sub (n := 2) (x := z) ha.contDiffAt hb.contDiffAt

/-- The time slices `r ↦ u r x` of a `C²` function on space-time are `C²`. -/
private theorem contDiff_slice_time (hu : ContDiff ℝ 2 (uncurry u)) (x : ℝ) :
    ContDiff ℝ 2 fun r ↦ u r x :=
  hu.comp (contDiff_id.prodMk contDiff_const)

/-- The space slices `u t` of a `C²` function on space-time are `C²`. -/
private theorem contDiff_slice_space (hu : ContDiff ℝ 2 (uncurry u)) (t : ℝ) :
    ContDiff ℝ 2 (u t) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

/-- The difference of two `C²` solutions of `∂ₜ²u = ∂ₓ²u + G` with the same forcing solves the
homogeneous wave equation. -/
private theorem deriv_deriv_sub_eq (hu : ContDiff ℝ 2 (uncurry u))
    (hv : ContDiff ℝ 2 (uncurry v))
    (hwu : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x + G t x)
    (hwv : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ v r x) s) t = deriv (deriv (v t)) x + G t x)
    (t x : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ u r x - v r x) s) t =
      deriv (deriv fun y ↦ u t y - v t y) x := by
  rw [deriv_deriv_sub_apply (contDiff_slice_time hu x) (contDiff_slice_time hv x),
    deriv_deriv_sub_apply (contDiff_slice_space hu t) (contDiff_slice_space hv t), hwu, hwv]
  abel

variable [CompleteSpace F]

/-- **Uniqueness for the forced Cauchy problem.** Two `C²` solutions of `∂ₜ²u = ∂ₓ²u + G` on the
space-time plane with the same initial displacement and the same initial velocity are equal. No
regularity of the forcing `G` is needed. -/
theorem eq_of_deriv_deriv_eq_add_of_eq_initial (hu : ContDiff ℝ 2 (uncurry u))
    (hv : ContDiff ℝ 2 (uncurry v))
    (hwu : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x + G t x)
    (hwv : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ v r x) s) t = deriv (deriv (v t)) x + G t x)
    (h0 : u 0 = v 0) (h1 : ∀ y, deriv (fun s ↦ u s y) 0 = deriv (fun s ↦ v s y) 0) : u = v := by
  have h := eq_of_deriv_deriv_eq_of_eq_initial (u := fun t x ↦ u t x - v t x)
    (v := fun _ _ ↦ (0 : F)) (hu.sub hv) contDiff_const (deriv_deriv_sub_eq hu hv hwu hwv)
    (fun _ _ ↦ by simp) (funext fun y ↦ by simp [h0])
    (fun y ↦ by
      rw [deriv_fun_sub ((contDiff_slice_time hu y).differentiable two_ne_zero 0)
        ((contDiff_slice_time hv y).differentiable two_ne_zero 0), h1, sub_self, deriv_const])
  funext t x
  simpa [sub_eq_zero] using congrFun (congrFun h t) x

variable (hG : Continuous (uncurry G)) (hGd : ∀ s, Differentiable ℝ (G s))
  (hGd' : Continuous (uncurry fun s ↦ deriv (G s)))
include hG hGd hGd'

/-- **The forced Cauchy problem.** For `f` of class `C²`, `g` of class `C¹` and `G` continuous
with a continuous spatial derivative, `u = dAlembert f g + dAlembertDuhamel G` satisfies
`∂ₜ²u = ∂ₓ²u + G` everywhere. It is `C²` by `contDiff_dAlembert` and
`contDiff_dAlembertDuhamel`, and its initial displacement `f` and initial velocity `g` come from
`dAlembert_time_zero`, `deriv_dAlembert_zero` and their Duhamel counterparts. -/
theorem deriv_deriv_dAlembert_add_dAlembertDuhamel {f g : ℝ → F} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 1 g) (t x : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ dAlembert f g r x + dAlembertDuhamel G r x) s) t =
      deriv (deriv fun y ↦ dAlembert f g t y + dAlembertDuhamel G t y) x + G t x := by
  have hU := contDiff_dAlembert hf hg
  have hW := contDiff_dAlembertDuhamel hG hGd hGd'
  rw [deriv_deriv_add_apply (contDiff_slice_time hU x) (contDiff_slice_time hW x),
    deriv_deriv_add_apply (contDiff_slice_space hU t) (contDiff_slice_space hW t),
    deriv_deriv_dAlembert hf hg, deriv_deriv_dAlembertDuhamel hG hGd hGd']
  abel

/-- **Representation of classical solutions.** Every `C²` solution `u` of the forced wave equation
`∂ₜ²u = ∂ₓ²u + G` on the space-time plane is the sum of d'Alembert's formula for its initial
displacement `u(0, ·)` and initial velocity `∂ₜu(0, ·)` and Duhamel's formula for the forcing. No
growth condition at infinity is assumed. -/
theorem eq_dAlembert_add_dAlembertDuhamel_of_deriv_deriv_eq (hu : ContDiff ℝ 2 (uncurry u))
    (hwave : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x + G t x)
    (t x : ℝ) :
    u t x = dAlembert (u 0) (fun y ↦ deriv (fun s ↦ u s y) 0) t x + dAlembertDuhamel G t x := by
  have hW := contDiff_dAlembertDuhamel hG hGd hGd'
  have h := eq_dAlembert_of_deriv_deriv_eq (u := fun t x ↦ u t x - dAlembertDuhamel G t x)
    (hu.sub hW) (deriv_deriv_sub_eq hu hW hwave (deriv_deriv_dAlembertDuhamel hG hGd hGd')) t x
  have h1 (y : ℝ) : deriv (fun s ↦ u s y - dAlembertDuhamel G s y) 0 = deriv (fun s ↦ u s y) 0 := by
    rw [deriv_fun_sub ((contDiff_slice_time hu y).differentiable two_ne_zero 0)
      ((contDiff_slice_time hW y).differentiable two_ne_zero 0), deriv_dAlembertDuhamel_zero hG,
      sub_zero]
  simp only [dAlembertDuhamel_time_zero, sub_zero, h1] at h
  exact eq_add_of_sub_eq h

/-- **The domain of dependence.** Let `u` and `v` be `C²` solutions of `∂ₜ²u = ∂ₓ²u + G` and
`∂ₜ²v = ∂ₓ²v + G'`, with `G` and `G'` continuous with continuous spatial derivatives. If their
initial displacements and velocities agree on the interval between `x - t` and `x + t`, and the
forcings agree on the backward characteristic triangle with apex `(t, x)`, then `u` and `v` agree
at `(t, x)`: forced waves also propagate with speed at most one. -/
theorem eq_of_deriv_deriv_eq_add_of_eqOn (hG' : Continuous (uncurry G'))
    (hG'd : ∀ s, Differentiable ℝ (G' s)) (hG'd' : Continuous (uncurry fun s ↦ deriv (G' s)))
    (hu : ContDiff ℝ 2 (uncurry u)) (hv : ContDiff ℝ 2 (uncurry v))
    (hwu : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t = deriv (deriv (u t)) x + G t x)
    (hwv : ∀ t x, deriv (fun s ↦ deriv (fun r ↦ v r x) s) t = deriv (deriv (v t)) x + G' t x)
    {t x : ℝ} (h0 : EqOn (u 0) (v 0) (uIcc (x - t) (x + t)))
    (h1 : EqOn (fun y ↦ deriv (fun s ↦ u s y) 0) (fun y ↦ deriv (fun s ↦ v s y) 0)
      (uIcc (x - t) (x + t)))
    (hGG' : ∀ s ∈ uIcc 0 t, EqOn (G s) (G' s) (uIcc (x - (t - s)) (x + (t - s)))) :
    u t x = v t x := by
  rw [eq_dAlembert_add_dAlembertDuhamel_of_deriv_deriv_eq hG hGd hGd' hu hwu,
    eq_dAlembert_add_dAlembertDuhamel_of_deriv_deriv_eq hG' hG'd hG'd' hv hwv,
    dAlembert_congr h0 h1, dAlembertDuhamel_congr hGG']

end CauchyProblem

end PDE

end TauCeti
