/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Derivatives in inner product spaces

## Complex derivatives of inner products

The inner product `⟪x, y⟫` of a complex inner product space is conjugate-linear in `x`, so the
inner product `⟪f w, g w⟫` of two holomorphic families is not holomorphic in general. It is
holomorphic when the first family is *antiholomorphic*, that is of the form `w ↦ f (conj w)` with
`f` holomorphic: the two conjugations cancel. This is the form in which inner products of analytic
families of vectors enter Stein's interpolation argument and the three-lines theorem.

## The radial map onto a ball

Mathlib's `OpenPartialHomeomorph.univUnitBall`, `x ↦ x / √(1 + ‖x‖²)`, maps a real inner product
space diffeomorphically onto its open unit ball, and `OpenPartialHomeomorph.univBall c r`,
`x ↦ c + r x / √(1 + ‖x‖²)`, is its rescaling onto the ball of radius `r` about `c`. Mathlib
proves that both are smooth; this file computes their derivatives. The first is
`v ↦ s v - s³ ⟪x, v⟫ x`, where `s = 1 / √(1 + ‖x‖²)`: a multiple `s` of the identity on the
orthogonal complement of `x`, multiplying `x` itself by `s³`. The second is `r` times the first.

## The second derivative of the squared norm

On a real inner product space the squared norm `x ↦ ‖x‖²` has constant second derivative
`2 • innerSL ℝ`, twice the inner product.

## Phases of Fourier integrals under a change of variables

A change of variables `f` in a Fourier integral produces the phases `y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫`. Their
derivative in a direction `v` is `⟪v, (Df(x))† ζ - ξ⟫`, and their derivatives of order at least one
are bounded by `‖ζ‖` times those of `f`, plus `‖ξ‖`.

## Main results

* `TauCeti.fderiv_fderiv_norm_sq`, `TauCeti.fderiv_fderiv_norm_sq_apply`: the second derivative
  of the squared norm is `2 • innerSL ℝ`, so it sends `(u, v)` to `2 ⟪u, v⟫`.
* `TauCeti.fderiv_inner_sub_inner_apply`: the derivative of `y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫` in the
  direction `v` is `⟪v, (Df(x))† ζ - ξ⟫`.
* `TauCeti.norm_iteratedFDeriv_succ_inner_sub_inner_le`: the bound on the derivatives of order at
  least one of `y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫`.
* `HasDerivAt.inner_comp_conj`: if `f` has derivative `f'` at `conj z` and `g` has derivative `g'`
  at `z`, then `w ↦ ⟪f (conj w), g w⟫` has derivative `⟪f', g z⟫ + ⟪f (conj z), g'⟫` at `z`.
* `OpenPartialHomeomorph.hasFDerivAt_univUnitBall`: the derivative of the radial map onto the
  unit ball.
* `OpenPartialHomeomorph.hasFDerivAt_univBall`: the derivative of the radial map onto a ball of
  radius `r > 0`.
-/

public section

open scoped InnerProductSpace ComplexConjugate RealInnerProductSpace InnerProduct

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The inner product of an antiholomorphic and a holomorphic family is holomorphic: if `f` has
complex derivative `f'` at `conj z` and `g` has complex derivative `g'` at `z`, then
`w ↦ ⟪f (conj w), g w⟫` has complex derivative `⟪f', g z⟫ + ⟪f (conj z), g'⟫` at `z`. -/
theorem HasDerivAt.inner_comp_conj {f g : ℂ → X} {f' g' : X} {z : ℂ}
    (hf : HasDerivAt f f' (conj z)) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun w ↦ ⟪f (conj w), g w⟫_ℂ) (⟪f', g z⟫_ℂ + ⟪f (conj z), g'⟫_ℂ) z := by
  -- Over `ℝ`, `w ↦ f (conj w)` is differentiable with derivative `h ↦ conj h • f'`.
  have hf₁ : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)
      (Complex.conjCLE z) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hD := (hf₁.comp z Complex.conjCLE.hasFDerivAt).inner ℂ (hg.hasFDerivAt.restrictScalars ℝ)
  refine hasDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_of_restrictScalars ℝ hD ?_)
  ext1 h
  simp [fderivInnerCLM_apply, inner_smul_left, inner_smul_right, mul_add, add_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The second derivative of the squared norm is twice the inner product:
`D²(‖·‖²)(y) = 2 • innerSL ℝ` at every point `y`. -/
theorem TauCeti.fderiv_fderiv_norm_sq (y : E) :
    fderiv ℝ (fderiv ℝ fun z : E ↦ ‖z‖ ^ 2) y = 2 • innerSL ℝ := by
  rw [fderiv_norm_sq]
  exact (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv

/-- The second derivative of the squared norm is twice the inner product, evaluated:
`D²(‖·‖²)(y)(u, v) = 2 ⟪u, v⟫`. -/
theorem TauCeti.fderiv_fderiv_norm_sq_apply (y u v : E) :
    fderiv ℝ (fderiv ℝ (fun z : E ↦ ‖z‖ ^ 2)) y u v = 2 * inner ℝ u v := by
  rw [TauCeti.fderiv_fderiv_norm_sq]
  simp only [two_smul, add_apply]
  rw [innerSL_apply_apply]
  ring

section UnitBall

/-- **The derivative of the radial map onto the unit ball.** Mathlib's
`OpenPartialHomeomorph.univUnitBall`, `x ↦ (√(1 + ‖x‖²))⁻¹ • x`, has derivative
`v ↦ s • v - (s³ ⟪x, v⟫) • x` at `x`, where `s = (√(1 + ‖x‖²))⁻¹`. -/
theorem OpenPartialHomeomorph.hasFDerivAt_univUnitBall (x : E) :
    HasFDerivAt (univUnitBall : E → E)
      ((√(1 + ‖x‖ ^ 2))⁻¹ • ContinuousLinearMap.id ℝ E -
        (√(1 + ‖x‖ ^ 2))⁻¹ ^ 3 • (innerSL ℝ x).smulRight x) x := by
  have hpos : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have h₁ : HasFDerivAt (fun y : E ↦ 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1
  have h₂ : HasFDerivAt (fun y : E ↦ √(1 + ‖y‖ ^ 2)) _ x := h₁.sqrt hpos.ne'
  have h₃ := HasFDerivAt.smul
    ((hasFDerivAt_inv (Real.sqrt_ne_zero'.2 hpos)).comp x h₂) (hasFDerivAt_id x)
  convert h₃ using 1
  · funext y
    exact univUnitBall_apply y
  · ext v
    have hs : √(1 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [sub_apply, smul_apply, add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      Function.comp_apply, id, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      nsmul_eq_mul]
    match_scalars <;> field_simp

/-- **The derivative of the radial map onto a ball.** For `r > 0`, Mathlib's
`OpenPartialHomeomorph.univBall c r`, `x ↦ c + r x / √(1 + ‖x‖²)`, has derivative
`v ↦ (r / √(1 + ‖x‖²)) • v - (r / √(1 + ‖x‖²)³ * ⟪x, v⟫) • x` at `x`. -/
theorem OpenPartialHomeomorph.hasFDerivAt_univBall {r : ℝ} (hr : 0 < r) (c x : E) :
    HasFDerivAt (univBall c r)
      ((r / √(1 + ‖x‖ ^ 2)) • ContinuousLinearMap.id ℝ E -
        (r / √(1 + ‖x‖ ^ 2) ^ 3) • (innerSL ℝ x).smulRight x) x := by
  convert ((hasFDerivAt_univUnitBall x).const_smul r).add_const c using 1
  · funext y
    rw [univBall_apply hr, vadd_eq_add, Pi.smul_apply, univUnitBall_apply, smul_smul,
      div_eq_mul_inv]
  · rw [smul_sub, smul_smul, smul_smul, div_eq_mul_inv, div_eq_mul_inv, inv_pow]

end UnitBall

section Phase

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The derivatives of order at least one of the phase `y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫` are bounded by
`‖ζ‖` times those of `f`, plus `‖ξ‖`. -/
theorem norm_iteratedFDeriv_succ_inner_sub_inner_le {f : E → F} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ (k + 1 : ℕ) f x) (ξ : E) (ζ : F) :
    ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫) x‖ ≤
      ‖ζ‖ * ‖iteratedFDeriv ℝ (k + 1) f x‖ + ‖ξ‖ := by
  have hζ : (fun y ↦ ⟪f y, ζ⟫) = innerSL ℝ ζ ∘ f := by
    ext y
    simp [real_inner_comm]
  have hξ : (fun y : E ↦ ⟪y, ξ⟫) = innerSL ℝ ξ := by
    ext y
    simp [real_inner_comm]
  rw [fun_iteratedFDeriv_sub_apply (hf.inner ℝ contDiffAt_const)
    (contDiffAt_fun_id.inner ℝ contDiffAt_const), hζ, hξ]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [← innerSL_apply_norm ℝ ζ]
    exact (innerSL ℝ ζ).norm_iteratedFDeriv_comp_left hf le_rfl
  · rw [← innerSL_apply_norm ℝ ξ]
    exact (innerSL ℝ ξ).norm_iteratedFDeriv_le_norm k.succ_pos x

/-- The derivative of the phase `y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫` at `x` in the direction `v` is
`⟪v, (Df(x))† ζ - ξ⟫`. -/
theorem fderiv_inner_sub_inner_apply [CompleteSpace E] [CompleteSpace F] {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (ξ : E) (ζ : F) (v : E) :
    fderiv ℝ (fun y ↦ ⟪f y, ζ⟫ - ⟪y, ξ⟫) x v = ⟪v, ((fderiv ℝ f x)†) ζ - ξ⟫ := by
  rw [fderiv_fun_sub (hf.inner ℝ (differentiableAt_const ζ))
      (differentiableAt_fun_id.inner ℝ (differentiableAt_const ξ)),
    sub_apply, fderiv_inner_apply ℝ hf (differentiableAt_const ζ),
    fderiv_inner_apply ℝ differentiableAt_fun_id (differentiableAt_const ξ)]
  simp [inner_sub_right, ContinuousLinearMap.adjoint_inner_right]

end TauCeti

end Phase
