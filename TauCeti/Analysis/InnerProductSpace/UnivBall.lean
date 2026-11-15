/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The derivative of the radial homeomorphism of a ball onto the space

Mathlib's `OpenPartialHomeomorph.univBall 0 r` maps a real normed space onto its open ball of
radius `r > 0`, and its inverse is `y ↦ y / √(r² - ‖y‖²)` on that ball
(`OpenPartialHomeomorph.univBall_zero_symm_apply`). In a real inner product space this file
computes the derivative of the inverse,

`D(y / √(r² - ‖y‖²)) v = v / √(r² - ‖y‖²) + ⟪y, v⟫ y / √(r² - ‖y‖²)³`

(`OpenPartialHomeomorph.fderiv_univBall_zero_symm_apply`), and in the Euclidean plane its Jacobian
determinant `r² / (r² - ‖y‖²)²` (`OpenPartialHomeomorph.det_fderiv_univBall_zero_symm`): the
derivative multiplies the determinant `p₀ q₁ - p₁ q₀` of two vectors by this factor. The factor is
the density of the area form that the map pulls back from the plane, which is what makes the
inverse of Lambert's azimuthal projection, this map followed by inverse stereographic projection,
equal-area (`TauCeti.eval₂_mfderiv_discToSphere`).
-/

public section

noncomputable section

open Metric
open scoped InnerProductSpace

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the inverse `y ↦ y / √(r² - ‖y‖²)` of `univBall 0 r` at a point `y` of the
open ball of radius `r` is `v ↦ v / √(r² - ‖y‖²) + ⟪y, v⟫ y / √(r² - ‖y‖²)³`. -/
theorem fderiv_univBall_zero_symm_apply {r : ℝ} {y : E} (hy : ‖y‖ < r) (v : E) :
    fderiv ℝ (univBall (0 : E) r).symm y v =
      (√(r ^ 2 - ‖y‖ ^ 2))⁻¹ • v + ((√(r ^ 2 - ‖y‖ ^ 2))⁻¹ ^ 3 * ⟪y, v⟫_ℝ) • y := by
  have hr : 0 < r := (norm_nonneg y).trans_lt hy
  set s := r ^ 2 - ‖y‖ ^ 2
  have hs : 0 < s := by
    have := (sq_lt_sq₀ (norm_nonneg y) hr.le).2 hy
    linarith
  have hsr : √s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hsq : HasFDerivAt (fun x : E ↦ r ^ 2 - ‖x‖ ^ 2) (-(2 • innerSL ℝ y)) y := by
    simpa using (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_sub (r ^ 2)
  have hinv : HasDerivAt (fun t : ℝ ↦ (√t)⁻¹) (-(1 / (2 * √s)) / √s ^ 2) s :=
    HasDerivAt.inv (Real.hasDerivAt_sqrt hs.ne') hsr
  have h := (hinv.comp_hasFDerivAt y hsq).smul (hasFDerivAt_id y)
  -- By the explicit formula, the inverse is the product of a scalar function and the identity.
  have hfun : ⇑(univBall (0 : E) r).symm =
      ((fun t : ℝ ↦ (√t)⁻¹) ∘ fun x : E ↦ r ^ 2 - ‖x‖ ^ 2) • id :=
    funext (univBall_zero_symm_apply hr)
  rw [hfun, h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, innerSL_apply_apply, Function.comp_apply, id_eq,
    smul_eq_mul]
  congr 2
  field_simp
  ring

/-- **The Jacobian determinant of the inverse of `univBall 0 r` in the plane** is
`r² / (r² - ‖y‖²)²`: the derivative of `y ↦ y / √(r² - ‖y‖²)` multiplies the determinant
`p₀ q₁ - p₁ q₀` of two vectors by this factor. -/
theorem det_fderiv_univBall_zero_symm {r : ℝ} {y : EuclideanSpace ℝ (Fin 2)} (hy : ‖y‖ < r)
    (p q : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (univBall 0 r).symm y p 0 * fderiv ℝ (univBall 0 r).symm y q 1 -
        fderiv ℝ (univBall 0 r).symm y p 1 * fderiv ℝ (univBall 0 r).symm y q 0 =
      r ^ 2 / (r ^ 2 - ‖y‖ ^ 2) ^ 2 * (p 0 * q 1 - p 1 * q 0) := by
  have hr : 0 < r := (norm_nonneg y).trans_lt hy
  have hs : 0 < r ^ 2 - ‖y‖ ^ 2 := by
    have := (sq_lt_sq₀ (norm_nonneg y) hr.le).2 hy
    linarith
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  set h := (√(r ^ 2 - ‖y‖ ^ 2))⁻¹ with hh
  have hh2 : h ^ 2 * (r ^ 2 - ‖y‖ ^ 2) = 1 := by
    rw [hh, inv_pow, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']
  have h4 : r ^ 2 / (r ^ 2 - ‖y‖ ^ 2) ^ 2 = r ^ 2 * h ^ 4 := by
    rw [hh, show (√(r ^ 2 - ‖y‖ ^ 2))⁻¹ ^ 4 = ((√(r ^ 2 - ‖y‖ ^ 2)) ^ 2)⁻¹ ^ 2 by ring,
      Real.sq_sqrt hs.le]
    field_simp
  -- Each derivative is `h • v + (h ^ 3 * ⟪y, v⟫) • y`, so the determinant picks up
  -- `h ^ 2 * (1 + h ^ 2 * ‖y‖ ^ 2) = r ^ 2 * h ^ 4`.
  simp only [fderiv_univBall_zero_symm_apply hy, ← hh, h4, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    star_trivial]
  rw [hn] at hh2
  linear_combination (-(h ^ 2) * (p 0 * q 1 - p 1 * q 0)) * hh2

end OpenPartialHomeomorph
