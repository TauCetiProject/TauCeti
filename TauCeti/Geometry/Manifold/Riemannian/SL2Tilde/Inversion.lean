/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# A nonlinear isometry of the Sasaki model `SL₂ℝ~`

Lift the upper-half-plane isometry `w ↦ -1/w` to the universal-cover Sasaki
model. In horocyclic coordinates its fibre correction is `2 arctan(x / exp y)`.
This correction preserves the connection form `dz + exp(-y) dx`; together with
the affine lifts it supplies the nonlinear generator for the hyperbolic base action.

The chosen lift fixes the fibre over `i` pointwise and is an involution. It differs
by a constant fibre translation from the lift obtained by lifting the derivative's
angle. Thus no order-two assertion about a lift in the universal covering group of
`PSL₂ℝ` is intended.

Reference: P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15
(1983), Section 4, the unit-tangent-bundle description of `SL₂ℝ~`.
The metric and isometry construction follow `SL2Tilde.translate`; the global
coordinate-diffeomorphism API follows `Sol.toProdDiffeomorph`.
-/

public section

noncomputable section

open Real Manifold Bundle
open scoped ContDiff Manifold

namespace TauCeti.SL2Tilde

private def denominator (r : ℝ × ℝ × ℝ) : ℝ := r.1 ^ 2 + (exp r.2.1) ^ 2

private theorem denominator_pos (r : ℝ × ℝ × ℝ) : 0 < denominator r :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (exp_pos _))

private def inversionCoordinates (r : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-r.1 / denominator r, r.2.1 - log (denominator r),
    r.2.2 + 2 * arctan (r.1 / exp r.2.1))

private theorem exp_inversionCoordinates (r : ℝ × ℝ × ℝ) :
    exp (inversionCoordinates r).2.1 = exp r.2.1 / denominator r := by
  simp only [inversionCoordinates, exp_sub, exp_log (denominator_pos r)]

private theorem denominator_inversionCoordinates (r : ℝ × ℝ × ℝ) :
    denominator (inversionCoordinates r) = (denominator r)⁻¹ := by
  rw [denominator, exp_inversionCoordinates]
  simp only [inversionCoordinates]
  have hd := (denominator_pos r).ne'
  dsimp only [denominator] at *
  field_simp

private theorem inversionCoordinates_involutive : Function.Involutive inversionCoordinates := by
  intro r
  have hd := (denominator_pos r).ne'
  have ht : (inversionCoordinates r).1 / exp (inversionCoordinates r).2.1 =
      -(r.1 / exp r.2.1) := by
    rw [exp_inversionCoordinates]
    simp only [inversionCoordinates]
    field_simp
  have hD := denominator_inversionCoordinates r
  simp only [inversionCoordinates] at hD ht ⊢
  rw [hD, ht, arctan_neg, log_inv]
  apply Prod.ext
  · simp [hd]
  · apply Prod.ext <;> ring

private theorem contDiff_inversionCoordinates : ContDiff ℝ ∞ inversionCoordinates := by
  have hd : ContDiff ℝ ∞ denominator := by
    unfold denominator
    fun_prop
  unfold inversionCoordinates
  exact (contDiff_fst.neg.div hd fun r => (denominator_pos r).ne').prodMk
    ((contDiff_snd.fst.sub (hd.log fun r => (denominator_pos r).ne')).prodMk
      (contDiff_snd.snd.add (contDiff_const.mul
        (contDiff_fst.div contDiff_snd.fst.exp fun r => exp_ne_zero r.2.1).arctan)))

private def xL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := .fst ℝ ℝ (ℝ × ℝ)
private def yL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
private def zL : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private def inversionDerivative (r : ℝ × ℝ × ℝ) :
    (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  ((denominator r ^ 2)⁻¹ •
    ((r.1 ^ 2 - (exp r.2.1) ^ 2) • xL + (2 * r.1 * (exp r.2.1) ^ 2) • yL)).prod
  ((denominator r)⁻¹ • ((-2 * r.1) • xL + (r.1 ^ 2 - (exp r.2.1) ^ 2) • yL) |>.prod
    (zL + (2 * exp r.2.1 / denominator r) • (xL - r.1 • yL)))

private theorem hasFDerivAt_inversionCoordinates (r : ℝ × ℝ × ℝ) :
    HasFDerivAt inversionCoordinates (inversionDerivative r) r := by
  have hx := xL.hasFDerivAt (x := r)
  have hy := yL.hasFDerivAt (x := r)
  have hz := zL.hasFDerivAt (x := r)
  have hd := (hx.pow 2).add (hy.exp.pow 2)
  have hd0 := (denominator_pos r).ne'
  have he0 := exp_ne_zero r.2.1
  have ha0 : 1 + (r.1 / exp r.2.1) ^ 2 ≠ 0 := by positivity
  have hdi := (hasDerivAt_inv hd0).comp_hasFDerivAt r hd
  have hei := (hasDerivAt_inv he0).comp_hasFDerivAt r hy.exp
  convert (hx.neg.mul hdi).prodMk
    ((hy.sub (hd.log hd0)).prodMk (hz.add ((hx.mul hei).arctan.const_mul 2))) using 1
  · funext v
    simp [div_eq_mul_inv, inversionCoordinates, denominator, xL, yL, zL]
  · ext <;>
      simp [inversionDerivative, xL, yL, zL, denominator, smul_eq_mul] <;>
      field_simp <;> ring

private def inversionFun : SL2Tilde → SL2Tilde :=
  toProd.symm ∘ inversionCoordinates ∘ toProd

private theorem inversionFun_involutive : Function.Involutive inversionFun := by
  intro p
  apply toProd.injective
  simpa only [inversionFun, Function.comp_apply, Equiv.apply_symm_apply] using
    inversionCoordinates_involutive (toProd p)

private theorem contMDiff_inversionFun :
    ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ inversionFun := by
  unfold inversionFun
  simpa only [coe_toProdDiffeomorph, coe_toProdDiffeomorph_symm,
    Function.comp_def] using toProdDiffeomorph.symm.contMDiff.comp
      (contDiff_inversionCoordinates.contMDiff.comp toProdDiffeomorph.contMDiff)

private theorem tangentSpaceCastModel_mfderiv_inversionFun (p : SL2Tilde)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (inversionFun p)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) inversionFun p v) =
    inversionDerivative (toProd p) (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v) := by
  have hc := contDiff_inversionCoordinates.differentiable (by simp) |>.mdifferentiable
  have hp : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) toProd := by
    simpa only [coe_toProdDiffeomorph] using toProdDiffeomorph.mdifferentiable (by simp)
  have hi : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) toProd.symm := by
    simpa only [coe_toProdDiffeomorph_symm] using
      toProdDiffeomorph.symm.mdifferentiable (by simp)
  unfold inversionFun
  rw [mfderiv_comp p (hi _) (hc.comp hp p)]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply,
    tangentSpaceCastModel_mfderiv_toProd_symm]
  rw [mfderiv_comp p (hc _) (hp _),
    (hasFDerivAt_inversionCoordinates (toProd p)).hasMFDerivAt.mfderiv]
  exact congrArg (inversionDerivative (toProd p)) (mfderiv_toProd_apply p v)

private theorem inner_mfderiv_inversionFun (p : SL2Tilde)
    (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) inversionFun p v)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) inversionFun p w) = inner ℝ v w := by
  have hd := (denominator_pos (toProd p)).ne'
  have he := exp_ne_zero p.y
  have h1 : exp (-(inversionFun p).y) = denominator (toProd p) / exp p.y := by
    rw [exp_neg]
    have h := exp_inversionCoordinates (toProd p)
    simpa only [inversionFun, Function.comp_apply, y_toProd_symm, fst_snd_toProd, inv_div]
      using congrArg Inv.inv h
  have h2 : exp (-2 * (inversionFun p).y) =
      (denominator (toProd p) / exp p.y) ^ 2 := by
    rw [show -2 * (inversionFun p).y = -(inversionFun p).y + -(inversionFun p).y by ring,
      exp_add, h1, pow_two]
  have h0 : exp (-2 * p.y) = (exp p.y)⁻¹ ^ 2 := by
    rw [show -2 * p.y = -p.y + -p.y by ring, exp_add, exp_neg, pow_two]
  rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_inversionFun,
    tangentSpaceCastModel_mfderiv_inversionFun, h1, h2, h0, exp_neg]
  simp only [inversionDerivative, denominator, fst_toProd, fst_snd_toProd, xL, yL, zL,
    ContinuousLinearMap.prod_apply, add_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hd0 : p.x ^ 2 + exp p.y ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The lift of `w ↦ -1/w` fixing the fibre over `i` pointwise. In coordinates,
`D = x² + exp(2y)`, it sends `(x,y,z)` to
`(-x/D, y-log D, z+2 arctan(x/exp y))`. -/
def inversion : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) SL2Tilde where
  toFun := inversionFun
  invFun := inversionFun
  left_inv := inversionFun_involutive
  right_inv := inversionFun_involutive
  contMDiff_toFun := contMDiff_inversionFun
  contMDiff_invFun := contMDiff_inversionFun
  inner_mfderiv' := inner_mfderiv_inversionFun

/-- The horizontal coordinate of the lifted inversion. -/
@[simp] theorem x_inversion (p : SL2Tilde) :
    (inversion p).x = -p.x / (p.x ^ 2 + (exp p.y) ^ 2) := by
  -- The isometry literal's coercion is its specified forward function.
  change (inversionFun p).x = _
  simp [inversionFun, inversionCoordinates, denominator]

/-- The logarithmic height of the lifted inversion. -/
@[simp] theorem y_inversion (p : SL2Tilde) :
    (inversion p).y = p.y - log (p.x ^ 2 + (exp p.y) ^ 2) := by
  -- The isometry literal's coercion is its specified forward function.
  change (inversionFun p).y = _
  simp [inversionFun, inversionCoordinates, denominator]

/-- The angle correction in the lifted inversion. -/
@[simp] theorem z_inversion (p : SL2Tilde) :
    (inversion p).z = p.z + 2 * arctan (p.x / exp p.y) := by
  -- The isometry literal's coercion is its specified forward function.
  change (inversionFun p).z = _
  simp [inversionFun, inversionCoordinates]

/-- The differential of the lifted inversion, read in the global model coordinates. -/
theorem tangentSpaceCastModel_mfderiv_inversion (p : SL2Tilde)
    (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
    let D := p.x ^ 2 + (exp p.y) ^ 2
    let u := tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v
    tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (inversion p)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) inversion p v) =
      (((p.x ^ 2 - (exp p.y) ^ 2) * u.1 + 2 * p.x * (exp p.y) ^ 2 * u.2.1) / D ^ 2,
        (-2 * p.x * u.1 + (p.x ^ 2 - (exp p.y) ^ 2) * u.2.1) / D,
        u.2.2 + 2 * exp p.y / D * (u.1 - p.x * u.2.1)) := by
  dsimp only
  -- Give the isometry literal its specified function before applying the coordinate bridge.
  change tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (inversionFun p)
    (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) inversionFun p v) = _
  rw [tangentSpaceCastModel_mfderiv_inversionFun]
  simp [inversionDerivative, denominator, xL, yL, zL, div_eq_mul_inv, mul_comm, mul_add]

/-- Applying the chosen lift twice recovers the original point. -/
@[simp] theorem inversion_inversion (p : SL2Tilde) : inversion (inversion p) = p :=
  inversionFun_involutive p

/-- The lifted inversion is its own inverse. -/
@[simp] theorem inversion_inv : inversion⁻¹ = inversion := by
  apply inv_eq_of_mul_eq_one_left
  apply RiemannianIsometry.ext
  intro p
  simpa only [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply] using
    inversion_inversion p

/-- The lifted inversion commutes with translations along the fibres. -/
theorem inversion_mul_translate_fibre (c : ℝ) :
    inversion * translate 0 0 c = translate 0 0 c * inversion := by
  apply RiemannianIsometry.ext
  intro p
  ext <;> simp [RiemannianIsometry.mul_apply]
  ring

/-- The fibre over `i` is fixed pointwise by the chosen lift. -/
@[simp] theorem inversion_mk_zero_zero (c : ℝ) : inversion (mk 0 0 c) = mk 0 0 c := by
  ext <;> simp

end TauCeti.SL2Tilde
