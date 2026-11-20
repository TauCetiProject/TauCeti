/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Symplectic.Complex.Line
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The area form of the complex line in polar coordinates

The standard area form `ω(v, w) = Re v Im w - Im v Re w` of `ℂ`
(`TauCeti.stdComplexSymplecticForm`) is `ρ dρ ∧ dφ = d(ρ² / 2) ∧ dφ` in polar coordinates
`z = ρ e^{iφ}`. This file records two forms of this fact.

* **At a point.** At a nonzero `z`, the differential of `|z|² / 2` is `v ↦ ⟪z, v⟫` and that of
  the angle is `v ↦ Im (v / z)`, and `ω(v, w) = ⟪z, v⟫ Im (w / z) - Im (v / z) ⟪z, w⟫`
  (`TauCeti.stdComplexSymplecticForm_apply_eq_polar`).
* **For maps in polar form.** A map `f = e^{iθ} r` from a real normed space, with real-valued
  angle `θ` and radius `r` differentiable at `x`, has differential
  `df_x v = e^{iθ(x)} (dr_x v + i r(x) dθ_x v)`
  (`TauCeti.fderiv_circleExp_mul_ofReal_apply`), and so pulls the area form back to
  `r dr ∧ dθ`: `ω(df_x v, df_x w) = r(x) (dr_x v dθ_x w - dθ_x v dr_x w)`
  (`TauCeti.stdComplexSymplecticForm_fderiv_circleExp_mul_ofReal`). The factor `e^{iθ(x)}` drops
  out because rotations preserve the area form (`TauCeti.stdComplexSymplecticForm_mul_mul`).

These formulas compute the pullback of the area form along maps given by a modulus and an
argument, such as the changes of slice charts of circle quotients.
-/

public section

open Complex
open scoped InnerProductSpace

namespace TauCeti

open scoped InnerProductSpace in
/-- **The area form in polar coordinates.** At a nonzero `z`, the area form is
`d(|z|² / 2) ∧ dφ`: the differential of `|z|² / 2` at `z` is `v ↦ ⟪z, v⟫`, and that of the angle
`φ` is `v ↦ Im (v / z)`, so `ω(v, w) = ⟪z, v⟫ Im (w / z) - Im (v / z) ⟪z, w⟫`. -/
theorem stdComplexSymplecticForm_apply_eq_polar {z : ℂ} (hz : z ≠ 0) (v w : ℂ) :
    stdComplexSymplecticForm v w = ⟪z, v⟫_ℝ * (w / z).im - (v / z).im * ⟪z, w⟫_ℝ := by
  have hz' : Complex.normSq z ≠ 0 := Complex.normSq_eq_zero.not.mpr hz
  simp only [stdComplexSymplecticForm_apply, Complex.inner, Complex.div_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  field_simp
  rw [Complex.normSq_apply]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {θ r : E → ℝ}
  {θ' r' : E →L[ℝ] ℝ} {x : E}

/-- **The differential of a map in polar form.** If the angle `θ` and the radius `r` are
differentiable at `x`, then `f = e^{iθ} r` has differential
`df_x v = e^{iθ(x)} (dr_x v + i r(x) dθ_x v)`. -/
theorem fderiv_circleExp_mul_ofReal_apply (hθ : HasFDerivAt θ θ' x) (hr : HasFDerivAt r r' x)
    (v : E) :
    fderiv ℝ (fun y ↦ (Circle.exp (θ y) : ℂ) * (r y : ℂ)) x v =
      (Circle.exp (θ x) : ℂ) * ((r' v : ℂ) + (r x * θ' v : ℝ) * I) := by
  have h : HasFDerivAt (fun y ↦ (Circle.exp (θ y) : ℂ) * (r y : ℂ)) _ x :=
    (((ofRealCLM.hasFDerivAt.comp x hθ).mul_const' I).cexp.mul
      (ofRealCLM.hasFDerivAt.comp x hr)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simp [Circle.coe_exp])
  rw [h.fderiv]
  simp only [Function.comp_apply, ofRealCLM_apply, op_smul_eq_smul, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, Circle.coe_exp, ofReal_mul]
  ring

/-- **Maps in polar form pull the area form back to `r dr ∧ dθ`.** If the angle `θ` and the radius
`r` are differentiable at `x`, then `f = e^{iθ} r` satisfies
`ω(df_x v, df_x w) = r(x) (dr_x v dθ_x w - dθ_x v dr_x w)`. -/
theorem stdComplexSymplecticForm_fderiv_circleExp_mul_ofReal (hθ : HasFDerivAt θ θ' x)
    (hr : HasFDerivAt r r' x) (v w : E) :
    stdComplexSymplecticForm (fderiv ℝ (fun y ↦ (Circle.exp (θ y) : ℂ) * (r y : ℂ)) x v)
        (fderiv ℝ (fun y ↦ (Circle.exp (θ y) : ℂ) * (r y : ℂ)) x w) =
      r x * (r' v * θ' w - θ' v * r' w) := by
  rw [fderiv_circleExp_mul_ofReal_apply hθ hr, fderiv_circleExp_mul_ofReal_apply hθ hr,
    stdComplexSymplecticForm_mul_mul, Circle.norm_coe, one_pow, one_mul,
    stdComplexSymplecticForm_apply]
  simp only [ofReal_mul, add_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero, I_re, mul_im,
    zero_mul, add_zero, I_im, mul_one, sub_self, add_im, zero_add]
  ring

end TauCeti
