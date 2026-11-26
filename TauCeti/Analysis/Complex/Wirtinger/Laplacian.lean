/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The conjugate Wirtinger derivative and the Laplacian

For a real `C²` function `φ` on the plane, the complex function `ψ = ∂ₛφ - i ∂ₜφ`, which is
`2 ∂φ`, satisfies `bar∂ ψ = Δφ / 2`. This is the identity `Δ = 4 ∂ bar∂` for real functions,
in the form used to pass from the weak equation `bar∂ u = h` to a weak Laplace equation for
`Re u`.

For a holomorphic factor `J` the product rule takes the form `Δ (J H) = J ΔH + 4 J' bar∂H`, since
`J` is harmonic and its partial derivatives are `J'` and `i J'`.

## Main results

* `TauCeti.conjWirtingerDeriv_fderiv_sub_I_mul_fderiv_apply_one`: `bar∂ (∂ₛφ - i ∂ₜφ) = Δφ / 2`.
* `TauCeti.laplacian_fun_mul_eq_mul_laplacian_add_deriv_mul_conjWirtingerDeriv`: the product rule
  `Δ (J H) = J ΔH + 4 J' bar∂H` for a holomorphic factor `J`.
-/

public section

open Complex InnerProductSpace
open scoped Laplacian

namespace TauCeti

/-- `ψ = ∂ₛφ - i ∂ₜφ`, which is `2 ∂φ`, has `bar∂ ψ = Δφ / 2` at `w` for a real function `φ`
that is `C²` at `w`. -/
theorem conjWirtingerDeriv_fderiv_sub_I_mul_fderiv_apply_one {φ : ℂ → ℝ} {w : ℂ}
    (hφ : ContDiffAt ℝ 2 φ w) :
    conjWirtingerDeriv (fun z ↦ (fderiv ℝ φ z 1 : ℂ) - I * (fderiv ℝ φ z I : ℂ)) w 1 =
      (2 : ℂ)⁻¹ * (Δ φ w : ℂ) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hline (v : ℂ) : HasFDerivAt (fun z ↦ ((fderiv ℝ φ z v : ℝ) : ℂ))
      (ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ φ) w))) w :=
    ofRealCLM.hasFDerivAt.comp w
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp w hd.hasFDerivAt)
  have hψ : HasFDerivAt (fun z ↦ (fderiv ℝ φ z 1 : ℂ) - I * (fderiv ℝ φ z I : ℂ)) _ w :=
    (hline 1).sub ((hline I).const_mul I)
  have hsymm := hφ.isSymmSndFDerivAt (by simp) I 1
  rw [conjWirtingerDeriv_apply, hψ.fderiv, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, sub_apply, smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.apply_apply, ofRealCLM_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, ofReal_add]
  rw [hsymm]
  linear_combination (-(2 : ℂ)⁻¹ * (fderiv ℝ (fderiv ℝ φ) w I I : ℂ)) * I_sq

/-- **The Laplacian of a product with a holomorphic factor.** If `J` is holomorphic (complex `C²`)
at `z` and `H` is real `C²` at `z`, then `Δ (J H) z = J z ΔH z + 4 J' z bar∂H z`, where
`bar∂H z = (∂ₓH z + i ∂ᵧH z) / 2` is the conjugate Wirtinger derivative. -/
theorem laplacian_fun_mul_eq_mul_laplacian_add_deriv_mul_conjWirtingerDeriv {J H : ℂ → ℂ} {z : ℂ}
    (hJ : ContDiffAt ℂ 2 J z) (hH : ContDiffAt ℝ 2 H z) :
    Δ (fun w ↦ J w * H w) z = J z * Δ H z + 4 * deriv J z * conjWirtingerDeriv H z 1 := by
  have hd (v : ℂ) : fderiv ℝ J z v = v * deriv J z :=
    (hJ.differentiableAt (by norm_num)).fderiv_restrictScalars_eq_smul_deriv ℝ v
  have h := fderiv_apply_one_add_I_smul_fderiv_apply_I H z
  rw [smul_eq_mul, smul_eq_mul] at h
  rw [(hJ.restrict_scalars ℝ).laplacian_fun_mul_complex hH, hJ.harmonicAt.2.self_of_nhds, hd, hd,
    Pi.zero_apply]
  linear_combination (2 * deriv J z) * h

end TauCeti
