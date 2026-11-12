/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.Analysis.Complex.Sqrt

/-!
# Inversion in the eta multiplier

For `γ = (a b; c d)` with `d > 0`, right multiplication by the inversion matrix
`S = (0 -1; 1 0)` multiplies the eta multiplier by `exp(-π i / 4)`.
The positivity condition controls the principal square root: at `τ = i`, the
new automorphy factor `-c + d i` lies in the upper half-plane.
Together with the translation laws, this is the inversion step in the Euclidean
calculation of the multiplier. The case `c = 1` has the explicit value
`exp(π i ((a + d) / 12 - 1/4))`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*,
  Theorems 3.1 and 3.4.
-/

public section

open Complex ModularGroup
open scoped Real UpperHalfPlane MatrixGroups

namespace TauCeti.ModularForm

/-- Right inversion multiplies the eta multiplier by `exp(-π i / 4)` when the
lower-right entry is positive. No sign condition on the lower-left entry is needed. -/
theorem etaMultiplier_mul_S (γ : SL(2, ℤ)) (hd : 0 < γ 1 1) :
    etaMultiplier (γ * S) = cexp (-(π * I / 4)) * etaMultiplier γ := by
  have hentry0 : (γ * S) 1 0 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hentry1 : (γ * S) 1 1 = -γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hpos : 0 < ((γ 1 1 : ℂ) * I - γ 1 0).im := by
    simpa using (Int.cast_pos.mpr hd : (0 : ℝ) < γ 1 1)
  have hroot := Complex.sqrt_neg_I_mul hpos
  have hrotate : -I * ((γ 1 1 : ℂ) * I - γ 1 0) = (γ 1 0 : ℂ) * I + γ 1 1 := by
    ring_nf
    simp
  rw [hrotate, Complex.sqrt_I_eq_exp, ← Complex.exp_neg] at hroot
  refine etaMultiplier_eq_of_eta_smul_eq (τ := UpperHalfPlane.I) ?_
  have hfixed : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    simp
  rw [mul_smul, hfixed, eta_smul, hentry0, hentry1]
  simp only [UpperHalfPlane.coe_I, Int.cast_neg, ← sub_eq_add_neg]
  rw [hroot]
  ring

/-- If the lower-left entry is `1`, the eta multiplier is
`exp(π i ((a + d) / 12 - 1/4))`. This is the initial case of its Dedekind-sum formula. -/
theorem etaMultiplier_of_c_eq_one (γ : SL(2, ℤ)) (hc : γ 1 0 = 1) :
    etaMultiplier γ = cexp (π * I * (((γ 0 0 : ℂ) + γ 1 1) / 12 - 1 / 4)) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_one] at hdet
  have hfactor : γ = T ^ (γ 0 0) * S * T ^ (γ 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_S,
        Matrix.mul_apply, Fin.sum_univ_two, hc]
    omega
  rw [congrArg etaMultiplier hfactor, etaMultiplier_mul_T_zpow,
    etaMultiplier_T_zpow_mul, etaMultiplier_S,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

end TauCeti.ModularForm
