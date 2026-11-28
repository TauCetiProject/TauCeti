/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.ContravariantForm
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower.Bounds
import TauCeti.Analysis.Matrix.DeterminantBound.L2OpNorm
import TauCeti.Analysis.Matrix.EntrywiseOpNorm.Uniform

/-!
# Squared-length bounds for Weyl module actions

The action on a polynomial Weyl module inherits the operator bound on the ambient tensor power.
A change of frame and an independent determinant factor can therefore be bounded using only
the entries of their matrices. The resulting bound depends on the number of boxes of the shape,
not on the dimension of the Weyl module.

The determinant-scaled estimate is the local size calculation used by
`New.weylNormSq_det_smul_weylRep_mulVec_weylEval_le` in lsernau/grh-lean, revision `72fead1`,
`grh/src/New/UpperBound/Size/ShortColumns.lean`. Here the tensor-power realization gives a bound
for arbitrary input vectors measured by the contravariant form.
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The squared-length bound for the polynomial Weyl action in the contravariant form. -/
theorem re_weylForm_weylRepOfShape_apply_self_le (μ : YoungDiagram) (g : GL (Fin n) 𝕜)
    (x : (weylModuleOfShape 𝕜 n μ).toSubmodule) :
    let y := weylRepOfShape 𝕜 n μ g x
    RCLike.re (weylForm n μ y y) ≤ ‖(g : Matrix (Fin n) (Fin n) 𝕜)‖ ^ (2 * μ.card) *
      RCLike.re (weylForm n μ x x) := by
  dsimp only
  simpa only [weylForm_apply, weylRepOfShape_apply_coe, Representation.tensorPower_apply,
    stdRep_apply] using re_tensorPowerForm_map_apply_self_le (g : Matrix (Fin n) (Fin n) 𝕜) x.val

/-- Scaling an input by `a` multiplies its squared length by `‖a‖²`. -/
theorem re_weylForm_smul_apply_self (μ : YoungDiagram) (a : 𝕜)
    (x : (weylModuleOfShape 𝕜 n μ).toSubmodule) :
    RCLike.re (weylForm n μ (a • x) (a • x)) = ‖a‖ ^ 2 * RCLike.re (weylForm n μ x x) := by
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
  simp only [starRingEnd_apply, smul_eq_mul]
  rw [← mul_assoc, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

/-- Let `g` and `Y` have entries of norm at most `R`, and let `h` have entries of norm at most
one. Acting by `g * h` and multiplying by `det Y` increases squared length by at most
`R^(4*n + 6*|μ|)`, where `R ≥ n` and `|μ|` counts the boxes of the polynomial shape. -/
theorem re_weylForm_det_smul_weylRepOfShape_mul_apply_self_le (μ : YoungDiagram)
    (g h : GL (Fin n) 𝕜) (Y : Matrix (Fin n) (Fin n) 𝕜)
    (x : (weylModuleOfShape 𝕜 n μ).toSubmodule) {R : ℝ} (hnR : (n : ℝ) ≤ R)
    (hg : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) 𝕜) i j‖ ≤ R)
    (hh : ∀ i j, ‖(h : Matrix (Fin n) (Fin n) 𝕜) i j‖ ≤ 1) (hY : ∀ i j, ‖Y i j‖ ≤ R) :
    let y := Y.det • weylRepOfShape 𝕜 n μ (g * h) x
    RCLike.re (weylForm n μ y y) ≤ R ^ (4 * n + 6 * μ.card) *
      RCLike.re (weylForm n μ x x) := by
  dsimp only
  have hR : 0 ≤ R := (Nat.cast_nonneg n).trans hnR
  have hnorm (A : Matrix (Fin n) (Fin n) 𝕜) (hA : ∀ i j, ‖A i j‖ ≤ R) : ‖A‖ ≤ R ^ 2 := by
    simpa only [Fintype.card_fin, sq] using
      (A.l2_opNorm_le_card_mul_of_norm_apply_le hA).trans
        (mul_le_mul_of_nonneg_right (by simpa only [Fintype.card_fin] using hnR) hR)
  have hh_op : ‖(h : Matrix (Fin n) (Fin n) 𝕜)‖ ≤ R :=
    (by simpa only [Fintype.card_fin, mul_one] using l2_opNorm_le_card_mul_of_norm_apply_le _ hh :
      ‖(h : Matrix (Fin n) (Fin n) 𝕜)‖ ≤ n).trans hnR
  have hgh : ‖(g * h : GL (Fin n) 𝕜).val‖ ≤ R ^ 3 := calc
    _ ≤ ‖g.val‖ * ‖h.val‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ R ^ 2 * R := by gcongr; exact hnorm _ hg
    _ = R ^ 3 := by ring
  have hd : ‖Y.det‖ ≤ (R ^ 2) ^ n := by
    refine (Y.norm_det_le_l2_opNorm_pow.trans_eq (by rw [Fintype.card_fin])).trans ?_
    gcongr
    exact hnorm Y hY
  have hx : 0 ≤ RCLike.re (weylForm n μ x x) := by
    rw [weylForm_apply, re_tensorPowerForm_apply_self]
    positivity
  rw [re_weylForm_smul_apply_self]
  calc
    _ ≤ ‖Y.det‖ ^ 2 * (‖(g * h : GL (Fin n) 𝕜).val‖ ^ (2 * μ.card) *
        RCLike.re (weylForm n μ x x)) :=
      mul_le_mul_of_nonneg_left (re_weylForm_weylRepOfShape_apply_self_le μ (g * h) x)
        (sq_nonneg _)
    _ ≤ ((R ^ 2) ^ n) ^ 2 * ((R ^ 3) ^ (2 * μ.card) * RCLike.re (weylForm n μ x x)) := by
      gcongr
    _ = _ := by rw [← mul_assoc, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]; congr 2; omega

end TauCeti
