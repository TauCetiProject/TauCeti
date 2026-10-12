/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.TristramLevine.Basic
public import Mathlib.Analysis.Complex.Circle

/-!
# Alexander roots and the Tristram--Levine form

At a unit-circle parameter different from `1`, the Tristram--Levine form is nonsingular
exactly when the Alexander polynomial does not vanish. This identifies the exceptional
parameters in the signature obstruction to sliceness and in concordance invariance.
The assertions here concern a chosen real Seifert matrix; assigning such a matrix to a
geometric knot is a separate construction.

For a matrix of size `2 * g`, the determinant is
`(-‖ω - 1‖²)^g * Δ(ω)`, with the Conway normalization of `alexander`.
The general-size formula and nonsingularity criterion also apply to odd-sized matrices.
In size zero the determinant is `1`, including at `ω = 1`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 8,
  Definition 8.8 and Theorem 8.19 (the signature obstruction away from Alexander roots).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory*
  (2005), for signature invariants and their exceptional parameters.
-/

public section

open Matrix LaurentPolynomial
open scoped ComplexConjugate

namespace TauCeti.KnotTheory

variable {ι : Type*}

/-- On the unit circle the Tristram--Levine form is a scalar multiple of the
Alexander matrix evaluated at the same parameter. -/
theorem tristramLevineForm_eq_smul_alexanderMatrix (V : Matrix ι ι ℝ) (ω : Circle) :
    tristramLevineForm V ω = (conj (ω : ℂ) - 1) •
      (alexanderMatrix V).map (eval₂ Complex.ofRealHom (Circle.toUnits ω)) := by
  have hω : conj (ω : ℂ) * (ω : ℂ) = 1 := by
    simpa using (RCLike.conj_mul (ω : ℂ))
  rw [map_eval₂_alexanderMatrix]
  ext i j
  simp only [tristramLevineForm_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.map_apply, Matrix.transpose_apply, smul_eq_mul, Circle.toUnits_apply,
    Units.val_mk0]
  linear_combination -(V i j : ℂ) * hω

variable [Fintype ι] [DecidableEq ι]

/-- The determinant formula for arbitrary finite size: the normalization contributes
`ω^(card ι / 2)` and the scalar multiple contributes `(conj ω - 1)^(card ι)`. -/
theorem det_tristramLevineForm (V : Matrix ι ι ℝ) (ω : Circle) :
    (tristramLevineForm V ω).det =
      (conj (ω : ℂ) - 1) ^ Fintype.card ι * (ω : ℂ) ^ (Fintype.card ι / 2) *
        eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) := by
  rw [tristramLevineForm_eq_smul_alexanderMatrix, Matrix.det_smul]
  have heval := eval₂_alexander Complex.ofRealHom (Circle.toUnits ω) V
  have hcancel : (ω : ℂ) ^ (Fintype.card ι / 2) *
      ((Circle.toUnits ω) ^ (-((Fintype.card ι / 2 : ℕ) : ℤ))).val = 1 := by
    simp only [_root_.zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Circle.toUnits_apply, Units.val_mk0]
    exact mul_inv_cancel₀ (pow_ne_zero _ ω.coe_ne_zero)
  rw [heval, mul_assoc, ← mul_assoc ((ω : ℂ) ^ _), hcancel, one_mul]
  rw [map_eval₂_alexanderMatrix]

/-- In even size the determinant factor is real and has sign `(-1)^g`:
`det H(ω) = (-‖ω - 1‖²)^g * Δ(ω)`. -/
theorem det_tristramLevineForm_of_card {g : ℕ} (V : Matrix ι ι ℝ)
    (hcard : Fintype.card ι = 2 * g) (ω : Circle) :
    (tristramLevineForm V ω).det =
      ((-(‖(ω : ℂ) - 1‖ ^ 2) : ℝ) : ℂ) ^ g *
        eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) := by
  have hω : conj (ω : ℂ) * (ω : ℂ) = 1 := by
    simpa using (RCLike.conj_mul (ω : ℂ))
  have hfactor : (conj (ω : ℂ) - 1) ^ 2 * (ω : ℂ) =
      ((-(‖(ω : ℂ) - 1‖ ^ 2) : ℝ) : ℂ) := by
    rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one ω.norm_coe]
    have hre : (ω : ℂ) + conj (ω : ℂ) = (2 * (ω : ℂ).re : ℝ) :=
      Complex.add_conj _
    push_cast at hre ⊢
    linear_combination (conj (ω : ℂ) - 2) * hω + hre
  rw [det_tristramLevineForm, hcard]
  simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), pow_mul,
    ← mul_pow, hfactor]

/-- Away from `1`, the Tristram--Levine form is nonsingular exactly away from roots
of the Alexander polynomial. No even-size or unimodularity assumption is needed. -/
@[simp]
theorem det_tristramLevineForm_ne_zero_iff (V : Matrix ι ι ℝ) (ω : Circle)
    (hω : ω ≠ 1) :
    (tristramLevineForm V ω).det ≠ 0 ↔
      eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) ≠ 0 := by
  have hcoe : (ω : ℂ) ≠ 1 := by
    intro h
    exact hω (Subtype.ext h)
  have hconj : conj (ω : ℂ) - 1 ≠ 0 := by
    intro h
    apply hcoe
    simpa using congrArg (starRingEnd ℂ) (sub_eq_zero.mp h)
  rw [det_tristramLevineForm]
  simp [hconj, ω.coe_ne_zero]

/-- The nonsingularity criterion for integral Seifert matrices, evaluating the integer
Alexander polynomial directly rather than its real-coefficient image. -/
theorem det_tristramLevineForm_int_ne_zero_iff (V : Matrix ι ι ℤ) (ω : Circle)
    (hω : ω ≠ 1) :
    (tristramLevineForm (V.map (Int.castRingHom ℝ)) ω).det ≠ 0 ↔
      eval₂ (Int.castRingHom ℂ) (Circle.toUnits ω) (alexander V) ≠ 0 := by
  have hcast : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  rw [det_tristramLevineForm_ne_zero_iff _ ω hω, eval₂_alexander_map, hcast]

/-- The figure-eight Alexander polynomial has positive real value everywhere on the
unit circle: `Δ(ω) = 3 - 2 * re ω ≥ 1`. In particular it has no unit-circle roots. -/
theorem one_le_re_eval₂_alexander_figureEightSeifertMatrix (ω : Circle) :
    1 ≤ (eval₂ (Int.castRingHom ℂ) (Circle.toUnits ω)
      (alexander figureEightSeifertMatrix)).re := by
  rw [alexander_figureEightSeifertMatrix]
  have hre : (ω : ℂ).re ≤ 1 := by
    simpa using Complex.re_le_norm (ω : ℂ)
  simp only [map_sub, map_add, map_neg, eval₂_T, map_ofNat, zpow_one, _root_.zpow_neg_one,
    Circle.toUnits_apply, Units.val_mk0, Units.val_inv_eq_inv_val]
  rw [Complex.inv_eq_conj ω.norm_coe]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.re_ofNat,
    Complex.conj_re]
  linarith

/-- Every unit-circle parameter other than `1` gives a nonsingular Tristram--Levine
form for the figure-eight Seifert matrix. -/
theorem det_tristramLevineForm_figureEightSeifertMatrix_ne_zero (ω : Circle)
    (hω : ω ≠ 1) :
    (tristramLevineForm (figureEightSeifertMatrix.map (Int.castRingHom ℝ)) ω).det ≠ 0 := by
  rw [det_tristramLevineForm_int_ne_zero_iff _ ω hω]
  intro h
  have hre := one_le_re_eval₂_alexander_figureEightSeifertMatrix ω
  rw [h, Complex.zero_re] at hre
  norm_num at hre

/-- For the trefoil, the exceptional parameters other than `1` are exactly the two
unit-circle points with real part `1 / 2`, the roots of `t - 1 + t⁻¹`. -/
theorem det_tristramLevineForm_trefoilSeifertMatrix_ne_zero_iff (ω : Circle)
    (hω : ω ≠ 1) :
    (tristramLevineForm (trefoilSeifertMatrix.map (Int.castRingHom ℝ)) ω).det ≠ 0 ↔
      (ω : ℂ).re ≠ 1 / 2 := by
  rw [det_tristramLevineForm_int_ne_zero_iff _ ω hω, alexander_trefoilSeifertMatrix]
  have heval : eval₂ (Int.castRingHom ℂ) (Circle.toUnits ω)
      (T 1 - 1 + T (-1)) = ((2 * (ω : ℂ).re - 1 : ℝ) : ℂ) := by
    simp only [map_add, map_sub, map_one, eval₂_T, zpow_one, _root_.zpow_neg_one,
      Circle.toUnits_apply, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [Complex.inv_eq_conj ω.norm_coe]
    push_cast
    have hre := Complex.add_conj (ω : ℂ)
    push_cast at hre
    linear_combination hre
  rw [heval, ne_eq, Complex.ofReal_eq_zero]
  constructor <;> contrapose! <;> intro h <;> linarith

end TauCeti.KnotTheory
