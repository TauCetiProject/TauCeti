/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic identities and norm bounds for `RCLike` fields

## Main results

* `RCLike.re_eq_self_of_im_eq_zero`: a scalar with zero imaginary part equals its real part.
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `RCLike.instSMulPosReflectLE`: scoped under `ComplexOrder`, scalar multiplication on the right by
  a strictly positive element of a `StarOrderedRing` `K`-`StarModule` reflects `≤`, complementing
  `RCLike.instMulPosReflectLE`.
-/

public section

namespace RCLike

variable {K : Type*} [RCLike K]

/-- The norm of a scalar is at most the sum of the absolute values of its real and imaginary
parts. -/
theorem norm_le_abs_re_add_abs_im (z : K) : ‖z‖ ≤ |re z| + |im z| := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_def]
  nlinarith [abs_mul_abs_self (re z), abs_mul_abs_self (im z), abs_nonneg (re z),
    abs_nonneg (im z)]

/-- A scalar with zero imaginary part is the image of its real part. -/
theorem re_eq_self_of_im_eq_zero {z : K} (h : im z = 0) : (re z : K) = z :=
  conj_eq_iff_re.mp (conj_eq_iff_im.mpr h)

section Order

open scoped ComplexOrder

/-- Scoped under `ComplexOrder`, right scalar multiplication by a strictly positive element `b > 0`
of a `StarOrderedRing` `K`-`StarModule` reflects `≤` (`z₁ • b ≤ z₂ • b → z₁ ≤ z₂`), complementing
`RCLike.instMulPosReflectLE`. -/
theorem instSMulPosReflectLE {B : Type*} [NonUnitalRing B] [PartialOrder B] [StarRing B]
    [StarOrderedRing B] [Module K B] [StarModule K B] [IsScalarTower K B B]
    [SMulCommClass K B B] : SMulPosReflectLE K B where
  le_of_smul_le_smul_right {b} hb {z₁ z₂} h := by
    have hb_sa : IsSelfAdjoint b := .of_nonneg hb.le
    have hsub : 0 ≤ (z₂ - z₁) • b := by
      simpa only [sub_smul, sub_nonneg] using h
    have hc_sa : star (z₂ - z₁) = z₂ - z₁ := by
      have hstar : star ((z₂ - z₁) • b) = (z₂ - z₁) • b :=
        (IsSelfAdjoint.of_nonneg hsub).star_eq
      rw [star_smul, hb_sa.star_eq] at hstar
      exact smul_left_injective K hb.ne' hstar
    have him : im (z₂ - z₁) = 0 := conj_eq_iff_im.mp hc_sa
    have hre_eq : (re (z₂ - z₁) : K) = z₂ - z₁ := re_eq_self_of_im_eq_zero him
    rw [← sub_nonneg, nonneg_iff]
    refine ⟨?_, him⟩
    by_contra! hneg
    have hpos : 0 < -((z₂ - z₁) • b) := by
      have hsmul : 0 < ((-re (z₂ - z₁) : ℝ) : K) • b :=
        smul_pos (ofReal_pos.mpr (neg_pos.mpr hneg)) hb
      simpa only [ofReal_neg, neg_smul, hre_eq] using hsmul
    exact not_le_of_gt (neg_pos.mp hpos) hsub

scoped[ComplexOrder] attribute [instance] RCLike.instSMulPosReflectLE

end Order

end RCLike
