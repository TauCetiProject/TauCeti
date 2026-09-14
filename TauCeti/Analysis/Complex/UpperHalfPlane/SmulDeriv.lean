/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The derivative of the `PSL(2, ℝ)`-action on the upper half-plane

A Möbius transformation of the upper half-plane is holomorphic, with derivative
`det g / denom g z ^ 2` at `z`, where `denom g z = c * z + d` is Mathlib's automorphy factor
(`UpperHalfPlane.hasStrictDerivAt_smul`). A representative in `SL(2, ℝ)` has determinant `1`, so
the derivative is `(denom g z ^ 2)⁻¹`; squaring the automorphy factor cancels the sign ambiguity
of the representative, so this depends only on the class in `PSL(2, ℝ)`. That well-defined
derivative is `TauCeti.UpperHalfPlane.smulDeriv`, the quantity the effective projective action
attaches to a point.

By the chain rule the derivative is a cocycle for the action
(`TauCeti.UpperHalfPlane.smulDeriv_mul`); restricted to the stabilizer of a point it therefore
becomes a character, which is what governs the stabilizers of a discrete subgroup.

## Main declarations

* `TauCeti.UpperHalfPlane.smulDeriv`: the derivative at `z : ℍ` of the Möbius transformation
  attached to `q : PSL(2, ℝ)`.
* `TauCeti.UpperHalfPlane.hasStrictDerivAt_coe_smul` and
  `TauCeti.UpperHalfPlane.deriv_coe_smul`: it is the complex derivative of that transformation,
  read through Mathlib's partial inverse `UpperHalfPlane.ofComplex` of the inclusion `ℍ → ℂ`.
* `TauCeti.UpperHalfPlane.smulDeriv_mul`: the chain rule
  `(q₁ * q₂)' z = q₁' (q₂ • z) * q₂' z`, and `TauCeti.UpperHalfPlane.smulDeriv_inv` for the
  inverse.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 7.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of
  Chicago Press, 1992, §§2.1–2.4.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- The automorphy factor changes sign along with its matrix, so squaring it gives a function of
the class in `PSL(2, ℝ)`. -/
theorem denom_mapGL_neg (g : SL(2, ℝ)) (z : ℂ) :
    denom (mapGL ℝ (-g)) z = -denom (mapGL ℝ g) z := by
  simp [denom]
  ring

/-- The derivative at `z : ℍ` of the Möbius transformation of the upper half-plane attached to
`q : PSL(2, ℝ)`; see `TauCeti.UpperHalfPlane.deriv_coe_smul`. On a representative
`g : SL(2, ℝ)` it is `(denom g z ^ 2)⁻¹`, independent of the representative by
`TauCeti.UpperHalfPlane.denom_mapGL_neg`. -/
def smulDeriv (q : PSL(2, ℝ)) (z : ℍ) : ℂ :=
  Quotient.liftOn' q (fun g : SL(2, ℝ) ↦ (denom (mapGL ℝ g) (z : ℂ) ^ 2)⁻¹) <| by
    rintro a b hab
    rw [QuotientGroup.leftRel_apply, mem_center_iff_eq_one_or_eq_neg_one] at hab
    rcases hab with h | h
    · rw [inv_mul_eq_one] at h
      rw [h]
    · have hb : b = -a := by simpa using congrArg (a * ·) h
      subst hb
      rw [denom_mapGL_neg, neg_sq]

/-- The derivative of the transformation of a representative, in terms of its automorphy
factor. -/
@[simp]
theorem smulDeriv_coe (g : SL(2, ℝ)) (z : ℍ) :
    smulDeriv (g : PSL(2, ℝ)) z = (denom (mapGL ℝ g) (z : ℂ) ^ 2)⁻¹ := (rfl)

/-- A Möbius transformation of `ℍ` has nowhere vanishing derivative. -/
@[simp]
theorem smulDeriv_ne_zero (q : PSL(2, ℝ)) (z : ℍ) : smulDeriv q z ≠ 0 := by
  induction q using QuotientGroup.induction_on with | _ g =>
  simp [denom_ne_zero]

/-- The identity transformation has derivative `1`. -/
@[simp]
theorem smulDeriv_one (z : ℍ) : smulDeriv 1 z = 1 := by
  have h : ((1 : SL(2, ℝ)) : PSL(2, ℝ)) = 1 := map_one (QuotientGroup.mk' _)
  rw [← h, smulDeriv_coe]
  simp

/-- **The chain rule for the `PSL(2, ℝ)`-action**: the derivative is a cocycle. -/
@[simp]
theorem smulDeriv_mul (q₁ q₂ : PSL(2, ℝ)) (z : ℍ) :
    smulDeriv (q₁ * q₂) z = smulDeriv q₁ (q₂ • z) * smulDeriv q₂ z := by
  induction q₁ using QuotientGroup.induction_on with | _ a =>
  induction q₂ using QuotientGroup.induction_on with | _ b =>
  have hmul : ((a : PSL(2, ℝ)) * (b : PSL(2, ℝ))) = ((a * b : SL(2, ℝ)) : PSL(2, ℝ)) :=
    (map_mul (QuotientGroup.mk' _) a b).symm
  have hb : ((b : PSL(2, ℝ)) • z) = (mapGL ℝ b) • z := by
    rw [pslMk_smul]
    rfl
  rw [hmul, smulDeriv_coe, smulDeriv_coe, hb, smulDeriv_coe, map_mul, denom_cocycle_σ,
    σ_eq_refl_of_det_pos (by simp)]
  simp [mul_pow, mul_comm]

/-- The inverse transformation has the inverse derivative at the image point. -/
@[simp]
theorem smulDeriv_inv (q : PSL(2, ℝ)) (z : ℍ) :
    smulDeriv q⁻¹ (q • z) = (smulDeriv q z)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← smulDeriv_mul, inv_mul_cancel, smulDeriv_one]

/-- **`smulDeriv` is the derivative of the Möbius transformation.** The transformation is read
on `ℂ` through Mathlib's partial inverse `UpperHalfPlane.ofComplex` of the inclusion `ℍ → ℂ`,
which is the identity on the upper half-plane and so does not affect the derivative there. -/
theorem hasStrictDerivAt_coe_smul (q : PSL(2, ℝ)) (z : ℍ) :
    HasStrictDerivAt (fun w : ℂ ↦ ((q • ofComplex w : ℍ) : ℂ)) (smulDeriv q z) (z : ℂ) := by
  induction q using QuotientGroup.induction_on with | _ g =>
  have h := UpperHalfPlane.hasStrictDerivAt_smul (g := mapGL ℝ g) (by simp) z
  have hfun : (fun w : ℂ ↦ (((g : PSL(2, ℝ)) • ofComplex w : ℍ) : ℂ)) =
      fun w : ℂ ↦ ((mapGL ℝ g • ofComplex w : ℍ) : ℂ) := by
    funext w
    rw [pslMk_smul]
    rfl
  rw [hfun, smulDeriv_coe]
  simpa [one_div] using h

/-- The derivative of a Möbius transformation of `ℍ`, in the form `deriv`. -/
@[simp]
theorem deriv_coe_smul (q : PSL(2, ℝ)) (z : ℍ) :
    deriv (fun w : ℂ ↦ ((q • ofComplex w : ℍ) : ℂ)) (z : ℂ) = smulDeriv q z :=
  (hasStrictDerivAt_coe_smul q z).hasDerivAt.deriv

end TauCeti.UpperHalfPlane
