/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponentiating the Leibniz rule

Let `B` be a Banach space over `ℝ` or `ℂ` with a continuous bilinear product. A bounded
operator satisfies the Leibniz rule for this product exactly when its entire exponential line
preserves the product. This applies to multiplication in Banach algebras and to Lie brackets.

## Main results

* `ContinuousLinearMap.forall_exp_smul_apply_bilinear_iff`: preservation along the exponential
  line is equivalent to the Leibniz rule.
* `ContinuousLinearMap.exp_apply_mul_of_derivation`: the exponential of a bounded derivation is
  multiplicative.

## References

* I. M. Singer and J. Wermer, *Derivations on commutative normed algebras*, Math. Ann. 129
  (1955), 260–264.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.7, for exponentials of bounded
  derivations.
-/

public section

open NormedSpace

namespace ContinuousLinearMap

section Bilinear

variable {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B] [NormedSpace 𝕜 B] [CompleteSpace B]

/-- The exponential of an operator satisfying the Leibniz rule for a continuous bilinear
product preserves that product. -/
theorem exp_apply_bilinear_of_leibniz (b : B →L[𝕜] B →L[𝕜] B) (D : B →L[𝕜] B)
    (hD : ∀ x y, D (b x y) = b x (D y) + b (D x) y) (x y : B) :
    exp D (b x y) = b (exp D x) (exp D y) := by
  have hE (t : 𝕜) (z : B) : HasDerivAt (fun s : 𝕜 ↦ exp (s • D) z) (exp (t • D) (D z)) t := by
    simpa [mul_apply_eq_comp] using
      (hasDerivAt_exp_smul_const D t).clm_apply (hasDerivAt_const t z)
  -- `D` commutes with each `exp (t • D)`.
  have hcomm (t : 𝕜) (z : B) : D (exp (t • D) z) = exp (t • D) (D z) := by
    simpa [mul_apply_eq_comp] using
      congr($(((Commute.refl D).smul_right t).exp_right) z)
  -- Pull the evolving product back along the inverse flow. The Leibniz rule makes it constant.
  let G : 𝕜 → B := fun t ↦ exp (t • -D) (b (exp (t • D) x) (exp (t • D) y))
  have hG (t : 𝕜) : HasDerivAt G 0 t := by
    have hm : HasDerivAt (fun s : 𝕜 ↦ b (exp (s • D) x) (exp (s • D) y))
        (b (exp (t • D) x) (exp (t • D) (D y)) +
          b (exp (t • D) (D x)) (exp (t • D) y)) t :=
      b.hasDerivAt_of_bilinear (fun _ ↦ hE t x) (fun _ ↦ hE t y)
    convert (hasDerivAt_exp_smul_const (-D) t).clm_apply hm using 1
    simp [mul_apply_eq_comp, hD, hcomm]
  have hG10 : G 1 = G 0 :=
    is_const_of_deriv_eq_zero (fun t ↦ (hG t).differentiableAt) (fun t ↦ (hG t).deriv) 1 0
  have hinv : exp D * exp (-D) = 1 := by
    -- `exp_add_of_commute` is stated for normed `ℚ`-algebras; the operator algebra is one by
    -- restriction of scalars from `𝕜`.
    let _ : NormedAlgebra ℚ (B →L[𝕜] B) := NormedAlgebra.restrictScalars ℚ 𝕜 _
    rw [← exp_add_of_commute (Commute.refl D).neg_right, add_neg_cancel, exp_zero]
  simp only [G, one_smul, zero_smul, exp_zero, one_apply_eq_self] at hG10
  rw [← hG10, ← mul_apply_eq_comp, hinv, one_apply_eq_self]

/-- Preserving a continuous bilinear product along an exponential line is equivalent to the
Leibniz rule for its infinitesimal generator. -/
theorem forall_exp_smul_apply_bilinear_iff (b : B →L[𝕜] B →L[𝕜] B) (D : B →L[𝕜] B) :
    (∀ (t : 𝕜) x y, exp (t • D) (b x y) = b (exp (t • D) x) (exp (t • D) y)) ↔
      ∀ x y, D (b x y) = b x (D y) + b (D x) y := by
  constructor
  · intro h x y
    have he (z : B) : HasDerivAt (fun t : 𝕜 ↦ exp (t • D) z) (D z) 0 := by
      simpa [mul_apply_eq_comp] using
        (hasDerivAt_exp_smul_const D 0).clm_apply (hasDerivAt_const (0 : 𝕜) z)
    have hb := b.hasDerivAt_of_bilinear (fun _ ↦ he x) (fun _ ↦ he y)
    have hf : (fun t : 𝕜 ↦ exp (t • D) (b x y)) =
        fun t : 𝕜 ↦ b (exp (t • D) x) (exp (t • D) y) := funext fun t ↦ h t x y
    have ha := he (b x y)
    rw [hf] at ha
    simpa using ha.unique hb
  · intro h t
    apply b.exp_apply_bilinear_of_leibniz (t • D)
    intro x y
    simp [h, smul_add]

end Bilinear

variable {𝕜 B : Type*} [RCLike 𝕜] [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [CompleteSpace B]

/-- The exponential of a bounded derivation of a Banach algebra preserves multiplication. -/
theorem exp_apply_mul_of_derivation (D : B →L[𝕜] B) (hD : ∀ x y, D (x * y) = x * D y + D x * y)
    (x y : B) : exp D (x * y) = exp D x * exp D y :=
  (mul 𝕜 B).exp_apply_bilinear_of_leibniz D hD x y

end ContinuousLinearMap
