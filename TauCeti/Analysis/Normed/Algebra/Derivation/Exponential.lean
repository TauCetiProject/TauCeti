/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of a bounded derivation is multiplicative

Let `B` be a Banach algebra over `𝕜 = ℝ` or `ℂ`, not necessarily unital or commutative, and let
`D : B → B` be a bounded derivation, meaning a continuous linear map satisfying the Leibniz rule
`D (x * y) = x * D y + D x * y`. Then the operator exponential `exp D = ∑ Dⁿ / n!`, computed in
the Banach algebra of bounded operators on `B`, is multiplicative:

`exp D (x * y) = exp D x * exp D y`.

Since `exp D` is invertible in the operator algebra, with inverse `exp (-D)`
(`NormedSpace.invertibleExp`), it is then an automorphism of `B`. Applied to the derivations
`t • D`, this makes every `exp (t • D)` an automorphism; the Singer–Wermer theorem composes
characters with these automorphisms.

The identity is proved by differentiating in the parameter: for fixed `x` and `y` the function
`t ↦ exp (-t • D) (exp (t • D) x * exp (t • D) y)` has derivative zero by the Leibniz rule, so it
is constant, equal to its value `x * y` at `t = 0`.

## Main results

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

variable {𝕜 B : Type*} [RCLike 𝕜] [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [CompleteSpace B]

/-- **The exponential of a bounded derivation is multiplicative.** If a continuous linear map
`D : B → B` on a Banach algebra satisfies `D (x * y) = x * D y + D x * y`, then
`exp D (x * y) = exp D x * exp D y`. -/
theorem exp_apply_mul_of_derivation (D : B →L[𝕜] B) (hD : ∀ x y, D (x * y) = x * D y + D x * y)
    (x y : B) : exp D (x * y) = exp D x * exp D y := by
  have hE (t : 𝕜) (z : B) : HasDerivAt (fun s : 𝕜 ↦ exp (s • D) z) (exp (t • D) (D z)) t := by
    simpa [mul_apply_eq_comp] using
      (hasDerivAt_exp_smul_const D t).clm_apply (hasDerivAt_const t z)
  -- `D` commutes with each `exp (t • D)`.
  have hcomm (t : 𝕜) (z : B) : D (exp (t • D) z) = exp (t • D) (D z) := by
    simpa [mul_apply_eq_comp] using
      congr($(((Commute.refl D).smul_right t).exp_right) z)
  -- The function `G t = exp (-t • D) (exp (t • D) x * exp (t • D) y)` has derivative zero.
  let G : 𝕜 → B := fun t ↦ exp (t • -D) (exp (t • D) x * exp (t • D) y)
  have hG (t : 𝕜) : HasDerivAt G 0 t := by
    have hm : HasDerivAt (fun s : 𝕜 ↦ exp (s • D) x * exp (s • D) y)
        (exp (t • D) x * exp (t • D) (D y) + exp (t • D) (D x) * exp (t • D) y) t :=
      (mul 𝕜 B).hasDerivAt_of_bilinear (fun _ ↦ hE t x) (fun _ ↦ hE t y)
    convert (hasDerivAt_exp_smul_const (-D) t).clm_apply hm using 1
    -- The derivative is `exp (t • -D) (m' - D m)` with `m = exp (t • D) x * exp (t • D) y`; it
    -- vanishes by the Leibniz rule once `D` is moved past `exp (t • D)`.
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

end ContinuousLinearMap
