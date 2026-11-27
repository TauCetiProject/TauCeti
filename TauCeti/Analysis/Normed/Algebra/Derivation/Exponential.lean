/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Exponentials of operators satisfying a bilinear Leibniz rule

Let `β : E × F → G` be a continuous bilinear map between Banach spaces over `𝕜 = ℝ` or `ℂ`, and
let `D₁`, `D₂`, `D₃` be bounded operators on `E`, `F`, `G` satisfying the Leibniz rule

`D₃ (β x y) = β (D₁ x) y + β x (D₂ y)`.

Then the operator exponentials `exp Dᵢ = ∑ Dᵢⁿ / n!`, computed in the Banach algebras of bounded
operators, satisfy

`exp D₃ (β x y) = β (exp D₁ x) (exp D₂ y)`

(`ContinuousLinearMap.exp_apply_apply_of_leibniz`). Two special cases are used in Tau Ceti.

* For the multiplication of a Banach algebra `B`, not necessarily unital or commutative, and a
  bounded derivation `D` of `B`, `D (x * y) = x * D y + D x * y`, this says that `exp D` is
  multiplicative (`ContinuousLinearMap.exp_apply_mul_of_derivation`). Since `exp D` is invertible
  in the operator algebra, with inverse `exp (-D)` (`NormedSpace.invertibleExp`), it is then an
  automorphism of `B`. Applied to the derivations `t • D`, this makes every `exp (t • D)` an
  automorphism; the Singer–Wermer theorem composes characters with these automorphisms.
* For the bracket of a finite-dimensional real Lie algebra and a derivation `D = ad X`, it says
  that `exp (ad X)` is a Lie algebra automorphism. These are the inner automorphisms
  `exp (s ad X)` of `TauCeti.Algebra.Lie.InvariantForm.Exponential`, which realize the root
  reflections of a compact Lie algebra.

The proof differentiates `t ↦ exp (-t D₃) (β (exp (t D₁) x) (exp (t D₂) y))`, whose derivative
vanishes by the Leibniz rule, so that it is constant.

## Main results

* `ContinuousLinearMap.exp_apply_apply_of_leibniz`: the exponentials of operators satisfying the
  Leibniz rule for a bilinear map are compatible with it.
* `ContinuousLinearMap.forall_exp_smul_apply_bilinear_iff`: preserving a bilinear product along an
  exponential line is equivalent to the Leibniz rule.
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

variable {𝕜 : Type*} [RCLike 𝕜]

section Bilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- **Exponentials of operators satisfying the Leibniz rule for a bilinear map.** If a continuous
bilinear map `β` and bounded operators `D₁`, `D₂`, `D₃` satisfy
`D₃ (β x y) = β (D₁ x) y + β x (D₂ y)`, then `exp D₃ (β x y) = β (exp D₁ x) (exp D₂ y)`. -/
theorem exp_apply_apply_of_leibniz (β : E →L[𝕜] F →L[𝕜] G) {D₁ : E →L[𝕜] E} {D₂ : F →L[𝕜] F}
    {D₃ : G →L[𝕜] G} (hD : ∀ x y, D₃ (β x y) = β (D₁ x) y + β x (D₂ y)) (x : E) (y : F) :
    exp D₃ (β x y) = β (exp D₁ x) (exp D₂ y) := by
  -- The function `K t = exp (-t • D₃) (β (exp (t • D₁) x) (exp (t • D₂) y))` has derivative zero
  -- by the Leibniz rule, so it is constant, equal to its value `β x y` at `t = 0`.
  let K : 𝕜 → G := fun t ↦ exp (t • -D₃) (β (exp (t • D₁) x) (exp (t • D₂) y))
  have hK (t : 𝕜) : HasDerivAt K 0 t := by
    have hm : HasDerivAt (fun s : 𝕜 ↦ β (exp (s • D₁) x) (exp (s • D₂) y))
        (β (exp (t • D₁) x) (exp (t • D₂) (D₂ y)) + β (exp (t • D₁) (D₁ x)) (exp (t • D₂) y)) t :=
      β.hasDerivAt_of_bilinear (fun _ ↦ hasDerivAt_exp_smul_apply D₁ t x)
        (fun _ ↦ hasDerivAt_exp_smul_apply D₂ t y)
    convert (hasDerivAt_exp_smul_const (-D₃) t).clm_apply hm using 1
    -- The derivative is `exp (t • -D₃) (m' - D₃ m)` with
    -- `m = β (exp (t • D₁) x) (exp (t • D₂) y)`; it vanishes by the Leibniz rule once `D₁` and
    -- `D₂` are moved past `exp (t • D₁)` and `exp (t • D₂)`.
    simp only [mul_apply_eq_comp, neg_apply, map_neg, map_add, hD, apply_exp_smul_apply, smul_neg]
    abel
  have hK10 : K 1 = K 0 :=
    is_const_of_deriv_eq_zero (fun t ↦ (hK t).differentiableAt) (fun t ↦ (hK t).deriv) 1 0
  have hinv : exp D₃ * exp (-D₃) = 1 := by
    -- `exp_add_of_commute` is stated for normed `ℚ`-algebras; the operator algebra is one by
    -- restriction of scalars from `𝕜`.
    let _ : NormedAlgebra ℚ (G →L[𝕜] G) := NormedAlgebra.restrictScalars ℚ 𝕜 _
    rw [← exp_add_of_commute (Commute.refl D₃).neg_right, add_neg_cancel, exp_zero]
  simp only [K, one_smul, zero_smul, exp_zero, one_apply_eq_self] at hK10
  rw [← hK10, ← mul_apply_eq_comp, hinv, one_apply_eq_self]

end Bilinear

section BilinearProduct

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [CompleteSpace B]

/-- Preserving a continuous bilinear product along an exponential line is equivalent to the
Leibniz rule for its infinitesimal generator. -/
theorem forall_exp_smul_apply_bilinear_iff (b : B →L[𝕜] B →L[𝕜] B) (D : B →L[𝕜] B) :
    (∀ (t : 𝕜) x y, exp (t • D) (b x y) = b (exp (t • D) x) (exp (t • D) y)) ↔
      ∀ x y, D (b x y) = b x (D y) + b (D x) y := by
  constructor
  · intro h x y
    have he (z : B) : HasDerivAt (fun t : 𝕜 ↦ exp (t • D) z) (D z) 0 := by
      simpa using D.hasDerivAt_exp_smul_apply 0 z
    have hb := b.hasDerivAt_of_bilinear (fun _ ↦ he x) (fun _ ↦ he y)
    have hf : (fun t : 𝕜 ↦ exp (t • D) (b x y)) =
        fun t : 𝕜 ↦ b (exp (t • D) x) (exp (t • D) y) := funext fun t ↦ h t x y
    have ha := he (b x y)
    rw [hf] at ha
    simpa using ha.unique hb
  · intro h t
    refine b.exp_apply_apply_of_leibniz (D₁ := t • D) (D₂ := t • D) (D₃ := t • D) ?_
    intro x y
    simp [h, smul_add, add_comm]

end BilinearProduct

variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [CompleteSpace B]

/-- **The exponential of a bounded derivation is multiplicative.** If a continuous linear map
`D : B → B` on a Banach algebra satisfies `D (x * y) = x * D y + D x * y`, then
`exp D (x * y) = exp D x * exp D y`. -/
theorem exp_apply_mul_of_derivation (D : B →L[𝕜] B) (hD : ∀ x y, D (x * y) = x * D y + D x * y)
    (x y : B) : exp D (x * y) = exp D x * exp D y :=
  (mul 𝕜 B).exp_apply_apply_of_leibniz (fun x y ↦ by simp [hD, add_comm]) x y

end ContinuousLinearMap
