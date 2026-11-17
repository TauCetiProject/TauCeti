/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Algebra.Star.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential unitaries and exponentials of idempotents and projections

In a complete normed algebra `A`, every positive power of an idempotent `e` equals `e`, so the power
series of `NormedSpace.exp (a * e)` for any `a` commuting with `e` collapses to
`1 + (NormedSpace.exp a - 1) * e` (`IsIdempotentElem.exp_mul_of_commute`), and in particular
`NormedSpace.exp (z • e) = 1 + (NormedSpace.exp z - 1) • e` (`IsIdempotentElem.exp_smul`). In a
complete normed complex star-algebra, for a star projection `p` this gives
`selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) = 1 + (exp (I * t) - 1) • p`
(`IsStarProjection.coe_expUnitary_smul`), which evaluates at `t = π` to the self-adjoint unitary
`1 - 2 * p` (`IsStarProjection.expUnitary_pi_smul`) and joins `1` to `1 - 2 * p` in `unitary A`
(`IsStarProjection.joined_one_one_sub_two_mul`).

## Main declarations

* `selfAdjoint.star_expUnitary`: `star (expUnitary b) = expUnitary (-b)`.
* `IsIdempotentElem.exp_mul_of_commute`, `IsIdempotentElem.exp`, `IsIdempotentElem.exp_smul`:
  closed forms for exponentials of `a * e`, `e`, and `z • e` for an idempotent `e`.
* `IsStarProjection.coe_expUnitary_smul`, `IsStarProjection.expUnitary_pi_smul`,
  `IsStarProjection.joined_one_one_sub_two_mul`: closed form and path to `1 - 2 * p` in `unitary A`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, 2nd ed.,
  Section 2.5.3.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Chapter 2,
  Lemma 2.1.4 and Proposition 2.2.7.
-/

public section

noncomputable section

namespace selfAdjoint

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The adjoint of `expUnitary` is `expUnitary` of the negative. -/
@[simp]
theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

end selfAdjoint

namespace IsIdempotentElem

section RatBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A] {e : A}

/-- In a complete normed `ℚ`-algebra, if `a` commutes with an idempotent `e`, then
`exp (a * e) = 1 + (exp a - 1) * e`. -/
theorem exp_mul_of_commute (he : IsIdempotentElem e) {a : A} (h : Commute a e) :
    NormedSpace.exp (a * e) = 1 + (NormedSpace.exp a - 1) * e := by
  have ha : HasSum (fun n : ℕ ↦ ((n + 1).factorial⁻¹ : ℚ) • a ^ (n + 1))
      (NormedSpace.exp a - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) a)
  have hseries : HasSum (fun n : ℕ ↦ ((n + 1).factorial⁻¹ : ℚ) • (a * e) ^ (n + 1))
      ((NormedSpace.exp a - 1) * e) :=
    (ha.map (AddMonoidHom.mulRight e) (continuous_mul_const e)).congr_fun fun n ↦ by
      simp [h.mul_pow, he.pow_succ_eq]
  have hfull : HasSum (fun n : ℕ ↦ (n.factorial⁻¹ : ℚ) • (a * e) ^ n)
      (1 + (NormedSpace.exp a - 1) * e) := by
    rw [← hasSum_nat_add_iff' 1]; simpa [add_comm] using hseries
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) (a * e)).unique hfull

/-- In a complete normed `ℚ`-algebra, `exp e = 1 + (exp 1 - 1) * e` for an idempotent `e`. -/
theorem exp (he : IsIdempotentElem e) :
    NormedSpace.exp e = 1 + (NormedSpace.exp (1 : A) - 1) * e := by
  simpa using he.exp_mul_of_commute (Commute.one_left e)

end RatBanachAlgebra

section BanachAlgebra

variable {𝕂 A : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
  [CompleteSpace 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A] {e : A}

/-- In a complete normed algebra over a complete characteristic-zero normed field `𝕂` with
continuous rational scaling (such as `ℝ` or `ℂ`), `exp (z • e) = 1 + (exp z - 1) • e` for any
idempotent `e`. -/
theorem exp_smul (he : IsIdempotentElem e) (z : 𝕂) :
    NormedSpace.exp (z • e) = 1 + (NormedSpace.exp z - 1) • e := by
  have hz : HasSum (fun n : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) * z ^ (n + 1))
      (NormedSpace.exp z - 1) := by
    simpa [smul_eq_mul] using
      (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) z)
  have hseries : HasSum (fun n : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) • (z • e) ^ (n + 1))
      ((NormedSpace.exp z - 1) • e) :=
    (hz.mapL ((ContinuousLinearMap.id 𝕂 𝕂).smulRight e)).congr_fun fun n ↦ by
      simp [smul_pow, he.pow_succ_eq, mul_smul]
  have hfull : HasSum (fun n : ℕ ↦ (n.factorial⁻¹ : 𝕂) • (z • e) ^ n)
      (1 + (NormedSpace.exp z - 1) • e) := by
    rw [← hasSum_nat_add_iff' 1]; simpa [add_comm] using hseries
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) (z • e)).unique hfull

end BanachAlgebra

end IsIdempotentElem

namespace IsStarProjection

section Exponential

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A] {p : A}

/-- The exponential unitary generated by `t • p` for a star projection `p` equals
`1 + (Complex.exp (I * t) - 1) • p`. -/
theorem coe_expUnitary_smul (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  have hsmul : Complex.I • (t • p) = (Complex.I * t) • p := by rw [← Complex.coe_smul, smul_smul]
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul, hsmul,
    hp.isIdempotentElem.exp_smul (Complex.I * t), ← Complex.exp_eq_exp_ℂ]

/-- At `t = π`, `expUnitary (π • ⟨p, _⟩)` for a star projection `p` evaluates to `1 - 2 * p`. -/
theorem coe_expUnitary_pi_smul (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (Real.pi • ⟨p, hp.isSelfAdjoint⟩) : A) = 1 - 2 * p := by
  rw [hp.coe_expUnitary_smul Real.pi, mul_comm Complex.I, Complex.exp_pi_mul_I,
    sub_smul, neg_smul, one_smul, sub_eq_add_neg, ← neg_add, ← two_mul, ← sub_eq_add_neg]

/-- Bundled form of `IsStarProjection.coe_expUnitary_pi_smul` in `unitary A`. -/
theorem expUnitary_pi_smul (hp : IsStarProjection p) :
    selfAdjoint.expUnitary (Real.pi • ⟨p, hp.isSelfAdjoint⟩) =
      ⟨1 - 2 * p, hp.one_sub_two_mul_mem_unitary⟩ :=
  Subtype.ext (coe_expUnitary_pi_smul hp)

/-- For any star projection `p`, the reflection unitary `1 - 2 * p` lies in the path component of
`1` in `unitary A`, joined by `t ↦ expUnitary ((π * t) • ⟨p, _⟩)`. -/
theorem joined_one_one_sub_two_mul (hp : IsStarProjection p) :
    Joined (1 : unitary A) ⟨1 - 2 * p, hp.one_sub_two_mul_mem_unitary⟩ :=
  ⟨{ toFun := fun t ↦ selfAdjoint.expUnitary (((Real.pi * (t : ℝ)) : ℝ) • ⟨p, hp.isSelfAdjoint⟩)
     continuous_toFun := selfAdjoint.continuous_expUnitary.comp (by fun_prop)
     source' := by simp
     target' := by simpa using expUnitary_pi_smul hp }⟩

end Exponential

end IsStarProjection
