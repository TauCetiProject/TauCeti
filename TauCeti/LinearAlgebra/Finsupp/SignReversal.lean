/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Int.Order.Units

/-!
# Changing the signs of coefficients

For an `R`-module `A` and a sign `ε p ∈ ℤˣ` at each index `p`, `Finsupp.signEquiv R ε` is the
`R`-linear involution of `α →₀ A` multiplying the coefficient at each `p` by `ε p`. For `A = R` it
is the change of basis between free modules whose basis vectors have been multiplied by signs, for
instance between Morse chain modules for different orientations, or the gauge automorphism of a
grid chain complex.

The special case `Finsupp.signReversal R S` negates the coefficients at the points of a set `S`
and keeps the others.

## Main definitions

* `Finsupp.signEquiv R ε`: the involution of `α →₀ A` multiplying the coefficient at `p` by `ε p`.
* `Finsupp.signReversal R S`: the involution of `α →₀ A` negating the coefficients on `S`.

## Main results

* `Finsupp.signEquiv_single`, `Finsupp.signEquiv_apply`: the values of `signEquiv`.
* `Finsupp.signEquiv_signEquiv`, `Finsupp.signEquiv_symm`: it is an involution.
* `Finsupp.signReversal_single`, `Finsupp.signReversal_apply`,
  `Finsupp.signReversal_signReversal`, `Finsupp.signReversal_symm`: the same for `signReversal`.
-/

public section

namespace Finsupp

variable {α : Type*} (R : Type*) {A : Type*} [Semiring R] [AddCommGroup A] [Module R A]

section SignEquiv

variable (ε : α → ℤˣ)

/-- The **sign change** by `ε : α → ℤˣ`: the `R`-linear involution of `α →₀ A` multiplying the
coefficient of each `p` by the sign `ε p`. -/
noncomputable def signEquiv : (α →₀ A) ≃ₗ[R] (α →₀ A) :=
  LinearEquiv.ofInvolutive (lsum ℕ fun p ↦ (ε p : ℤ) • lsingle p) <| by
    intro c
    induction c using induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add] at hc hd ⊢; rw [hc, hd]
    | single p a =>
      simp only [lsum_single, LinearMap.smul_apply, lsingle_apply, smul_single, smul_smul,
        ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

variable {R ε}

/-- The sign change multiplies `single p a` by the sign `ε p`. -/
@[simp]
theorem signEquiv_single (p : α) (a : A) :
    signEquiv R ε (single p a) = single p ((ε p : ℤ) • a) := by
  have h : ⇑(signEquiv R ε) = lsum ℕ fun p ↦ (ε p : ℤ) • (lsingle p : A →ₗ[R] α →₀ A) :=
    LinearEquiv.coe_ofInvolutive _ _
  rw [h, lsum_single, LinearMap.smul_apply, lsingle_apply, smul_single]

/-- The coefficient of `q` in the sign change of `c` is `ε q • c q`. -/
@[simp]
theorem signEquiv_apply (c : α →₀ A) (q : α) : signEquiv R ε c q = (ε q : ℤ) • c q := by
  induction c using induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, add_apply, add_apply, hc, hd, smul_add]
  | single p a =>
    rw [signEquiv_single]
    rcases eq_or_ne p q with rfl | hpq
    · simp
    · rw [single_eq_of_ne' hpq, single_eq_of_ne' hpq, smul_zero]

/-- The sign change is an involution. -/
@[simp]
theorem signEquiv_signEquiv (c : α →₀ A) : signEquiv R ε (signEquiv R ε c) = c := by
  ext q
  rw [signEquiv_apply, signEquiv_apply, smul_smul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, one_smul]

/-- The sign change is its own inverse. -/
@[simp]
theorem signEquiv_symm : (signEquiv (A := A) R ε).symm = signEquiv R ε :=
  LinearEquiv.ext fun c ↦ (signEquiv R ε).symm_apply_eq.2 (signEquiv_signEquiv c).symm

end SignEquiv

section SignReversal

variable (S : Set α) [DecidablePred (· ∈ S)]

/-- The **sign reversal** on `S`: the `R`-linear involution of `α →₀ A` negating the coefficients
of the points of `S` and keeping the others. -/
noncomputable def signReversal : (α →₀ A) ≃ₗ[R] (α →₀ A) :=
  signEquiv R fun p ↦ if p ∈ S then -1 else 1

variable {R S}

/-- The sign reversal negates `single p a` exactly when `p ∈ S`. -/
@[simp]
theorem signReversal_single (p : α) (a : A) :
    signReversal R S (single p a) = single p (if p ∈ S then -a else a) := by
  rw [signReversal, signEquiv_single]
  split_ifs <;> simp

/-- The coefficient of `q` in the sign reversal of `c` is `-c q` on `S` and `c q` off `S`. -/
@[simp]
theorem signReversal_apply (c : α →₀ A) (q : α) :
    signReversal R S c q = if q ∈ S then -c q else c q := by
  rw [signReversal, signEquiv_apply]
  split_ifs <;> simp

/-- The sign reversal is an involution. -/
@[simp]
theorem signReversal_signReversal (c : α →₀ A) :
    signReversal R S (signReversal R S c) = c :=
  signEquiv_signEquiv c

/-- The sign reversal is its own inverse. -/
@[simp]
theorem signReversal_symm : (signReversal (A := A) R S).symm = signReversal R S :=
  signEquiv_symm

end SignReversal

end Finsupp
