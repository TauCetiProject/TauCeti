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
* `Finsupp.signEquiv_signEquiv`, `Finsupp.signEquiv_symm`, `Finsupp.signEquiv_trans_self`: it is
  an involution.
* `Finsupp.signEquiv_one`, `Finsupp.signEquiv_trans`: the trivial signs give the identity, and
  composing sign changes multiplies the signs.
* `Finsupp.support_signEquiv`: the sign change keeps the support.
* `LinearMap.comp_signEquiv_eq_smul`: a linear map supported on the indices of one sign `u` is
  multiplied by `u` under the sign change.
* `Finsupp.signReversal_single`, `Finsupp.signReversal_apply`,
  `Finsupp.signReversal_signReversal`, `Finsupp.signReversal_symm`,
  `Finsupp.signReversal_trans_self`, `Finsupp.signReversal_empty`,
  `Finsupp.support_signReversal`: the same for `signReversal`.
* `Finsupp.signReversal_congr`, `Finsupp.signReversal_eq_refl`: the sign reversal depends only on
  the points of the set, and is the identity on a set without points.
* `Finsupp.signReversal_trans_signReversal`: sign reversals compose by symmetric difference of
  their sets.
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

/-- The sign change composed with itself is the identity. -/
@[simp]
theorem signEquiv_trans_self :
    (signEquiv (A := A) R ε).trans (signEquiv R ε) = LinearEquiv.refl R (α →₀ A) :=
  LinearEquiv.ext signEquiv_signEquiv

/-- Composing the sign changes by `ε` and by `η` is the sign change by `ε * η`. -/
theorem signEquiv_trans (η : α → ℤˣ) :
    (signEquiv (A := A) R ε).trans (signEquiv R η) = signEquiv R (ε * η) :=
  LinearEquiv.ext fun c ↦ ext fun q ↦ by
    rw [LinearEquiv.trans_apply, signEquiv_apply, signEquiv_apply, signEquiv_apply, Pi.mul_apply,
      mul_comm, Units.val_mul, mul_smul]

/-- The sign change keeps the support. -/
@[simp]
theorem support_signEquiv (c : α →₀ A) : (signEquiv R ε c).support = c.support := by
  ext q
  rw [mem_support_iff, mem_support_iff, signEquiv_apply]
  rcases Int.units_eq_one_or (ε q) with h | h <;> simp [h]

/-- **A linear map supported on one sign.** If an `R`-linear map `a` on `α →₀ A` vanishes on the
coefficients at every `q` whose sign `ε q` is not `u`, then composing `a` with the sign change by
`ε` multiplies it by `u`. For the Koszul sign `ε q = (-1) ^ |q|` of a graded basis, a linear form
of degree `k` is multiplied by `(-1) ^ k`. -/
theorem _root_.LinearMap.comp_signEquiv_eq_smul {N : Type*} [AddCommGroup N] [Module R N]
    (a : (α →₀ A) →ₗ[R] N) {u : ℤˣ} (ha : ∀ q, ε q ≠ u → ∀ c, a (single q c) = 0) :
    a ∘ₗ (signEquiv R ε).toLinearMap = (u : ℤ) • a := by
  refine lhom_ext fun q c ↦ ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, signEquiv_single, LinearMap.smul_apply]
  by_cases hq : ε q = u
  · rw [hq, ← smul_single, map_zsmul]
  · rw [ha q hq, ha q hq, smul_zero]

variable (R) in
/-- The sign change by the trivial signs is the identity. -/
@[simp]
theorem signEquiv_one : signEquiv R (1 : α → ℤˣ) = LinearEquiv.refl R (α →₀ A) :=
  LinearEquiv.ext fun c ↦ ext fun q ↦ by simp

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

/-- The sign reversal composed with itself is the identity. -/
@[simp]
theorem signReversal_trans_self :
    (signReversal (A := A) R S).trans (signReversal R S) = LinearEquiv.refl R (α →₀ A) :=
  signEquiv_trans_self

/-- The sign reversal keeps the support. -/
@[simp]
theorem support_signReversal (c : α →₀ A) : (signReversal R S c).support = c.support :=
  support_signEquiv c

/-- The sign reversal depends only on the points of the set: sign reversals on sets with the same
points agree, whatever their decidability instances. -/
theorem signReversal_congr {T : Set α} [DecidablePred (· ∈ T)] (h : ∀ p, p ∈ S ↔ p ∈ T) :
    signReversal (A := A) R S = signReversal R T :=
  LinearEquiv.ext fun c ↦ ext fun q ↦ by simp [h]

/-- The sign reversal on a set without points is the identity. -/
theorem signReversal_eq_refl (h : ∀ p, p ∉ S) :
    signReversal R S = LinearEquiv.refl R (α →₀ A) :=
  LinearEquiv.ext fun c ↦ ext fun q ↦ by simp [h]

/-- **Sign reversals compose by symmetric difference**: the sign reversal on `S` followed by that
on `T` is the sign reversal on a set `U` whose points are those lying in exactly one of `S` and
`T`. -/
theorem signReversal_trans_signReversal {T U : Set α} [DecidablePred (· ∈ T)]
    [DecidablePred (· ∈ U)] (h : ∀ p, p ∈ U ↔ Xor (p ∈ S) (p ∈ T)) :
    (signReversal (A := A) R S).trans (signReversal R T) = signReversal R U :=
  LinearEquiv.ext fun c ↦ ext fun q ↦ by
    rw [LinearEquiv.trans_apply, signReversal_apply, signReversal_apply, signReversal_apply]
    by_cases hS : q ∈ S <;> by_cases hT : q ∈ T <;> simp [hS, hT, h]

variable (R) in
/-- The sign reversal on the empty set is the identity. -/
@[simp]
theorem signReversal_empty [DecidablePred (· ∈ (∅ : Set α))] :
    signReversal R (∅ : Set α) = LinearEquiv.refl R (α →₀ A) :=
  signReversal_eq_refl Set.notMem_empty

end SignReversal

end Finsupp
