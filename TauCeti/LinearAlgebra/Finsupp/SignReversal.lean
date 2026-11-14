/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Negating the coefficients on a set

For a ring `R` and a set `S` of indices, `Finsupp.signReversal R S` is the `R`-linear involution
of `α →₀ R` that negates the coefficients at the points of `S` and keeps the others. It is the
change of basis between free modules whose basis vectors on `S` have been replaced by their
negatives, for instance between Morse chain modules for orientations differing on `S`.

## Main definitions

* `Finsupp.signReversal R S`: the involution of `α →₀ R` negating the coefficients on `S`.

## Main results

* `Finsupp.signReversal_single`, `Finsupp.signReversal_apply`: its values.
* `Finsupp.signReversal_signReversal`, `Finsupp.signReversal_symm`: it is an involution.
-/

public section

namespace Finsupp

variable {α : Type*} (R : Type*) [Ring R] (S : Set α) [DecidablePred (· ∈ S)]

/-- The **sign reversal** on `S`: the `R`-linear involution of `α →₀ R` negating the coefficients
of the points of `S` and keeping the others. -/
noncomputable def signReversal : (α →₀ R) ≃ₗ[R] (α →₀ R) :=
  LinearEquiv.ofInvolutive
    (linearCombination R fun p ↦ single p (if p ∈ S then -1 else 1)) <| by
      intro c
      induction c using induction_linear with
      | zero => simp
      | add c d hc hd => simp only [map_add] at hc hd ⊢; rw [hc, hd]
      | single p a => by_cases hp : p ∈ S <;> simp [hp]

variable {R S}

/-- The sign reversal negates `single p a` exactly when `p ∈ S`. -/
@[simp]
theorem signReversal_single (p : α) (a : R) :
    signReversal R S (single p a) = single p (if p ∈ S then -a else a) := by
  have h : ⇑(signReversal R S) =
      linearCombination R fun p ↦ single p (if p ∈ S then (-1 : R) else 1) :=
    LinearEquiv.coe_ofInvolutive _ _
  rw [h, linearCombination_single, smul_single, smul_eq_mul]
  split_ifs <;> simp

/-- The coefficient of `q` in the sign reversal of `c` is `-c q` on `S` and `c q` off `S`. -/
@[simp]
theorem signReversal_apply (c : α →₀ R) (q : α) :
    signReversal R S c q = if q ∈ S then -c q else c q := by
  induction c using induction_linear with
  | zero => simp
  | add c d hc hd => by_cases hq : q ∈ S <;> simp_all [add_comm]
  | single p a =>
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p ∈ S <;> simp [hp]
    · by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> simp [hp, hq, single_eq_of_ne' hpq]

/-- The sign reversal is an involution. -/
@[simp]
theorem signReversal_signReversal (c : α →₀ R) :
    signReversal R S (signReversal R S c) = c := by
  ext q
  by_cases hq : q ∈ S <;> simp [hq]

/-- The sign reversal is its own inverse. -/
@[simp]
theorem signReversal_symm : (signReversal R S).symm = signReversal R S :=
  LinearEquiv.ext fun c ↦ (signReversal R S).symm_apply_eq.2 (signReversal_signReversal c).symm

end Finsupp
