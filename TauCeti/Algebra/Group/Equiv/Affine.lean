/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Abel

/-!
# Iterates of affine automorphisms of additive groups

An additive automorphism followed by translation acts on any additive commutative group,
in particular on the additive group of a complex torus. The translation part of its `k`-th
power is the partial cyclic norm. This file computes every power, distinguishes periodicity
from exact order, and characterizes fixed points by the image of `1 - A^k`.

The partial norm and difference maps are defined for arbitrary additive endomorphisms.
All results allow torsion. In particular, no division is used for involutions.

The norm and difference convention is the one in Brown, *Cohomology of Groups*,
Chapter VI, Section 2. Powers of additive maps are written using function iteration.
-/

public section

namespace TauCeti.CyclicAffine

variable {T : Type*}

section Norm

variable [AddCommMonoid T]

/-- The partial cyclic norm `1 + A + ⋯ + A^(k-1)`, including the empty sum at `k = 0`. -/
def cyclicNormHom (A : T →+ T) (k : ℕ) : T →+ T where
  toFun t := ∑ i ∈ Finset.range k, A^[i] t
  map_zero' := by simp [iterate_map_zero]
  map_add' x y := by simp [iterate_map_add, Finset.sum_add_distrib]

/-- Evaluation of the partial cyclic norm as an ordered sum of powers. -/
theorem cyclicNormHom_apply (A : T →+ T) (k : ℕ) (t : T) :
    cyclicNormHom A k t = ∑ i ∈ Finset.range k, A^[i] t :=
  (rfl)

@[simp]
theorem cyclicNormHom_zero (A : T →+ T) : cyclicNormHom A 0 = 0 := by
  ext t
  simp [cyclicNormHom_apply]

@[simp]
theorem cyclicNormHom_one (A : T →+ T) : cyclicNormHom A 1 = AddMonoidHom.id T := by
  ext t
  simp [cyclicNormHom_apply]

/-- Extending a partial norm by its last summand. -/
theorem cyclicNormHom_succ_apply (A : T →+ T) (k : ℕ) (t : T) :
    cyclicNormHom A (k + 1) t = cyclicNormHom A k t + A^[k] t :=
  Finset.sum_range_succ _ _

/-- The period-two norm, with no assumption on `A` or on torsion in `T`. -/
@[simp]
theorem cyclicNormHom_two (A : T →+ T) :
    cyclicNormHom A 2 = AddMonoidHom.id T + A := by
  ext t
  simp [cyclicNormHom_succ_apply]

end Norm

variable [AddCommGroup T]

/-- The difference map whose image detects fixed points of an affine power. -/
def oneSubPow (A : T →+ T) (k : ℕ) : T →+ T :=
  AddMonoidHom.id T - AddMonoidHom.mk' A^[k] (iterate_map_add A k)

@[simp]
theorem oneSubPow_apply (A : T →+ T) (k : ℕ) (t : T) :
    oneSubPow A k t = t - A^[k] t :=
  (rfl)

@[simp]
theorem oneSubPow_zero (A : T →+ T) : oneSubPow A 0 = 0 := by
  ext t
  simp

/-- The first difference map is `1 - A`. -/
@[simp]
theorem oneSubPow_one (A : T →+ T) : oneSubPow A 1 = AddMonoidHom.id T - A := by
  ext t
  simp

/-- An affine permutation with linear part `A` and translation part `t`. -/
def affineEquiv (A : T ≃+ T) (t : T) : Equiv.Perm T :=
  A.toEquiv.trans (Equiv.addRight t)

@[simp]
theorem affineEquiv_apply (A : T ≃+ T) (t x : T) : affineEquiv A t x = A x + t :=
  (rfl)

@[simp]
theorem affineEquiv_symm_apply (A : T ≃+ T) (t x : T) :
    (affineEquiv A t).symm x = A.symm (x - t) := by
  simp [affineEquiv, sub_eq_add_neg]

/-- Every affine power has translation part equal to its partial cyclic norm. -/
theorem affineEquiv_pow_apply (A : T ≃+ T) (t : T) (k : ℕ) (x : T) :
    (affineEquiv A t ^ k) x = A^[k] x + cyclicNormHom A.toAddMonoidHom k t := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, affineEquiv_apply, iterate_map_add,
      cyclicNormHom_succ_apply]
    simp only [AddEquiv.coe_toAddMonoidHom, Function.iterate_succ_apply]
    abel

/-- An affine power is the identity exactly when both its linear and translation parts are. -/
theorem affineEquiv_pow_eq_one_iff (A : T ≃+ T) (t : T) (k : ℕ) :
    affineEquiv A t ^ k = 1 ↔
      A^[k] = id ∧ cyclicNormHom A.toAddMonoidHom k t = 0 := by
  constructor
  · intro h
    have ht := congrArg (fun e : Equiv.Perm T ↦ e 0) h
    simp only [affineEquiv_pow_apply, iterate_map_zero, zero_add, Equiv.Perm.one_apply] at ht
    refine ⟨?_, ht⟩
    funext x
    have hx := congrArg (fun e : Equiv.Perm T ↦ e x) h
    simpa only [affineEquiv_pow_apply, ht, add_zero, Equiv.Perm.one_apply, id_eq] using hx
  · rintro ⟨hA, ht⟩
    ext x
    simp only [affineEquiv_pow_apply, hA, ht, id_eq, add_zero, Equiv.Perm.one_apply]

/-- If the linear part is `m`-periodic, the affine map is `m`-periodic exactly when its norm
vanishes. This asserts order dividing `m`, not exact order. -/
theorem affineEquiv_pow_eq_one_iff_of_pow_eq_one (A : T ≃+ T) (t : T) (m : ℕ)
    (hA : A^[m] = id) :
    affineEquiv A t ^ m = 1 ↔ cyclicNormHom A.toAddMonoidHom m t = 0 := by
  simp [affineEquiv_pow_eq_one_iff, hA]

/-- Exact order requires excluding every smaller positive affine power. -/
theorem orderOf_affineEquiv_eq_iff (A : T ≃+ T) (t : T) {m : ℕ} (hm : 0 < m) :
    orderOf (affineEquiv A t) = m ↔
      (A^[m] = id ∧ cyclicNormHom A.toAddMonoidHom m t = 0) ∧
      ∀ k, 0 < k → k < m →
        A^[k] ≠ id ∨ cyclicNormHom A.toAddMonoidHom k t ≠ 0 := by
  rw [orderOf_eq_iff hm]
  simp only [Ne, affineEquiv_pow_eq_one_iff, not_and_or]
  exact and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_comm

/-- The fixed-point equation for each affine power, with the displayed positive difference sign. -/
theorem affineEquiv_pow_apply_eq_self_iff (A : T ≃+ T) (t : T) (k : ℕ) (x : T) :
    (affineEquiv A t ^ k) x = x ↔
      oneSubPow A.toAddMonoidHom k x = cyclicNormHom A.toAddMonoidHom k t := by
  rw [affineEquiv_pow_apply, oneSubPow_apply]
  simp only [AddEquiv.coe_toAddMonoidHom]
  rw [sub_eq_iff_eq_add']
  exact eq_comm

/-- An affine power has a fixed point exactly when its partial norm is in the image of the
corresponding difference map. This applies to every power, including composite periods. -/
theorem exists_affineEquiv_pow_fixedPoint_iff (A : T ≃+ T) (t : T) (k : ℕ) :
    (∃ x, (affineEquiv A t ^ k) x = x) ↔
      cyclicNormHom A.toAddMonoidHom k t ∈ (oneSubPow A.toAddMonoidHom k).range := by
  simp only [AddMonoidHom.mem_range, affineEquiv_pow_apply_eq_self_iff]

/-- Exclusion of fixed points for all nonidentity powers in a specified period range.
Periodicity is separate: this equivalence itself does not assume it. -/
theorem affineEquiv_pow_fixedPoint_free_iff (A : T ≃+ T) (t : T) (m : ℕ) :
    (∀ k, 0 < k → k < m → ∀ x, (affineEquiv A t ^ k) x ≠ x) ↔
      ∀ k, 0 < k → k < m →
        cyclicNormHom A.toAddMonoidHom k t ∉ (oneSubPow A.toAddMonoidHom k).range := by
  simp only [← exists_affineEquiv_pow_fixedPoint_iff, not_exists]

/-- Conjugating by the translation `x ↦ x + b` changes the twist by `(1 - A)b`. -/
theorem translation_conj_affineEquiv (A : T ≃+ T) (t b : T) :
    Equiv.addRight b * affineEquiv A t * (Equiv.addRight b)⁻¹ =
      affineEquiv A (t + oneSubPow A.toAddMonoidHom 1 b) := by
  ext x
  simp [Equiv.Perm.mul_apply, affineEquiv_apply, map_add, map_neg, sub_eq_add_neg]
  abel

end TauCeti.CyclicAffine
