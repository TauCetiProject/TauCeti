/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel

/-!
# Iterates of affine automorphisms of additive groups

An additive automorphism followed by translation acts on any additive commutative group,
in particular on the additive group of a complex torus. The translation part of its `k`-th
power is the partial cyclic norm. This file computes every power, distinguishes periodicity
from exact order, and characterizes fixed points by the image of `1 - A^k`.

The partial norm and difference maps use sums and powers in `AddMonoid.End`.
All results allow torsion. In particular, no division is used for involutions.
The period-two zero composites are instances of
`TauCeti.one_sub_mul_one_add_of_sq_eq_one` and
`TauCeti.one_add_mul_one_sub_of_sq_eq_one` in
`TauCeti.LinearAlgebra.End.OrderTwoThree`, since endomorphism multiplication is composition.

The public API is in `TauCeti.CyclicAffine`. With `open TauCeti.CyclicAffine`, use
`affinePerm A t` for the permutation and `toEnd A` for its linear endomorphism.
Theorems likewise take explicit arguments, as in `affinePerm_pow_apply A t k x`.

The norm and difference convention is the one in Brown, *Cohomology of Groups*,
Chapter VI, Section 2. Periodicity is expressed using powers in `AddMonoid.End`;
the iterate formula also uses function iteration.
-/

public section

namespace TauCeti.CyclicAffine

variable {T : Type*}

/-- View an additive automorphism as an element of the endomorphism monoid, so that its
powers and geometric sums use composition and pointwise addition. -/
-- The explicit result type is needed at this pin: `A.toAddMonoidHom` has type `T →+ T`,
-- which has no composition-power instance, even with an `AddMonoid.End T` type ascription.
def toEnd [AddZeroClass T] (A : T ≃+ T) : AddMonoid.End T :=
  A.toAddMonoidHom

@[simp]
theorem coe_toEnd [AddZeroClass T] (A : T ≃+ T) : ⇑(toEnd A) = A := by rfl

@[simp]
theorem toEnd_refl [AddZeroClass T] : toEnd (AddEquiv.refl T) = 1 := (rfl)

@[simp]
theorem toEnd_trans [AddZeroClass T] (A B : T ≃+ T) :
    toEnd (A.trans B) = toEnd B * toEnd A := (rfl)

variable [AddCommGroup T]

/-- An affine permutation with linear part `A` and translation part `t`. -/
def affinePerm (A : T ≃+ T) (t : T) : Equiv.Perm T :=
  A.toEquiv.trans (Equiv.addRight t)

@[simp]
theorem affinePerm_apply (A : T ≃+ T) (t x : T) : affinePerm A t x = A x + t :=
  (rfl)

/-- An affine permutation uniquely determines its linear and translation parts. -/
@[simp]
theorem affinePerm_inj (A B : T ≃+ T) (t s : T) :
    affinePerm A t = affinePerm B s ↔ A = B ∧ t = s := by
  constructor
  · intro h
    have ht : t = s := by
      simpa using congrArg (fun e : Equiv.Perm T ↦ e 0) h
    refine ⟨?_, ht⟩
    ext x
    have hx := congrArg (fun e : Equiv.Perm T ↦ e x) h
    simpa only [affinePerm_apply, ht, add_left_inj] using hx
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem affinePerm_symm_apply (A : T ≃+ T) (t x : T) :
    (affinePerm A t).symm x = A.symm (x - t) := by
  simp [affinePerm, sub_eq_add_neg]

/-- Composing affine permutations composes their linear parts and transports the twist. -/
@[simp]
theorem affinePerm_mul (B A : T ≃+ T) (s t : T) :
    affinePerm B s * affinePerm A t = affinePerm (A.trans B) (B t + s) := by
  ext x
  simp [Equiv.Perm.mul_apply, map_add, add_assoc]

@[simp]
theorem affinePerm_refl (b : T) :
    affinePerm (AddEquiv.refl T) b = Equiv.addRight b := by
  ext x
  rfl

/-- Every affine power has translation part equal to its partial cyclic norm. -/
theorem affinePerm_pow_apply (A : T ≃+ T) (t : T) (k : ℕ) (x : T) :
    (affinePerm A t ^ k) x = A^[k] x + (∑ i ∈ Finset.range k, (toEnd A) ^ i) t := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have add_apply (f g : AddMonoid.End T) (y : T) : (f + g) y = f y + g y := by rfl
    simp [pow_succ, ih, iterate_map_add, Finset.sum_range_succ,
      Function.iterate_succ_apply, add_apply]
    abel

/-- An affine power is the identity exactly when both its linear and translation parts are. -/
theorem affinePerm_pow_eq_one_iff (A : T ≃+ T) (t : T) (k : ℕ) :
    affinePerm A t ^ k = 1 ↔
      (toEnd A) ^ k = 1 ∧ (∑ i ∈ Finset.range k, (toEnd A) ^ i) t = 0 := by
  constructor
  · intro h
    have ht := congrArg (fun e : Equiv.Perm T ↦ e 0) h
    simp only [affinePerm_pow_apply, iterate_map_zero, zero_add, Equiv.Perm.one_apply] at ht
    refine ⟨?_, ht⟩
    ext x
    have hx := congrArg (fun e : Equiv.Perm T ↦ e x) h
    simpa only [affinePerm_pow_apply, ht, add_zero, Equiv.Perm.one_apply,
      AddMonoid.End.coe_pow, coe_toEnd, AddMonoid.End.one_apply] using hx
  · rintro ⟨hA, ht⟩
    ext x
    have hx := DFunLike.congr_fun hA x
    have hx' : A^[k] x = x := by
      simpa only [AddMonoid.End.coe_pow, coe_toEnd, AddMonoid.End.one_apply] using hx
    simpa only [ht, add_zero, hx', Equiv.Perm.one_apply] using affinePerm_pow_apply A t k x

/-- If the linear part is `m`-periodic, the affine map is `m`-periodic exactly when its norm
vanishes. This asserts order dividing `m`, not exact order. -/
theorem affinePerm_pow_eq_one_iff_of_pow_eq_one (A : T ≃+ T) (t : T) (m : ℕ)
    (hA : (toEnd A) ^ m = 1) :
    affinePerm A t ^ m = 1 ↔ (∑ i ∈ Finset.range m, (toEnd A) ^ i) t = 0 := by
  simp [affinePerm_pow_eq_one_iff, hA]

/-- Exact order requires excluding every smaller positive affine power. -/
theorem orderOf_affinePerm_eq_iff (A : T ≃+ T) (t : T) {m : ℕ} (hm : 0 < m) :
    orderOf (affinePerm A t) = m ↔
      ((toEnd A) ^ m = 1 ∧ (∑ i ∈ Finset.range m, (toEnd A) ^ i) t = 0) ∧
      ∀ k, 0 < k → k < m →
        (toEnd A) ^ k ≠ 1 ∨ (∑ i ∈ Finset.range k, (toEnd A) ^ i) t ≠ 0 := by
  rw [orderOf_eq_iff hm]
  simp only [Ne, affinePerm_pow_eq_one_iff, not_and_or]
  exact and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_comm

/-- `x` is fixed by the `k`-th affine power iff `x - A^k x = N_k t`. -/
theorem affinePerm_pow_apply_eq_self_iff (A : T ≃+ T) (t : T) (k : ℕ) (x : T) :
    (affinePerm A t ^ k) x = x ↔
      (1 - (toEnd A) ^ k) x = (∑ i ∈ Finset.range k, (toEnd A) ^ i) t := by
  rw [affinePerm_pow_apply]
  -- `AddMonoidHom.sub_apply` does not rewrite the endomorphism ring's subtraction at
  -- this pin. Expose its pointwise definition and the composition-power coercion.
  change A^[k] x + (∑ i ∈ Finset.range k, (toEnd A) ^ i) t = x ↔
    x - A^[k] x = (∑ i ∈ Finset.range k, (toEnd A) ^ i) t
  rw [sub_eq_iff_eq_add']
  exact eq_comm

/-- An affine power has a fixed point exactly when its partial norm is in the image of the
corresponding difference map. This applies to every power, including composite periods. -/
theorem exists_affinePerm_pow_fixedPoint_iff (A : T ≃+ T) (t : T) (k : ℕ) :
    (∃ x, (affinePerm A t ^ k) x = x) ↔
      (∑ i ∈ Finset.range k, (toEnd A) ^ i) t ∈ (1 - (toEnd A) ^ k).range := by
  -- Range membership is definitionally existence of a preimage; transport that witness.
  exact exists_congr fun x ↦ affinePerm_pow_apply_eq_self_iff A t k x

/-- Conjugating by the translation `x ↦ x + b` changes the twist by `(1 - A)b`. -/
theorem affinePerm_conj_addRight (A : T ≃+ T) (t b : T) :
    Equiv.addRight b * affinePerm A t * (Equiv.addRight b)⁻¹ =
      affinePerm A (t + (1 - toEnd A) b) := by
  -- As in the fixed-point proof, expose pointwise subtraction in `AddMonoid.End`;
  -- `AddMonoidHom.sub_apply` does not rewrite through its ring instance at this pin.
  change Equiv.addRight b * affinePerm A t * (Equiv.addRight b)⁻¹ =
    affinePerm A (t + (b - A b))
  ext x
  simp [Equiv.Perm.mul_apply, map_add, map_neg, sub_eq_add_neg]
  abel

end TauCeti.CyclicAffine
