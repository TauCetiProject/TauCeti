/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Logic.Function.Iterate
public import TauCeti.RepresentationTheory.Cyclic.Automorphism
import Mathlib.Tactic.Abel

/-!
# Affine automorphisms of an additive commutative group

Let `T` be an additive commutative group, `A : T ≃+ T` an additive automorphism of `T`, and
`t : T`. The affine automorphism of `T` with linear part `A` and translation part `t` is the map
`x ↦ A x + t`. It is a bijection of the underlying type, written `AddEquiv.affineEquiv A t`, but an
additive homomorphism only when `t = 0`.

Iterating the affine automorphism accumulates its translations: the `k`-th iterate is the `k`-th
iterate of the linear part followed by the partial norm
`AddEquiv.partialNorm A k t = ∑ i < k, A^i t`, that is

`(affineEquiv A t)^k x = A^k x + partialNorm A k t`

(`AddEquiv.affineEquiv_iterate_apply`). The partial norm is indexed by an arbitrary exponent `k`.
For a linear part of period dividing `m`, its value at `k = m` is the norm of the cyclic
representation of `A` (`AddEquiv.cyclicRepresentation_norm_eq_partialNorm`).

The iterate formula turns the period of the affine automorphism into a linear condition on its
translation. If the linear part has period dividing `m`, then the affine automorphism has `m`-th
power the identity exactly when the translation is killed by the `m`-th partial norm, and its order
then divides `m` (`AddEquiv.affineEquiv_pow_eq_one_iff_of_iterate_eq_id`,
`AddEquiv.orderOf_affineEquiv_dvd_iff`); without a hypothesis on the linear part the criterion is
`AddEquiv.affineEquiv_iterate_eq_id_iff`. The iterates then depend only on the exponent modulo `m`,
and `ZMod m` acts on `T` by them (`AddEquiv.affineAddAction`), with the residue `1` acting by the
affine automorphism itself (`AddEquiv.affineAddAction_one_vadd`). The affine automorphism has exact
order `m` exactly when, in addition, every smaller positive iterate differs from the identity
(`AddEquiv.orderOf_affineEquiv_eq_iff`), which for an affine automorphism means that each of those
iterates has a nontrivial linear part or a nonzero partial norm.

## Main definitions

* `AddEquiv.affineEquiv A t`: the affine equivalence `x ↦ A x + t` of `T`, with linear part `A` and
  translation part `t`.
* `AddEquiv.partialNorm A k t`: the partial norm `∑ i < k, A^i t` of the translation part, that is
  the translation accumulated by `k` iterates.
* `AddEquiv.affineAddAction`: the action of `ZMod m` on `T` by the iterates of an affine
  equivalence whose `m`-th iterate is the identity.

## Main results

* `AddEquiv.affineEquiv_iterate_apply`: the `k`-th iterate of the affine equivalence is the
  `k`-th iterate of its linear part plus the `k`-th partial norm of its translation part.
* `AddEquiv.affineEquiv_iterate_add_period`: an affine equivalence whose `m`-th iterate is the
  identity has equal iterates at exponents differing by `m`.
* `AddEquiv.cyclicRepresentation_norm_eq_partialNorm`: the norm of the cyclic representation of `A`
  is the partial norm of order `m`.
* `AddEquiv.affineEquiv_iterate_eq_id_iff`, `AddEquiv.affineEquiv_pow_eq_one_iff`: the affine
  equivalence has `m`-th power the identity exactly when its linear part has `m`-th iterate the
  identity and the `m`-th partial norm of its translation part vanishes.
* `AddEquiv.affineEquiv_pow_eq_one_iff_of_iterate_eq_id`,
  `AddEquiv.orderOf_affineEquiv_dvd_iff`: under a linear part of period dividing `m`, the same
  criterion needs only the partial norm, and then the order of the affine equivalence divides `m`.
* `AddEquiv.orderOf_affineEquiv_eq_iff`: the affine equivalence has exact order `m` exactly when
  its `m`-th power is the identity and no smaller positive power is.

## References

* Kenneth S. Brown, *Cohomology of Groups*, Chapter VI, Section 2, for the cyclic norm of a
  translation part and the periodicity of its partial sums.
-/

public section

namespace AddEquiv

variable {T : Type*} [AddCommGroup T]

/-! ### The affine equivalence -/

/-- The affine equivalence of an additive commutative group with linear part `A` and translation
part `t`, sending `x` to `A x + t`.

Its inverse sends `y` to `A⁻¹ (y - t)`. It is an additive homomorphism only when `t = 0`. As an
affine self-map of the `ℤ`-module `T` it is the affine equivalence with linear part
`A.toIntLinearEquiv` and base point `t`, which Mathlib provides as `AffineEquiv.ofLinearEquiv`; it
is recorded here as a permutation of `T` because the iterates, the order and the action of `ZMod m`
below are properties of that permutation, and `AffineEquiv` carries no group structure. -/
def affineEquiv (A : T ≃+ T) (t : T) : T ≃ T where
  toFun x := A x + t
  invFun y := A.symm (y - t)
  left_inv x := by simp
  right_inv y := by simp

@[simp]
theorem affineEquiv_apply (A : T ≃+ T) (t x : T) : affineEquiv A t x = A x + t := by
  simp [affineEquiv]

@[simp]
theorem affineEquiv_symm_apply (A : T ≃+ T) (t y : T) :
    (affineEquiv A t).symm y = A.symm (y - t) := by
  rw [Equiv.symm_apply_eq, affineEquiv_apply, AddEquiv.apply_symm_apply, sub_add_cancel]

/-! ### The partial norm of a translation part -/

/-- The partial norm `∑ i < k, A^i t` of the translation part `t`: the translation accumulated by
the first `k` iterates of the affine equivalence with linear part `A` and translation part `t`. -/
def partialNorm (A : T ≃+ T) (k : ℕ) (t : T) : T :=
  ∑ i ∈ Finset.range k, (⇑A)^[i] t

@[simp]
theorem partialNorm_zero (A : T ≃+ T) (t : T) : partialNorm A 0 t = 0 := by
  simp [partialNorm]

@[simp]
theorem partialNorm_one (A : T ≃+ T) (t : T) : partialNorm A 1 t = t := by
  simp [partialNorm]

/-- Shifting the linear part through the partial norm: `A (N_{A,k} t) = N_{A,k} (A t)`. -/
theorem map_partialNorm (A : T ≃+ T) (k : ℕ) (t : T) :
    A (partialNorm A k t) = partialNorm A k (A t) := by
  rw [partialNorm, partialNorm, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← Function.iterate_succ_apply' (f := ⇑A) i t,
      Function.iterate_succ_apply (f := ⇑A) i t]

/-- The partial norm satisfies the recurrence `N_{A,k+1} t = t + A (N_{A,k} t)`: a further iterate
appends one more translate of the linear part. -/
theorem partialNorm_succ (A : T ≃+ T) (k : ℕ) (t : T) :
    partialNorm A (k + 1) t = t + A (partialNorm A k t) := by
  have hshift : partialNorm A (k + 1) t = partialNorm A k (A t) + t := by
    rw [partialNorm, partialNorm, Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq]
    congr 1
  calc partialNorm A (k + 1) t = partialNorm A k (A t) + t := hshift
    _ = A (partialNorm A k t) + t := by rw [map_partialNorm]
    _ = t + A (partialNorm A k t) := add_comm _ _

/-- The norm of the cyclic representation of a linear part of period dividing `m` is the partial
norm of order `m` of its translation part. -/
theorem cyclicRepresentation_norm_eq_partialNorm {m : ℕ} [NeZero m] (A : T ≃+ T)
    (hA : (⇑A)^[m] = id) (x : T) :
    (A.cyclicRepresentation hA).norm x = partialNorm A m x := by
  rw [cyclicRepresentation_norm_apply, partialNorm]

/-! ### The iterate formula -/

/-- The `k`-th iterate of an affine equivalence is the `k`-th iterate of its linear part plus the
`k`-th partial norm of its translation part. -/
theorem affineEquiv_iterate_apply (A : T ≃+ T) (t x : T) (k : ℕ) :
    (⇑(affineEquiv A t))^[k] x = (⇑A)^[k] x + partialNorm A k t := by
  induction k generalizing x with
  | zero =>
    rw [partialNorm_zero, add_zero]
    rfl
  | succ k ih =>
    calc (⇑(affineEquiv A t))^[Nat.succ k] x
        = affineEquiv A t ((⇑(affineEquiv A t))^[k] x) :=
          Function.iterate_succ_apply' (f := ⇑(affineEquiv A t)) k x
      _ = affineEquiv A t ((⇑A)^[k] x + partialNorm A k t) := by rw [ih]
      _ = A ((⇑A)^[k] x + partialNorm A k t) + t := affineEquiv_apply A t _
      _ = A ((⇑A)^[k] x) + A (partialNorm A k t) + t := by rw [map_add]
      _ = A ((⇑A)^[k] x) + (t + A (partialNorm A k t)) := by abel
      _ = (⇑A)^[Nat.succ k] x + partialNorm A (Nat.succ k) t := by
          have h1 : (⇑A)^[Nat.succ k] x = A ((⇑A)^[k] x) :=
            Function.iterate_succ_apply' (f := ⇑A) k x
          have h2 : partialNorm A (Nat.succ k) t = t + A (partialNorm A k t) :=
            partialNorm_succ A k t
          rw [h1, h2]

/-- An affine equivalence whose `m`-th iterate is the identity has equal iterates at exponents
differing by `m`. -/
theorem affineEquiv_iterate_add_period (A : T ≃+ T) (t : T) {m : ℕ}
    (h : (⇑(affineEquiv A t))^[m] = id) (k : ℕ) :
    (⇑(affineEquiv A t))^[k + m] = (⇑(affineEquiv A t))^[k] := by
  rw [Function.iterate_add, h, Function.comp_id]

/-! ### The period criterion -/

/-- An affine equivalence has `m`-th iterate the identity exactly when its linear part has `m`-th
iterate the identity and the `m`-th partial norm of its translation part vanishes. -/
theorem affineEquiv_iterate_eq_id_iff (A : T ≃+ T) (t : T) (m : ℕ) :
    (⇑(affineEquiv A t))^[m] = id ↔ (⇑A)^[m] = id ∧ partialNorm A m t = 0 := by
  have hzero : (⇑A)^[m] (0 : T) = 0 := Function.iterate_fixed (map_zero A) m
  constructor
  · intro h
    have hx : ∀ x : T, (⇑A)^[m] x + partialNorm A m t = x := by
      intro x
      rw [← affineEquiv_iterate_apply A t x m, congrFun h x]
      rfl
    have hN : partialNorm A m t = 0 := by
      have := hx 0
      rwa [hzero, zero_add] at this
    refine ⟨funext fun x => ?_, hN⟩
    have := hx x
    rwa [hN, add_zero] at this
  · rintro ⟨hA, hN⟩
    funext x
    rw [affineEquiv_iterate_apply, hA, hN, add_zero]

/-- An affine equivalence has `m`-th power the identity exactly when its linear part has `m`-th
iterate the identity and the `m`-th partial norm of its translation part vanishes. This is
`AddEquiv.affineEquiv_iterate_eq_id_iff` stated in the group of permutations of `T`. -/
theorem affineEquiv_pow_eq_one_iff (A : T ≃+ T) (t : T) (m : ℕ) :
    (affineEquiv A t) ^ m = 1 ↔ (⇑A)^[m] = id ∧ partialNorm A m t = 0 := by
  have hbridge : (affineEquiv A t) ^ m = 1 ↔ (⇑(affineEquiv A t))^[m] = id := by
    rw [← Equiv.coe_fn_injective.eq_iff]
    simp [Equiv.Perm.coe_pow]
  rw [hbridge]
  exact affineEquiv_iterate_eq_id_iff A t m

/-- If the linear part has `m`-th iterate the identity, then the affine equivalence has `m`-th power
the identity exactly when the `m`-th partial norm of its translation part vanishes: the order of
the affine equivalence then divides `m` (`AddEquiv.orderOf_affineEquiv_dvd_iff`). -/
theorem affineEquiv_pow_eq_one_iff_of_iterate_eq_id (A : T ≃+ T) (t : T) (m : ℕ)
    (hA : (⇑A)^[m] = id) :
    (affineEquiv A t) ^ m = 1 ↔ partialNorm A m t = 0 := by
  rw [affineEquiv_pow_eq_one_iff, hA]
  simp

/-- Under a linear part of period dividing `m`, the order of the affine equivalence divides `m`
exactly when the `m`-th partial norm of its translation part vanishes. -/
theorem orderOf_affineEquiv_dvd_iff (A : T ≃+ T) (t : T) (m : ℕ) (hA : (⇑A)^[m] = id) :
    orderOf (affineEquiv A t) ∣ m ↔ partialNorm A m t = 0 := by
  rw [orderOf_dvd_iff_pow_eq_one, affineEquiv_pow_eq_one_iff_of_iterate_eq_id A t m hA]

/-- The exact order criterion: under a linear part of period dividing `m`, the affine equivalence
has exact order `m` exactly when its `m`-th partial norm vanishes and no smaller positive iterate
is the identity. For an affine equivalence the latter means that every iterate with `0 < k < m`
has a nontrivial linear part or a nonzero partial norm. -/
theorem orderOf_affineEquiv_eq_iff (A : T ≃+ T) (t : T) (m : ℕ) (hm : 0 < m)
    (hA : (⇑A)^[m] = id) :
    orderOf (affineEquiv A t) = m ↔ partialNorm A m t = 0 ∧
      ∀ k, 0 < k → k < m → ((⇑A)^[k] ≠ id ∨ partialNorm A k t ≠ 0) := by
  rw [orderOf_eq_iff hm]
  simp only [affineEquiv_pow_eq_one_iff, hA, true_and, ne_eq, not_and_or]
  constructor
  · rintro ⟨hN, h⟩
    exact ⟨hN, fun k hk0 hkm => h k hkm hk0⟩
  · rintro ⟨hN, h⟩
    exact ⟨hN, fun k hkm hk0 => h k hk0 hkm⟩

/-! ### The action of `ZMod m` by iterates -/

section Periodic

variable {m : ℕ} [NeZero m]

/-- The action of `ZMod m` on `T` by the iterates of an affine equivalence whose `m`-th iterate is
the identity. The residue `k` acts by the `k`-th iterate, which is well defined by the periodicity
of the iterates; `AddEquiv.affineAddAction_vadd` evaluates it. -/
@[instance_reducible]
def affineAddAction (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : partialNorm A m t = 0) : AddAction (ZMod m) T where
  toVAdd := ⟨fun k x => (⇑(affineEquiv A t))^[k.val] x⟩
  zero_vadd x := by
    -- the goal states the `vadd` field of the structure being defined, so beta-reduction is the
    -- only way to expose the iterate it contains
    change (⇑(affineEquiv A t))^[(0 : ZMod m).val] x = x
    rw [ZMod.val_zero]
    rfl
  add_vadd k l x := by
    -- the goal states the `vadd` field of the structure being defined, so beta-reduction is the
    -- only way to expose the two iterates it contains
    change (⇑(affineEquiv A t))^[(k + l).val] x =
      (⇑(affineEquiv A t))^[k.val] ((⇑(affineEquiv A t))^[l.val] x)
    have hper : (⇑(affineEquiv A t))^[m] = id :=
      (affineEquiv_iterate_eq_id_iff A t m).2 ⟨hA, hN⟩
    -- shifting an exponent by a multiple of the period does not move the iterate
    have hshift : ∀ i q : ℕ,
        (⇑(affineEquiv A t))^[i + m * q] = (⇑(affineEquiv A t))^[i] := by
      intro i q
      induction q with
      | zero => rw [Nat.mul_zero, add_zero]
      | succ q ih =>
        rw [Nat.mul_succ, ← add_assoc, affineEquiv_iterate_add_period A t hper, ih]
    rw [ZMod.val_add,
      show (⇑(affineEquiv A t))^[(k.val + l.val) % m] =
        (⇑(affineEquiv A t))^[k.val + l.val] by
        conv_rhs => rw [← Nat.mod_add_div (k.val + l.val) m]
        rw [hshift]]
    rw [Function.iterate_add_apply]

@[simp]
theorem affineAddAction_vadd (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : partialNorm A m t = 0) (k : ZMod m) (x : T) :
    (affineAddAction (m := m) A t hA hN).vadd k x = (⇑(affineEquiv A t))^[k.val] x :=
  (rfl)

/-- The residue `1` of `ZMod m` acts by the affine equivalence itself: the action is generated by
the affine equivalence. -/
theorem affineAddAction_one_vadd (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : partialNorm A m t = 0) (x : T) :
    (affineAddAction (m := m) A t hA hN).vadd (1 : ZMod m) x = affineEquiv A t x := by
  rw [affineAddAction_vadd, ZMod.val_one_eq_one_mod]
  rcases eq_or_ne m 1 with hm1 | hm1
  · subst hm1
    rw [Nat.mod_one, Function.iterate_zero, affineEquiv_apply]
    have hAid : A = AddEquiv.refl T := by
      ext y
      simpa using congrFun hA y
    have ht : t = 0 := by
      simpa using hN
    rw [hAid, ht, AddEquiv.refl_apply, add_zero]
    rfl
  · rw [Nat.one_mod_eq_one.mpr hm1, Function.iterate_one]

end Periodic

end AddEquiv
