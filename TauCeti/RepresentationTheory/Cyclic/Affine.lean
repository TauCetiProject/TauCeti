/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.BirkhoffSum.Basic
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
`AddEquiv.affineEquiv_iterate_eq_id_iff`. The iterates then depend only on the exponent modulo `m`:
the affine automorphism has `m`-th power the identity, so it is the generator of an action of
`ZMod m` on `T` by its iterates (`AddEquiv.affineAddAction`), and the residue `1` acts by the affine
automorphism itself (`AddEquiv.affineAddAction_one_vadd`). The affine automorphism has exact order
`m` exactly when, in addition, every smaller positive iterate differs from the identity
(`AddEquiv.orderOf_affineEquiv_eq_iff`), which for an affine automorphism means that each of those
iterates has a nontrivial linear part or a nonzero partial norm.

## Main definitions

* `AddEquiv.affineEquiv A t`: the affine equivalence `x ↦ A x + t` of `T`, with linear part `A` and
  translation part `t`.
* `AddEquiv.partialNorm A k t`: the partial norm `∑ i < k, A^i t` of the translation part, that is
  the translation accumulated by `k` iterates.
* `AddEquiv.affineAddAction`: the action of `ZMod m` on `T` by the iterates of an affine
  equivalence whose `m`-th power is the identity.

## Main results

* `AddEquiv.affineEquiv_iterate_apply`: the `k`-th iterate of the affine equivalence is the
  `k`-th iterate of its linear part plus the `k`-th partial norm of its translation part.
* `AddEquiv.partialNorm_def`: the partial norm as its defining finite sum.
* `AddEquiv.partialNorm_add`, `AddEquiv.partialNorm_neg`, `AddEquiv.partialNorm_sub`,
  `AddEquiv.partialNorm_zero_right`, `AddEquiv.partialNorm_add_exponent`: the partial norm is
  additive in its translation argument, vanishes on the zero translation part, and splits over the
  exponent.
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
* `AddEquiv.affineAddAction_vadd`, `AddEquiv.affineAddAction_one_vadd`: the residue `k` of `ZMod m`
  acts by the `k`-th iterate of the affine equivalence, and the residue `1` by the affine
  equivalence itself.
-/

public section

namespace AddEquiv

variable {T : Type*} [AddCommGroup T]

/-! ### The affine equivalence -/

/-- The affine equivalence of an additive commutative group with linear part `A` and translation
part `t`, sending `x` to `A x + t`.

Its inverse sends `y` to `A⁻¹ (y - t)`. It is an additive homomorphism only when `t = 0`. As an
affine self-map of the `ℤ`-module `T` it is the affine equivalence with linear part
`A.toIntLinearEquiv` and base points `0` and `t` (so `0 ↦ t`), which Mathlib provides as
`AffineEquiv.ofLinearEquiv`, and it is the element of the group `AffineEquiv` with those data. It is
recorded here as a permutation of `T`, because the iterates, the order and the action of `ZMod m`
below are those of the underlying permutation. -/
def affineEquiv (A : T ≃+ T) (t : T) : T ≃ T :=
  (A : T ≃ T).trans (Equiv.addRight t)

/-- The affine equivalence sends `x` to `A x + t`. -/
@[simp]
theorem affineEquiv_apply (A : T ≃+ T) (t x : T) : affineEquiv A t x = A x + t := by
  simp [affineEquiv]

/-- The inverse of the affine equivalence sends `y` to `A⁻¹ (y - t)`. -/
@[simp]
theorem affineEquiv_symm_apply (A : T ≃+ T) (t y : T) :
    (affineEquiv A t).symm y = A.symm (y - t) := by
  simp [affineEquiv, sub_eq_add_neg]

/-! ### The partial norm of a translation part -/

/-- The partial norm `∑ i < k, A^i t` of the translation part `t`: the translation accumulated by
the first `k` iterates of the affine equivalence with linear part `A` and translation part `t`. -/
def partialNorm (A : T ≃+ T) (k : ℕ) (t : T) : T :=
  birkhoffSum (⇑A) id k t

/-- The partial norm is the defining finite sum `∑ i < k, A^i t`. -/
theorem partialNorm_def (A : T ≃+ T) (k : ℕ) (t : T) :
    partialNorm A k t = ∑ i ∈ Finset.range k, (⇑A)^[i] t := by
  simp only [partialNorm, birkhoffSum, id_eq]

/-- The partial norm of zero iterates is zero. -/
@[simp]
theorem partialNorm_zero (A : T ≃+ T) (t : T) : partialNorm A 0 t = 0 := by
  simpa only [partialNorm] using birkhoffSum_zero_apply (⇑A) id t

/-- The partial norm of one iterate is the translation part itself. -/
@[simp]
theorem partialNorm_one (A : T ≃+ T) (t : T) : partialNorm A 1 t = t := by
  simpa only [partialNorm, id_eq] using birkhoffSum_one_apply (⇑A) id t

/-- The partial norm is additive in its translation argument. -/
@[simp]
theorem partialNorm_add (A : T ≃+ T) (k : ℕ) (u v : T) :
    partialNorm A k (u + v) = partialNorm A k u + partialNorm A k v := by
  simp only [partialNorm_def, ← Finset.sum_add_distrib, iterate_map_add]

/-- The partial norm is additive in its translation argument, in negative form. -/
@[simp]
theorem partialNorm_neg (A : T ≃+ T) (k : ℕ) (u : T) :
    partialNorm A k (-u) = -partialNorm A k u := by
  simp only [partialNorm_def, ← Finset.sum_neg_distrib, iterate_map_neg]

/-- The partial norm is additive in its translation argument, in difference form. -/
@[simp]
theorem partialNorm_sub (A : T ≃+ T) (k : ℕ) (u v : T) :
    partialNorm A k (u - v) = partialNorm A k u - partialNorm A k v := by
  simp only [sub_eq_add_neg, partialNorm_add, partialNorm_neg]

/-- The partial norm vanishes on the zero translation part. -/
@[simp]
theorem partialNorm_zero_right (A : T ≃+ T) (k : ℕ) : partialNorm A k 0 = 0 := by
  simp only [partialNorm_def, iterate_map_zero, Finset.sum_const_zero]

/-- Shifting the linear part through the partial norm: `A (N_{A,k} t) = N_{A,k} (A t)`. -/
theorem map_partialNorm (A : T ≃+ T) (k : ℕ) (t : T) :
    A (partialNorm A k t) = partialNorm A k (A t) := by
  simp only [partialNorm]
  rw [map_birkhoffSum, ← birkhoffSum_comp_apply]
  simp only [Function.comp_id, Function.id_comp]

/-- Splitting the exponent of a partial norm: the partial norm of `k + l` iterates is the partial
norm of `k` iterates plus the `k`-th iterate of the linear part applied to the partial norm of `l`
iterates, `N_{A,k+l} t = N_{A,k} t + A^k (N_{A,l} t)`. -/
theorem partialNorm_add_exponent (A : T ≃+ T) (k l : ℕ) (t : T) :
    partialNorm A (k + l) t = partialNorm A k t + (⇑A)^[k] (partialNorm A l t) := by
  have hcomm : Function.Commute ((⇑A)^[k]) (partialNorm A l) :=
    Function.Commute.iterate_left (map_partialNorm A l) k
  rw [hcomm t]
  simp only [partialNorm]
  exact birkhoffSum_add_right_apply (⇑A) id k l t

/-- The partial norm satisfies the recurrence `N_{A,k+1} t = t + A (N_{A,k} t)`: a further iterate
appends one more translate of the linear part. -/
theorem partialNorm_succ (A : T ≃+ T) (k : ℕ) (t : T) :
    partialNorm A (k + 1) t = t + A (partialNorm A k t) := by
  rw [Nat.add_comm k 1, partialNorm_add_exponent, partialNorm_one, Function.iterate_one]

/-- The norm of the cyclic representation of a linear part `A` of period dividing `m` is the partial
norm `partialNorm A m` of order `m`. -/
theorem cyclicRepresentation_norm_eq_partialNorm {m : ℕ} [NeZero m] (A : T ≃+ T)
    (hA : (⇑A)^[m] = id) (x : T) :
    (A.cyclicRepresentation hA).norm x = partialNorm A m x := by
  rw [cyclicRepresentation_norm_apply, partialNorm_def]

/-! ### The iterate formula -/

/-- The `k`-th iterate of an affine equivalence is the `k`-th iterate of its linear part plus the
`k`-th partial norm of its translation part. -/
theorem affineEquiv_iterate_apply (A : T ≃+ T) (t x : T) (k : ℕ) :
    (⇑(affineEquiv A t))^[k] x = (⇑A)^[k] x + partialNorm A k t := by
  induction k generalizing x with
  | zero => simp only [Function.iterate_zero_apply, partialNorm_zero, add_zero]
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, affineEquiv_apply, map_add, partialNorm_succ]
    abel

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
      rw [← affineEquiv_iterate_apply A t x m]
      exact congrFun h x
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

/-- The action of `ZMod m` on `T` by the iterates of an affine equivalence whose `m`-th power is
the identity: the residue `k` acts by the `k`-th iterate, which is well defined because the iterates
are periodic with period `m`. `AddEquiv.affineAddAction_vadd` evaluates it. -/
@[instance_reducible]
noncomputable def affineAddAction (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : partialNorm A m t = 0) : AddAction (ZMod m) T :=
  AddAction.compHom T (MonoidHom.toAdditiveRight
    ((TauCeti.zmodMonoidHomEquiv m (Equiv.Perm T)).symm
      ⟨affineEquiv A t, (affineEquiv_pow_eq_one_iff A t m).2 ⟨hA, hN⟩⟩))

/-- The residue `k` of `ZMod m` acts on `T` by the `k`-th iterate of the affine equivalence. -/
@[simp]
theorem affineAddAction_vadd (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : partialNorm A m t = 0) (k : ZMod m) (x : T) :
    letI := affineAddAction (m := m) A t hA hN
    k +ᵥ x = (⇑(affineEquiv A t))^[k.val] x := by
  simp only [AddAction.compHom_vadd_def, MonoidHom.coe_toAdditiveRight, Function.comp_apply,
    TauCeti.zmodMonoidHomEquiv_symm_apply, ofMul_vadd, Equiv.Perm.smul_def, Equiv.Perm.coe_pow]

/-- The residue `1` of `ZMod m` acts by the affine equivalence itself: the action is generated by
the affine equivalence. -/
theorem affineAddAction_one_vadd (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : partialNorm A m t = 0) (x : T) :
    letI := affineAddAction (m := m) A t hA hN
    (1 : ZMod m) +ᵥ x = affineEquiv A t x := by
  simp only [AddAction.compHom_vadd_def, MonoidHom.coe_toAdditiveRight, Function.comp_apply,
    TauCeti.zmodMonoidHomEquiv_symm_apply_ofAdd_one, ofMul_vadd, Equiv.Perm.smul_def]

end Periodic

end AddEquiv
