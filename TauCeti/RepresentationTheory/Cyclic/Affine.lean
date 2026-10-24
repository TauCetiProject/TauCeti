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
import Mathlib.Tactic.Abel

/-!
# Affine automorphisms of an additive commutative group

Let `T` be an additive commutative group, `A : T ≃+ T` an additive automorphism of `T`, and
`t : T`. The affine automorphism of `T` with linear part `A` and translation part `t` is the map
`x ↦ A x + t`. It is a bijection of the underlying type, written `AddEquiv.affineEquiv A t`, but an
additive homomorphism only when `t = 0`.

Iterating the affine automorphism accumulates its translations: the `k`-th iterate is the `k`-th
iterate of the linear part followed by the partial norm
`AddEquiv.cyclicNorm A k t = ∑ i < k, A^i t`, that is

`(affineEquiv A t)^k x = A^k x + cyclicNorm A k t`

(`AddEquiv.affineEquiv_iterate_apply`). The partial norm is indexed by an arbitrary exponent `k`,
which is what the iterate and period formulas below need; its value at `k = m` is the ordered sum
`∑ i < m, A^i t` appearing in the `m`-periodicity criterion.

The iterate formula turns the period of the affine automorphism into a linear condition on its
translation. If the linear part has period dividing `m`, then the affine automorphism has
`m`-th power the identity exactly when the translation is killed by the `m`-th partial norm
(`AddEquiv.affineEquiv_iterate_eq_id_iff`). The iterates then depend only on the exponent modulo
`m`, and `ZMod m` acts on `T` by them (`AddEquiv.affineAddAction`), with the residue `1` acting by
the affine automorphism itself (`AddEquiv.affineAddAction_one_vadd`). The affine automorphism has
exact order `m` exactly when, in addition, every smaller positive iterate differs from the
identity (`AddEquiv.orderOf_affineEquiv_eq_iff`), which for an affine automorphism means that each
of those iterates has a nontrivial linear part or a nonzero partial norm.

## Main definitions

* `AddEquiv.affineEquiv A t`: the affine equivalence `x ↦ A x + t` of `T`, with linear part `A` and
  translation part `t`.
* `AddEquiv.cyclicNorm A k t`: the partial norm `∑ i < k, A^i t` of the translation part, that is
  the translation accumulated by `k` iterates.
* `AddEquiv.affineAddAction`: the action of `ZMod m` on `T` by the iterates of an affine
  equivalence whose `m`-th iterate is the identity.

## Main results

* `AddEquiv.affineEquiv_iterate_apply`: the `k`-th iterate of the affine equivalence is the
  `k`-th iterate of its linear part plus the `k`-th partial norm of its translation part.
* `AddEquiv.affineEquiv_iterate_add_period`: an affine equivalence whose `m`-th iterate is the
  identity has equal iterates at exponents differing by `m`.
* `AddEquiv.affineEquiv_iterate_eq_id_iff`, `AddEquiv.affineEquiv_pow_eq_one_iff`: the affine
  equivalence has `m`-th power the identity exactly when the `m`-th partial norm of its
  translation part vanishes.
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

Its inverse sends `y` to `A⁻¹ (y - t)`. It is an additive homomorphism only when `t = 0`. -/
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
def cyclicNorm (A : T ≃+ T) (k : ℕ) (t : T) : T :=
  ∑ i ∈ Finset.range k, (⇑A)^[i] t

@[simp]
theorem cyclicNorm_zero (A : T ≃+ T) (t : T) : cyclicNorm A 0 t = 0 := by
  simp [cyclicNorm]

/-- Shifting the linear part through the partial norm: `A (N_{A,k} t) = N_{A,k} (A t)`. -/
theorem map_cyclicNorm (A : T ≃+ T) (k : ℕ) (t : T) :
    A (cyclicNorm A k t) = cyclicNorm A k (A t) := by
  rw [cyclicNorm, cyclicNorm, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← Function.iterate_succ_apply' (f := ⇑A) i t,
      Function.iterate_succ_apply (f := ⇑A) i t]

/-- The partial norm satisfies the recurrence `N_{A,k+1} t = t + A (N_{A,k} t)`: a further iterate
appends one more translate of the linear part. -/
theorem cyclicNorm_succ (A : T ≃+ T) (k : ℕ) (t : T) :
    cyclicNorm A (k + 1) t = t + A (cyclicNorm A k t) := by
  have hshift : cyclicNorm A (k + 1) t = cyclicNorm A k (A t) + t := by
    rw [cyclicNorm, cyclicNorm, Finset.sum_range_succ']
    simp only [Function.iterate_zero, id_eq]
    congr 1
  calc cyclicNorm A (k + 1) t = cyclicNorm A k (A t) + t := hshift
    _ = A (cyclicNorm A k t) + t := by rw [map_cyclicNorm]
    _ = t + A (cyclicNorm A k t) := add_comm _ _

/-! ### The iterate formula -/

/-- The `k`-th iterate of an affine equivalence is the `k`-th iterate of its linear part plus the
`k`-th partial norm of its translation part. -/
theorem affineEquiv_iterate_apply (A : T ≃+ T) (t x : T) (k : ℕ) :
    (⇑(affineEquiv A t))^[k] x = (⇑A)^[k] x + cyclicNorm A k t := by
  induction k generalizing x with
  | zero =>
    rw [cyclicNorm_zero, add_zero]
    rfl
  | succ k ih =>
    calc (⇑(affineEquiv A t))^[Nat.succ k] x
        = affineEquiv A t ((⇑(affineEquiv A t))^[k] x) :=
          Function.iterate_succ_apply' (f := ⇑(affineEquiv A t)) k x
      _ = affineEquiv A t ((⇑A)^[k] x + cyclicNorm A k t) := by rw [ih]
      _ = A ((⇑A)^[k] x + cyclicNorm A k t) + t := affineEquiv_apply A t _
      _ = A ((⇑A)^[k] x) + A (cyclicNorm A k t) + t := by rw [map_add]
      _ = A ((⇑A)^[k] x) + (t + A (cyclicNorm A k t)) := by abel
      _ = (⇑A)^[Nat.succ k] x + cyclicNorm A (Nat.succ k) t := by
          have h1 : (⇑A)^[Nat.succ k] x = A ((⇑A)^[k] x) :=
            Function.iterate_succ_apply' (f := ⇑A) k x
          have h2 : cyclicNorm A (Nat.succ k) t = t + A (cyclicNorm A k t) :=
            cyclicNorm_succ A k t
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
    (⇑(affineEquiv A t))^[m] = id ↔ (⇑A)^[m] = id ∧ cyclicNorm A m t = 0 := by
  have hzero : (⇑A)^[m] (0 : T) = 0 := Function.iterate_fixed (map_zero A) m
  constructor
  · intro h
    have hx : ∀ x : T, (⇑A)^[m] x + cyclicNorm A m t = x := by
      intro x
      rw [← affineEquiv_iterate_apply A t x m, congrFun h x]
      rfl
    have hN : cyclicNorm A m t = 0 := by
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
    (affineEquiv A t) ^ m = 1 ↔ (⇑A)^[m] = id ∧ cyclicNorm A m t = 0 := by
  have hbridge : (affineEquiv A t) ^ m = 1 ↔ (⇑(affineEquiv A t))^[m] = id := by
    rw [← Equiv.coe_fn_injective.eq_iff]
    simp [Equiv.Perm.coe_pow]
  rw [hbridge]
  exact affineEquiv_iterate_eq_id_iff A t m

/-- If the linear part has `m`-th iterate the identity, then the affine equivalence has `m`-th power
the identity exactly when the `m`-th partial norm of its translation part vanishes: the order of
the affine equivalence divides `m`. -/
theorem affineEquiv_pow_eq_one_iff_of_iterate_eq_id (A : T ≃+ T) (t : T) (m : ℕ)
    (hA : (⇑A)^[m] = id) :
    (affineEquiv A t) ^ m = 1 ↔ cyclicNorm A m t = 0 := by
  rw [affineEquiv_pow_eq_one_iff, hA]
  simp

/-- The exact order criterion: under a linear part of period dividing `m`, the affine equivalence
has exact order `m` exactly when its `m`-th partial norm vanishes and no smaller positive iterate
is the identity. For an affine equivalence the latter means that every iterate with `0 < k < m`
has a nontrivial linear part or a nonzero partial norm. -/
theorem orderOf_affineEquiv_eq_iff (A : T ≃+ T) (t : T) (m : ℕ) (hm : 0 < m)
    (hA : (⇑A)^[m] = id) :
    orderOf (affineEquiv A t) = m ↔ cyclicNorm A m t = 0 ∧
      ∀ k, 0 < k → k < m → ((⇑A)^[k] ≠ id ∨ cyclicNorm A k t ≠ 0) := by
  have hpow : (affineEquiv A t) ^ m = 1 ↔ cyclicNorm A m t = 0 :=
    affineEquiv_pow_eq_one_iff_of_iterate_eq_id A t m hA
  constructor
  · intro h
    have hN : cyclicNorm A m t = 0 :=
      hpow.1 (by rw [← h]; exact pow_orderOf_eq_one _)
    refine ⟨hN, fun k hk0 hkm => ?_⟩
    have hne : (affineEquiv A t) ^ k ≠ 1 := by
      intro hk
      have hdvd : m ∣ k := by
        rw [← h]
        exact orderOf_dvd_iff_pow_eq_one.2 hk
      exact absurd (Nat.le_of_dvd hk0 hdvd) (Nat.not_le.2 hkm)
    exact not_and_or.1 fun hk => hne ((affineEquiv_pow_eq_one_iff A t k).2 hk)
  · rintro ⟨hN, hsmall⟩
    have hdvd : orderOf (affineEquiv A t) ∣ m :=
      orderOf_dvd_iff_pow_eq_one.2 (hpow.2 hN)
    have hpos : 0 < orderOf (affineEquiv A t) :=
      Nat.pos_of_ne_zero fun h0 => by
        rw [h0] at hdvd
        exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (Nat.ne_of_gt hm)
    have hle : m ≤ orderOf (affineEquiv A t) := by
      rcases lt_or_ge (orderOf (affineEquiv A t)) m with hlt | hge
      · exfalso
        rcases (affineEquiv_pow_eq_one_iff A t _).1 (pow_orderOf_eq_one (affineEquiv A t))
          with ⟨hAk, hNk⟩
        rcases hsmall _ hpos hlt with h | h
        · exact h hAk
        · exact h hNk
      · exact hge
    exact Nat.le_antisymm (Nat.le_of_dvd hm hdvd) hle

/-! ### The action of `ZMod m` by iterates -/

section Periodic

variable {m : ℕ} [NeZero m]

/-- The action of `ZMod m` on `T` by the iterates of an affine equivalence whose `m`-th iterate is
the identity. The residue `k` acts by the `k`-th iterate, which is well defined by the periodicity
of the iterates; `AddEquiv.affineAddAction_vadd` evaluates it. -/
-- the body is exposed because `affineAddAction_vadd` states the value of the action by reduction
@[expose, instance_reducible]
def affineAddAction (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : cyclicNorm A m t = 0) : AddAction (ZMod m) T where
  toVAdd := ⟨fun k x => (⇑(affineEquiv A t))^[k.val] x⟩
  zero_vadd x := by
    change (⇑(affineEquiv A t))^[(0 : ZMod m).val] x = x
    rw [ZMod.val_zero]
    rfl
  add_vadd k l x := by
    change (⇑(affineEquiv A t))^[(k + l).val] x =
      (⇑(affineEquiv A t))^[k.val] ((⇑(affineEquiv A t))^[l.val] x)
    have hper : (⇑(affineEquiv A t))^[m] = id :=
      (affineEquiv_iterate_eq_id_iff A t m).2 ⟨hA, hN⟩
    -- the residue of a sum of natural numbers is reached by copies of `m`, which do not move
    have hmod : ∀ i : ℕ, (⇑(affineEquiv A t))^[i] = (⇑(affineEquiv A t))^[i % m] := by
      intro i
      have hq : ∀ q : ℕ, (⇑(affineEquiv A t))^[m * q] = id := by
        intro q
        rw [Function.iterate_mul, hper]
        simp
      conv_lhs => rw [← Nat.mod_add_div i m]
      rw [Function.iterate_add, hq, Function.comp_id]
    rw [ZMod.val_add, ← hmod (k.val + l.val), Function.iterate_add_apply]

@[simp]
theorem affineAddAction_vadd (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : cyclicNorm A m t = 0) (k : ZMod m) (x : T) :
    (affineAddAction (m := m) A t hA hN).vadd k x = (⇑(affineEquiv A t))^[k.val] x :=
  rfl

/-- The residue `1` of `ZMod m` acts by the affine equivalence itself: the action is generated by
the affine equivalence. -/
theorem affineAddAction_one_vadd (A : T ≃+ T) (t : T) (hA : (⇑A)^[m] = id)
    (hN : cyclicNorm A m t = 0) (x : T) :
    (affineAddAction (m := m) A t hA hN).vadd (1 : ZMod m) x = affineEquiv A t x := by
  rw [affineAddAction_vadd, ZMod.val_one_eq_one_mod]
  rcases eq_or_ne m 1 with hm1 | hm1
  · subst hm1
    rw [Nat.mod_one, Function.iterate_zero, affineEquiv_apply]
    have hAid : A = AddEquiv.refl T := by
      ext y
      simpa using congrFun hA y
    have ht : t = 0 := by
      simpa [cyclicNorm] using hN
    rw [hAid, ht, AddEquiv.refl_apply, add_zero]
    rfl
  · rw [Nat.one_mod_eq_one.mpr hm1, Function.iterate_one]

end Periodic

end AddEquiv
