/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import TauCeti.FieldTheory.Finite.PrimitivePolynomial

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.RingTheory.Polynomial.ScaleRoots

/-!
# Scaling roots and root products of primitive polynomials

Let `K` be a finite field with `q` elements and `p : K[X]` a primitive polynomial
(`Polynomial.IsPrimitivePolynomial`), meaning `p` is monic, irreducible, and its roots in any
splitting extension have multiplicative order `q ^ p.natDegree - 1`.

This file proves two properties of primitive polynomials over finite fields:

* Scaling the roots of `p` by an `M`-th root of unity `a : Kˣ` with `M ^ 2 ∣ q - 1` preserves
  primitivity (`Polynomial.IsPrimitivePolynomial.scaleRoots`), because every prime dividing the
  order of `a` divides `(orderOf a) ^ 2 ∣ M ^ 2 ∣ q - 1 ∣ q ^ r - 1`.
* For any irreducible polynomial `p : K[X]` and root `ξ` in a nontrivial `K`-algebra integral
  domain `L`, the product of the roots of `p` is `ξ ^ (∑ i ∈ Finset.range p.natDegree, q ^ i)`
  (`Polynomial.pow_geom_sum_eq_prod_aroots_of_irreducible`, specialized to primitive polynomials as
  `Polynomial.IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots`), and when `p` is primitive this
  product is a primitive `(q - 1)`-th root of unity
  (`Polynomial.IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots`).

## Main results

* `Polynomial.IsPrimitivePolynomial.scaleRoots`: scaling roots by an `M`-th root of unity with
  `M ^ 2 ∣ Nat.card K - 1` preserves `Polynomial.IsPrimitivePolynomial`.
* `Polynomial.pow_geom_sum_eq_prod_aroots_of_irreducible`: for an irreducible polynomial over a
  finite field, the root product equals the Frobenius norm power
  `ξ ^ (∑ i ∈ Finset.range p.natDegree, Nat.card K ^ i)`.
* `Polynomial.IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots`: primitive-polynomial
  specialization.
* `Polynomial.IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots`: the root product is a primitive
  `(Nat.card K - 1)`-th root of unity.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/Objects/LabelsAndIndexTypes.lean`, declarations
`New.IsPrimitivePolynomial.scaleRoots`, `New.IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots`,
and `New.IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots`.
-/

public section

open Finset

namespace Polynomial

variable {K : Type*} [Field K]

/-- Scaling the roots of a primitive polynomial `p` over a finite field `K` by an `M`-th root of
unity `a : Kˣ` with `M ^ 2 ∣ Nat.card K - 1` yields a primitive polynomial. -/
theorem IsPrimitivePolynomial.scaleRoots [Finite K] {p : K[X]} (hp : p.IsPrimitivePolynomial)
    (a : Kˣ) {M : ℕ} (ha : (a : K) ^ M = 1) (hM : M ^ 2 ∣ Nat.card K - 1) :
    (p.scaleRoots (a : K)).IsPrimitivePolynomial := by
  obtain ⟨h_monic_p, h_irr_p, h_ord_p⟩ := isPrimitivePolynomial_iff.mp hp
  have h_two_le : 2 ≤ Nat.card K ^ p.natDegree :=
    (Nat.succ_le_of_lt Finite.one_lt_card).trans
      (Nat.le_self_pow h_irr_p.natDegree_pos.ne' (Nat.card K))
  have : Fact (Irreducible p) := ⟨h_irr_p⟩
  let ξ : AdjoinRoot p := AdjoinRoot.root p
  let b : AdjoinRoot p := algebraMap K (AdjoinRoot p) (a : K)
  have h_root : aeval (b * ξ) (p.scaleRoots (a : K)) = 0 := by
    simpa [b, mul_comm] using scaleRoots_aeval_eq_zero (r := (a : K))
      ((AdjoinRoot.aeval_eq p).trans AdjoinRoot.mk_self)
  rw [isPrimitivePolynomial_iff_orderOf_eq (x := b * ξ) h_root]
  refine ⟨(monic_scaleRoots_iff (a : K)).mpr h_monic_p, irreducible_scaleRoots h_irr_p a, ?_⟩
  rw [natDegree_scaleRoots, ← h_ord_p]
  refine (Commute.all b ξ).orderOf_mul_eq_right_of_forall_prime_mul_dvd
    (orderOf_pos_iff.mp (h_ord_p ▸ Nat.sub_pos_of_lt h_two_le)) fun q _ hq_dvd ↦ ?_
  calc q * orderOf b ∣ orderOf b ^ 2 := by simpa [sq] using mul_dvd_mul_right hq_dvd (orderOf b)
    _ ∣ M ^ 2 := pow_dvd_pow_of_dvd (orderOf_dvd_of_pow_eq_one (by simp [b, ← map_pow, ha])) 2
    _ ∣ Nat.card K - 1 := hM
    _ ∣ Nat.card K ^ p.natDegree - 1 := Nat.sub_one_dvd_pow_sub_one _ _
    _ = orderOf ξ := h_ord_p.symm

/-- For an irreducible polynomial `p` over a finite field `K` and any root `ξ` in a `K`-algebra
integral domain `L`, the product of the roots of `p` in `L` equals
`ξ ^ (∑ i ∈ Finset.range p.natDegree, Nat.card K ^ i)`. -/
theorem pow_geom_sum_eq_prod_aroots_of_irreducible [Finite K] {L : Type*} [CommRing L]
    [IsDomain L] [Algebra K L] {p : K[X]} (hp : Irreducible p) {ξ : L}
    (hξ : aeval ξ p = 0) :
    ξ ^ ∑ i ∈ range p.natDegree, Nat.card K ^ i = (p.aroots L).prod := by
  cases nonempty_fintype K
  rw [TauCeti.FiniteField.aroots_eq_map_pow_card_pow hp hξ, ← prod_pow_eq_pow_sum,
    Nat.card_eq_fintype_card, Finset.prod_eq_multiset_prod, range_val]

/-- For a primitive polynomial `p` over a finite field `K` and any root `ξ` in a `K`-algebra
integral domain `L`, the product of the roots of `p` in `L` equals
`ξ ^ (∑ i ∈ Finset.range p.natDegree, Nat.card K ^ i)`. -/
theorem IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots [Finite K] {L : Type*} [CommRing L]
    [IsDomain L] [Algebra K L] {p : K[X]} (hp : p.IsPrimitivePolynomial) {ξ : L}
    (hξ : aeval ξ p = 0) :
    ξ ^ ∑ i ∈ range p.natDegree, Nat.card K ^ i = (p.aroots L).prod :=
  pow_geom_sum_eq_prod_aroots_of_irreducible hp.irreducible hξ

/-- The product of the roots of a primitive polynomial `p` over a finite field `K` in any
`K`-algebra integral domain `L` containing a root of `p` is a primitive `(Nat.card K - 1)`-th
root of unity. -/
theorem IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots [Finite K] {L : Type*} [CommRing L]
    [IsDomain L] [Algebra K L] {p : K[X]} (hp : p.IsPrimitivePolynomial) {ξ : L}
    (hξ : aeval ξ p = 0) :
    IsPrimitiveRoot (p.aroots L).prod (Nat.card K - 1) := by
  have h_two_le : 2 ≤ Nat.card K ^ p.natDegree :=
    (Nat.succ_le_of_lt Finite.one_lt_card).trans
      (Nat.le_self_pow hp.irreducible.natDegree_pos.ne' (Nat.card K))
  obtain ⟨-, -, h_ord⟩ := (isPrimitivePolynomial_iff_orderOf_eq hξ).mp hp
  have h_prim : IsPrimitiveRoot ξ (Nat.card K ^ p.natDegree - 1) :=
    IsPrimitiveRoot.iff_orderOf.mpr h_ord
  rw [← hp.pow_geom_sum_eq_prod_aroots hξ]
  exact h_prim.pow (Nat.sub_pos_of_lt h_two_le)
    (geom_sum_mul_of_one_le Nat.card_pos p.natDegree).symm

end Polynomial
