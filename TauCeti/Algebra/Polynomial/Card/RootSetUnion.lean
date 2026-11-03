/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Int.Interval
public import TauCeti.Algebra.Polynomial.Card.BoundedCoeff

/-!
# Counting the roots of all polynomials of bounded degree and bounded coefficients

For a ring hom `m : R →+* S` into a domain `S` and a finite set `U` of allowed coefficient
values, the set of all roots in `S` of the polynomials of degree at most `d` with every
coefficient in `U`,

`⋃ (f) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U), (f.map m).roots.toFinset`,

has cardinality at most `#U ^ (d + 1) · d`: there are at most `#U ^ (d + 1)` such polynomials
(`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`), and each contributes at most `d`
roots (a degree-`≤ d` polynomial has at most `d` roots in a domain).

This is precisely the explicit count of the *generating set* in Mathlib's proof of Hermite's
finiteness theorem. There, `NumberField.finite_of_discr_bdd` shows the number fields of bounded
discriminant inside a fixed extension are finite by realising each as `ℚ(x)` for `x` a root of an
integer polynomial of explicitly bounded degree and coefficient height, then invoking the
*finiteness* of this very union of root sets, `Polynomial.bUnion_roots_finite`. Mathlib exposes
only that finiteness; the matching explicit cardinality bounds the number of fields generated
by elements of this set, giving an effective Hermite–Minkowski count. This file supplies that
cardinality, upgrading
`Polynomial.bUnion_roots_finite` exactly as
`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le` upgrades the polynomial finiteness it is
built on.

## Main results

* `TauCeti.Polynomial.ncard_biUnion_roots_map_le`: a finite family `t` of polynomials of degree
  `≤ d` has at most `#t · d` roots in `S`.
* `TauCeti.Polynomial.ncard_biUnion_roots_natDegree_le_coeff_mem_le`: at most `#U ^ (d + 1) · d`
  roots in `S` among all degree-`≤ d` polynomials with every coefficient in a finite set `U`.
* `TauCeti.Polynomial.ncard_biUnion_roots_natDegree_le_abs_intCoeff_le`: the integer
  specialisation, `(2 · B + 1) ^ (d + 1) · d` roots among all degree-`≤ d` integer polynomials
  with every coefficient bounded by `B` in absolute value.
* `TauCeti.Polynomial.finite_biUnion_roots_natDegree_le_abs_intCoeff_le`: the same root set
  is finite.
* `TauCeti.Polynomial.finite_biUnion_roots_natDegree_le_coeff_mem_pi`,
  `TauCeti.Polynomial.ncard_biUnion_roots_natDegree_le_coeff_mem_pi_le`: the coefficient-dependent
  version, at most `∏ᵢ #(s i) · n` roots among all degree-`≤ n` polynomials whose `i`-th
  coefficient lies in a finite set `s i`; with `s n = {1}` it counts roots of monic polynomials.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]

/-- The roots in a domain `S` of the polynomials in a finite family `t`, all of degree at most
`d`, mapped along a ring hom `m : R →+* S`, number at most `#t · d`: each polynomial contributes at
most `d` roots. -/
theorem ncard_biUnion_roots_map_le (m : R →+* S) {t : Set R[X]} (ht : t.Finite) {d : ℕ}
    (hd : ∀ f ∈ t, f.natDegree ≤ d) :
    (⋃ f ∈ t, ((f.map m).roots.toFinset : Set S)).ncard ≤ t.ncard * d := by
  set s : R[X] → Set S := fun f => ((f.map m).roots.toFinset : Set S) with hs
  have hbound : ∀ f ∈ t, (s f).ncard ≤ d := by
    intro f hf
    rw [hs, Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le _).trans ((card_roots_map_le_natDegree f).trans (hd f hf))
  calc (⋃ f ∈ t, s f).ncard
      ≤ ∑ᶠ f ∈ t, (s f).ncard := ht.ncard_biUnion_le s
    _ = ∑ f ∈ ht.toFinset, (s f).ncard := finsum_mem_eq_finite_toFinset_sum _ ht
    _ ≤ ∑ _f ∈ ht.toFinset, d :=
        Finset.sum_le_sum fun f hf => hbound f ((Set.Finite.mem_toFinset ht).mp hf)
    _ = ht.toFinset.card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ = t.ncard * d := by rw [Set.ncard_eq_toFinset_card t ht]

/-- The roots in a domain `S` of all polynomials of degree at most `d` with every coefficient in a
finite set `U`, mapped along a ring hom `m : R →+* S`, number at most `#U ^ (d + 1) · d`: there are
at most `#U ^ (d + 1)` such polynomials, and each, having degree at most `d`, has at most `d` roots
in `S`. This is the explicit cardinality of the set whose finiteness is
`Polynomial.bUnion_roots_finite`. -/
theorem ncard_biUnion_roots_natDegree_le_coeff_mem_le (m : R →+* S) (d : ℕ) (U : Finset R) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U),
        ((f.map m).roots.toFinset : Set S)).ncard ≤ U.card ^ (d + 1) * d :=
  (ncard_biUnion_roots_map_le m (finite_setOf_natDegree_le_coeff_mem d U.finite_toSet)
    fun _ hf ↦ hf.1).trans (by gcongr; exact ncard_natDegree_le_coeff_mem_le d U)

/-- The integer specialisation: the roots in a domain `S` of all integer polynomials of degree at
most `d` whose coefficients are bounded by `B` in absolute value form a finite set. -/
theorem finite_biUnion_roots_natDegree_le_abs_intCoeff_le (m : ℤ →+* S) (d B : ℕ) :
    (⋃ (f : ℤ[X]) (_ : f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)),
        ((f.map m).roots.toFinset : Set S)).Finite :=
  (finite_setOf_natDegree_le_abs_intCoeff_le d B).biUnion fun _ _ ↦ Finset.finite_toSet _

/-- The integer specialisation: the roots in a domain `S` of all integer polynomials of degree at
most `d` with every coefficient bounded by `B` in absolute value number at most
`(2 · B + 1) ^ (d + 1) · d`. Each of the `2 · B + 1` integers in `[-B, B]` is an allowed
coefficient, and a degree-`≤ d` polynomial has at most `d` roots. -/
theorem ncard_biUnion_roots_natDegree_le_abs_intCoeff_le (m : ℤ →+* S) (d B : ℕ) :
    (⋃ (f : ℤ[X]) (_ : f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)),
        ((f.map m).roots.toFinset : Set S)).ncard ≤ (2 * B + 1) ^ (d + 1) * d := by
  have key := ncard_biUnion_roots_natDegree_le_coeff_mem_le m d (Finset.Icc (-(B : ℤ)) B)
  have hU : (Finset.Icc (-(B : ℤ)) B).card = 2 * B + 1 := by rw [Int.card_Icc]; omega
  rw [hU] at key
  have hpred : ∀ (f : ℤ[X]) (i : ℕ),
      |f.coeff i| ≤ (B : ℤ) ↔ f.coeff i ∈ Finset.Icc (-(B : ℤ)) B := by
    intro f i; rw [Finset.mem_Icc, abs_le]
  simpa only [hpred] using key

/-- The roots in a domain `S` of all polynomials of degree at most `n` whose `i`-th coefficient
lies in a finite set `s i` form a finite set. -/
theorem finite_biUnion_roots_natDegree_le_coeff_mem_pi (m : R →+* S) (n : ℕ)
    (s : Fin (n + 1) → Finset R) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ n ∧ ∀ i : Fin (n + 1), f.coeff i ∈ s i),
        ((f.map m).roots.toFinset : Set S)).Finite :=
  (finite_setOf_natDegree_le_coeff_mem_pi n s).biUnion fun _ _ ↦ Finset.finite_toSet _

/-- The roots in a domain `S` of all polynomials of degree at most `n` whose `i`-th coefficient
lies in a finite set `s i`, mapped along a ring hom `m : R →+* S`, number at most
`∏ᵢ #(s i) · n`: there are at most `∏ᵢ #(s i)` such polynomials, each with at most `n` roots in
`S`. Unlike `TauCeti.Polynomial.ncard_biUnion_roots_natDegree_le_coeff_mem_le`, the allowed values
may depend on the coefficient, for instance to count roots of monic polynomials. -/
theorem ncard_biUnion_roots_natDegree_le_coeff_mem_pi_le (m : R →+* S) (n : ℕ)
    (s : Fin (n + 1) → Finset R) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ n ∧ ∀ i : Fin (n + 1), f.coeff i ∈ s i),
        ((f.map m).roots.toFinset : Set S)).ncard ≤ (∏ i, (s i).card) * n :=
  (ncard_biUnion_roots_map_le m (finite_setOf_natDegree_le_coeff_mem_pi n s) fun _ hf ↦ hf.1).trans
    (by gcongr; exact ncard_natDegree_le_coeff_mem_pi_le n s)

end TauCeti.Polynomial
