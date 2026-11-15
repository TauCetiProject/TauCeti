/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.RootCount
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Semialgebraic root loci of polynomial families

Let `P k` be a finite family of univariate polynomials whose coefficients are multivariate
polynomials in a parameter. On a semialgebraic set where every specialization is nonzero, the
distinct roots of the family together are the distinct roots of the product of its members. The
uniform root-count descriptions for one polynomial therefore give semialgebraic descriptions of
the shared ordered root list of the family.

This file proves that the locus where the distinguished coordinate is the `i`-th root of some
member, and the locus where it lies in the `j`-th complementary interval of the combined root
list, are semialgebraic. Common roots of several members occur only once, because the combined
root set is a `Finset.biUnion`. Empty families and families without real roots are included.

## Main declarations

* `TauCeti.IsSemialgebraic.setOf_mem_biUnion_roots_card_lt`: the locus of the `i`-th distinct root
  of a finite family, wherever it exists, is semialgebraic on a base where all members are active.
* `TauCeti.IsSemialgebraic.setOf_not_mem_biUnion_roots_card_lt`: the `j`-th region complementary to
  the combined roots is semialgebraic on such a base.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapters 4, 5, and 10.
-/

public section

open Polynomial Set

namespace TauCeti

variable {R ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  {n : ℕ}

/-- **The ordered root loci of a finite family are semialgebraic.** Let `P k` be a finite family
of polynomial families over `R ^ n`. On a semialgebraic base `S` where every member specializes
to a nonzero polynomial, the points whose distinguished coordinate is a root of some member and
has exactly `i` distinct roots of the family below it form a semialgebraic set.

The union counts a root shared by several members only once. For an empty family the set is
empty. -/
theorem IsSemialgebraic.setOf_mem_biUnion_roots_card_lt {S : Set (Fin n → R)}
    (hS : IsSemialgebraic S) (s : Finset ι) (P : ι → (MvPolynomial (Fin n) R)[X])
    (hP : ∀ k ∈ s, ∀ x ∈ S, (P k).map (MvPolynomial.eval x) ≠ 0) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R | Fin.tail y ∈ S ∧
      y 0 ∈ s.biUnion (fun k ↦ ((P k).map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
      {r ∈ s.biUnion (fun k ↦ ((P k).map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
        r < y 0}.card = i} := by
  classical
  let Q : (MvPolynomial (Fin n) R)[X] := s.prod P
  have hroot := hS.preimage_tail.inter (isSemialgebraic_setOf_isRoot_card_roots_lt Q i)
  convert hroot using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  by_cases hy : Fin.tail y ∈ S
  · have hprod : Q.map (MvPolynomial.eval (Fin.tail y)) ≠ 0 := by
      simpa only [Q, Polynomial.map_prod] using
        (Finset.prod_ne_zero_iff.mpr fun k hk ↦ hP k hk _ hy)
    have hroots : (Q.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset =
        s.biUnion (fun k ↦ ((P k).map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) := by
      simpa only [Q, Polynomial.map_prod] using roots_prod_toFinset s _ fun k hk ↦ hP k hk _ hy
    simp only [hy, true_and, ← hroots, Multiset.mem_toFinset, mem_roots hprod]
  · simp only [hy, false_and]

/-- **The sectors of the combined root list are semialgebraic.** Let `P k` be a finite family of
polynomial families over `R ^ n`. On a semialgebraic base `S` where every member specializes to a
nonzero polynomial, the points whose distinguished coordinate is not a root of any member and
has exactly `j` distinct roots of the family below it form a semialgebraic set.

The regions are numbered from below. For an empty family, or for a family without real roots,
the region with index zero is the whole cylinder over `S` and all other regions are empty. -/
theorem IsSemialgebraic.setOf_not_mem_biUnion_roots_card_lt {S : Set (Fin n → R)}
    (hS : IsSemialgebraic S) (s : Finset ι) (P : ι → (MvPolynomial (Fin n) R)[X])
    (hP : ∀ k ∈ s, ∀ x ∈ S, (P k).map (MvPolynomial.eval x) ≠ 0) (j : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R | Fin.tail y ∈ S ∧
      y 0 ∉ s.biUnion (fun k ↦ ((P k).map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
      {r ∈ s.biUnion (fun k ↦ ((P k).map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
        r < y 0}.card = j} := by
  classical
  let Q : (MvPolynomial (Fin n) R)[X] := s.prod P
  have hsector := hS.preimage_tail.inter (isSemialgebraic_setOf_not_isRoot_card_roots_lt Q j)
  convert hsector using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  by_cases hy : Fin.tail y ∈ S
  · have hprod : Q.map (MvPolynomial.eval (Fin.tail y)) ≠ 0 := by
      simpa only [Q, Polynomial.map_prod] using
        (Finset.prod_ne_zero_iff.mpr fun k hk ↦ hP k hk _ hy)
    have hroots : (Q.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset =
        s.biUnion (fun k ↦ ((P k).map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) := by
      simpa only [Q, Polynomial.map_prod] using roots_prod_toFinset s _ fun k hk ↦ hP k hk _ hy
    simp only [hy, true_and, ← hroots, Multiset.mem_toFinset, mem_roots hprod]
  · simp only [hy, false_and]

end TauCeti
