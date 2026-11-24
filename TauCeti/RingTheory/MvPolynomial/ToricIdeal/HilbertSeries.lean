/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import TauCeti.Data.Finsupp.HilbertSeries
public import TauCeti.RingTheory.MvPolynomial.ToricIdeal.HilbertFunction

/-!
# Hilbert series of semigroup algebras generated in degree one

Let `a : ι → M` be a finite family of `d` elements of an additive commutative monoid, generating
the submonoid `S`, and let `deg : M →+ ℕ` be a degree with `deg (a i) = 1` for every `i`. The
Hilbert function of the semigroup algebra `k[S]` counts the elements of `S` of each degree `n`
(`AddMonoidAlgebra.finrank_gradeBy`). This file proves that its Hilbert series
`∑ₙ #{s ∈ S | deg s = n} Tⁿ` is rational, of the form `p / (1 - T)ᵈ` for a polynomial `p`.
Consequently, in characteristic zero, the number of elements of `S` of degree `n` is the value at
`n` of Mathlib's `Polynomial.hilbertPoly p d` for every `n` greater than the degree of `p`.

The counts are those of the standard monomials of the toric ideal of `a` for any monomial order
(`MonomialOrder.card_standardMonomials_toricIdeal`), as the weight of `X^c` is its total degree.
The standard monomials form a lower set of exponents, whose counting series is rational
(`IsLowerSet.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow`). The counts are integers,
whatever the coefficients of the semigroup algebra; the series may take coefficients in any
commutative ring.

## Main results

* `TauCeti.exists_mk_card_closure_eq_mul_invOneSubPow`: the series counting the elements of `S` by
  degree is `p / (1 - T)ᵈ`.
* `TauCeti.exists_mk_finrank_gradeBy_eq_mul_invOneSubPow`: the Hilbert series of `k[S]`, formed
  from the ranks of its homogeneous components, is `p / (1 - T)ᵈ`.
* `TauCeti.exists_card_closure_eq_hilbertPoly_eval`: with coefficients in a field of characteristic
  zero, the number of elements of `S` of degree `n` is `(hilbertPoly p d).eval n` for every `n`
  greater than the degree of `p`.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 4.
* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, 4th ed., Springer, 2015,
  Chapter 9, §3.
-/

public section

open AddMonoidAlgebra PowerSeries
open scoped Polynomial

namespace TauCeti

variable {ι M : Type*} [Fintype ι] [AddCommMonoid M]

variable (R : Type*) [CommRing R] in
/-- **Rationality of the Hilbert series of a semigroup generated in degree one.** If
`deg (a i) = 1` for each of the `d` generators `a i` of the submonoid `S`, the series counting the
elements of `S` by degree is `p / (1 - T)ᵈ` for a polynomial `p`. -/
theorem exists_mk_card_closure_eq_mul_invOneSubPow (a : ι → M) (deg : M →+ ℕ)
    (ha : ∀ i, deg (a i) = 1) :
    ∃ p : R[X], PowerSeries.mk (fun n ↦
      (Nat.card {s : AddSubmonoid.closure (Set.range a) // deg s = n} : R)) =
        p * invOneSubPow R (Fintype.card ι) := by
  classical
  -- Any monomial order will do; choose the lexicographic order for some ordering of `ι`.
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  let m : MonomialOrder ι := MonomialOrder.lex
  obtain ⟨p, hp⟩ := IsLowerSet.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow R
    (m.isLowerSet_standardMonomials (toricIdeal ℚ a))
  refine ⟨p, Eq.trans ?_ hp⟩
  ext n
  have hw : Finsupp.weight (deg ∘ a) = Finsupp.degree := by
    rw [Finsupp.degree_eq_weight_one]
    simp only [Function.comp_def, ha]
  rw [coeff_mk, coeff_mk, ← m.card_standardMonomials_toricIdeal (k := ℚ) a deg n, hw,
    Nat.card_coe_set_eq]

variable (k : Type*) [CommSemiring k] [StrongRankCondition k] (R : Type*) [CommRing R] in
/-- **The Hilbert series of a semigroup algebra generated in degree one.** If `deg (a i) = 1` for
each of the `d` generators `a i` of the submonoid `S`, the series formed from the ranks of the
homogeneous components of `k[S]` is `p / (1 - T)ᵈ` for a polynomial `p`. -/
theorem exists_mk_finrank_gradeBy_eq_mul_invOneSubPow (a : ι → M) (deg : M →+ ℕ)
    (ha : ∀ i, deg (a i) = 1) :
    ∃ p : R[X], PowerSeries.mk (fun n ↦ (Module.finrank k
      (gradeBy k (deg ∘ Subtype.val : AddSubmonoid.closure (Set.range a) → ℕ) n) : R)) =
        p * invOneSubPow R (Fintype.card ι) := by
  simp_rw [finrank_gradeBy]
  exact exists_mk_card_closure_eq_mul_invOneSubPow R a deg ha

variable (F : Type*) [Field F] [CharZero F] in
/-- **The Hilbert polynomial of a semigroup generated in degree one.** If `deg (a i) = 1` for each
of the `d` generators `a i` of the submonoid `S`, its counting series is `p / (1 - T)ᵈ` for a
polynomial `p` over a field `F` of characteristic zero, and the number of elements of `S` of
degree `n` is the value at `n` of `Polynomial.hilbertPoly p d` whenever `n` exceeds the degree
of `p`. -/
theorem exists_card_closure_eq_hilbertPoly_eval (a : ι → M) (deg : M →+ ℕ)
    (ha : ∀ i, deg (a i) = 1) :
    ∃ p : F[X], PowerSeries.mk (fun n ↦
        (Nat.card {s : AddSubmonoid.closure (Set.range a) // deg s = n} : F)) =
          p * invOneSubPow F (Fintype.card ι) ∧
      ∀ n, p.natDegree < n →
        (Nat.card {s : AddSubmonoid.closure (Set.range a) // deg s = n} : F) =
          (Polynomial.hilbertPoly p (Fintype.card ι)).eval (n : F) := by
  obtain ⟨p, hp⟩ := exists_mk_card_closure_eq_mul_invOneSubPow F a deg ha
  refine ⟨p, hp, fun n hn ↦ ?_⟩
  rw [← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn, ← hp, coeff_mk]

end TauCeti
