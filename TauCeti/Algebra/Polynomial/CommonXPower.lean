/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Clearing a common power of `X` from a family of polynomials

Given a family of polynomials that is not identically zero, the least exponent occurring
with a nonzero coefficient across the family is the largest power of `X` dividing every member.
Dividing by that power leaves at least one polynomial with nonzero constant term. The family
may be infinite: the least exponent exists by well-ordering of the natural numbers.

This elementary polynomial result is used in three function-field linear-independence arguments:
the valuation criterion of Stichtenoth, Lemma 1.1.7 (`Place.OfValuationSubring`), the place-degree
bound of Proposition 1.1.15 (`Place.Degree`), and the bound on zeros counted with multiplicity
and degree of Proposition 1.3.3 (`Place.Zeros`).

## Main results

* `TauCeti.Polynomial.exists_common_X_pow_factor`: a family of polynomials, not all zero, is
  `X ^ m` times a family in which some member has nonzero constant term.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Lemma 1.1.7 and Propositions 1.1.15 and 1.3.3.
-/

public section

open Polynomial

namespace TauCeti

variable {k : Type*} [Semiring k]

namespace Polynomial

/-- Dividing a family of polynomials, not all zero, by the largest common power of `X`
leaves at least one quotient with nonzero constant term. The exponent is the least index carrying
a nonzero coefficient across the family. -/
theorem exists_common_X_pow_factor {ι : Type*} (s : Set ι) (p : ι → k[X])
    (hne : ∃ i ∈ s, p i ≠ 0) :
    ∃ m, ∃ q : ι → k[X], (∀ i ∈ s, p i = X ^ m * q i) ∧
      ∃ j ∈ s, (q j).coeff 0 ≠ 0 := by
  classical
  have hex : ∃ d, ∃ i ∈ s, (p i).coeff d ≠ 0 := by
    obtain ⟨i, hi, hpi⟩ := hne
    exact ⟨_, i, hi, mem_support_iff.mp (natTrailingDegree_mem_support_of_ne_zero hpi)⟩
  -- Below the least such index every member has zero coefficient, so `X ^ Nat.find hex`
  -- divides every member; the implication form lets `choose` produce a total family.
  have hdvd (i : ι) : ∃ c, i ∈ s → p i = X ^ Nat.find hex * c := by
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := X_pow_dvd_iff.mpr fun d hd ↦
        not_not.mp fun h ↦ Nat.find_min hex hd ⟨i, hi, h⟩
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨0, fun h ↦ (hi h).elim⟩
  choose q hq using hdvd
  obtain ⟨j, hjs, hjm⟩ := Nat.find_spec hex
  exact ⟨_, q, hq, j, hjs, by simpa [hq j hjs, coeff_X_pow_mul'] using hjm⟩

end Polynomial

end TauCeti
