/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Clearing a common power of `X` from a family of polynomials

Given a family of polynomials that is not identically zero, the least exponent occurring
with a nonzero coefficient across the family is the largest power of `X` dividing every member.
Dividing by that power leaves at least one polynomial with nonzero constant term. The family
may be infinite: the least exponent exists by well-ordering of the natural numbers.

This elementary polynomial result is used, through
`TauCeti.Polynomial.exists_polynomial_relation_of_sum_smul_eq_zero`, in three function-field
linear-independence arguments:
the valuation criterion of Stichtenoth, Lemma 1.1.7 (`Place.OfValuationSubring`), the place-degree
bound of Proposition 1.1.15 (`Place.Degree`), and the bound on zeros counted with multiplicity
and degree of Proposition 1.3.3 (`Place.Zeros`).

## Main results

* `TauCeti.Polynomial.exists_common_X_pow_factor`: a family of polynomials, not all zero, is
  `X ^ m` times a family in which some member has nonzero constant term.
* `TauCeti.Polynomial.exists_polynomial_relation_of_sum_smul_eq_zero`: a nontrivial relation over
  `R[x]` between elements of a domain yields one with polynomial coefficients over `R`, one of which
  has nonzero constant term.

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

/-- **Removing a common power of `x` from a nontrivial relation over `R[x]`.** Let `x ≠ 0` in a
domain `A` over `R`. If elements `v i` of `A` satisfy a relation `∑ i ∈ s, g i • v i = 0` with
coefficients `g i` in `R[x]`, not all zero, then they satisfy
`∑ i ∈ s, q_i(x) * v i = 0` for polynomials `q i` over `R`, one of which, for an index in `s`, has
nonzero constant term. -/
theorem exists_polynomial_relation_of_sum_smul_eq_zero {R A : Type*} [CommSemiring R]
    [CommSemiring A] [IsDomain A] [Algebra R A] {x : A} (hx0 : x ≠ 0) {ι : Type*} (s : Finset ι)
    (v : ι → A) (g : ι → Algebra.adjoin R ({x} : Set A)) (hsum : ∑ i ∈ s, g i • v i = 0)
    {i₁ : ι} (hi₁ : i₁ ∈ s) (hg0 : g i₁ ≠ 0) :
    ∃ q : ι → R[X], ∑ i ∈ s, aeval x (q i) * v i = 0 ∧ ∃ i₂ ∈ s, (q i₂).coeff 0 ≠ 0 := by
  have hrange : ∀ y : A, y ∈ Algebra.adjoin R ({x} : Set A) → ∃ p : R[X], aeval x p = y := by
    intro y hy
    rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hy
  choose p hp using fun i ↦ hrange (g i : A) (g i).2
  have hpne : p i₁ ≠ 0 := by
    intro h
    exact hg0 (Subtype.ext (by simpa [h] using (hp i₁).symm))
  obtain ⟨m, q, hfactor, i₂, hi₂, hq₂⟩ :=
    exists_common_X_pow_factor (s : Set ι) p ⟨i₁, hi₁, hpne⟩
  refine ⟨q, ?_, i₂, hi₂, hq₂⟩
  refine mul_left_cancel₀ (pow_ne_zero m hx0) ?_
  rw [Finset.mul_sum, mul_zero, ← hsum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Algebra.smul_def, Subalgebra.algebraMap_apply, ← hp i, hfactor i hi, map_mul, map_pow,
    aeval_X]
  ring

end Polynomial

end TauCeti
