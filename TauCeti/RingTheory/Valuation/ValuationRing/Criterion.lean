/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Kaplansky's criterion for valuation rings

Let `R` be an integrally closed local domain with fraction field `K`. If `x ∈ K` is a root of a
polynomial over `R` with some unit coefficient, then `x ∈ R` or `x⁻¹ ∈ R`. So `R` is a valuation
ring as soon as every element of `K` is such a root.

Induct on the degree. If the leading coefficient `c` is a unit, `x` is integral, hence in `R`.
Otherwise `c x` is integral, so `c x = a ∈ R`. If `a` is a unit then `x⁻¹ = c a⁻¹ ∈ R`. If not,
replacing the top two terms `c X ^ (m + 1) + c' X ^ m` by `(c' + a) X ^ m` gives a relation of
smaller degree that still has a unit coefficient, as `R` is local.

## Main results

* `IsIntegrallyClosed.isInteger_or_isInteger_inv_of_aeval_eq_zero`: in an integrally closed local
  domain `R`, a root of a polynomial over `R` with a unit coefficient, or its inverse, lies in `R`.
* `ValuationRing.of_forall_exists_isUnit_coeff_aeval_eq_zero`: an integrally closed local domain
  in whose fraction field every element is such a root is a valuation ring.

## References

* [I. Kaplansky, *Commutative Rings*], Theorem 67, for the criterion through roots of polynomials
  with a unit coefficient.
-/

public section

open Polynomial

variable {R K : Type*} [CommRing R] [IsLocalRing R] [IsIntegrallyClosed R] [Field K]
  [Algebra R K] [IsFractionRing R K]

namespace IsIntegrallyClosed

/-- **Kaplansky's criterion.** In an integrally closed local domain `R` with fraction field `K`,
if `x ∈ K` is a root of a polynomial over `R` one of whose coefficients is a unit, then `x` or
`x⁻¹` lies in `R`. -/
theorem isInteger_or_isInteger_inv_of_aeval_eq_zero {x : K} {p : R[X]} {i : ℕ}
    (hi : IsUnit (p.coeff i)) (hp : aeval x p = 0) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p i with
  | ind n ih =>
  -- `c • x` is integral over `R`, for `c` the leading coefficient, so it is some `a ∈ R`
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_leadingCoeff_smul p x hp)
  rw [Algebra.smul_def] at ha
  by_cases hc : IsUnit p.leadingCoeff
  · refine Or.inl ⟨hc.unit⁻¹ * a, ?_⟩
    have hinv := congrArg (algebraMap R K) hc.val_inv_mul
    simp only [map_mul, map_one] at hinv ⊢
    linear_combination algebraMap R K ↑hc.unit⁻¹ * ha + x * hinv
  by_cases haU : IsUnit a
  · refine Or.inr ⟨p.leadingCoeff * haU.unit⁻¹, eq_inv_of_mul_eq_one_left ?_⟩
    have hinv := congrArg (algebraMap R K) haU.mul_val_inv
    simp only [map_mul, map_one] at hinv ⊢
    linear_combination hinv - algebraMap R K ↑haU.unit⁻¹ * ha
  -- the unit coefficient sits below the top degree `n = m + 1`
  have hin : i < n := by
    rcases lt_trichotomy i n with h | rfl | h
    · exact h
    · rw [← hn, coeff_natDegree] at hi
      exact absurd hi hc
    · rw [coeff_eq_zero_of_natDegree_lt (hn ▸ h)] at hi
      exact absurd hi not_isUnit_zero
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one_of_ne_zero (by omega)
  -- replace `c X ^ (m + 1)` by `a X ^ m`
  set q := p.eraseLead + C a * X ^ m
  have hq : q.natDegree < m + 1 := by
    refine Nat.lt_succ_of_le (natDegree_add_le_of_degree_le ?_ ?_)
    · exact (eraseLead_natDegree_le p).trans (by omega)
    · exact natDegree_C_mul_X_pow_le a m
  refine ih _ hq (p := q) (i := i) ?_ ?_ rfl
  · have hcoeff : q.coeff i = p.coeff i + if i = m then a else 0 := by
      rw [coeff_add, eraseLead_coeff_of_ne _ (by omega), coeff_C_mul_X_pow]
    rw [hcoeff]
    split_ifs
    · -- a unit plus a nonunit is a unit in a local ring
      refine (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := p.coeff i + a) (b := -a)
        (by rwa [add_neg_cancel_right])).resolve_right ?_
      rwa [IsUnit.neg_iff]
    · rwa [add_zero]
  · simp only [q, ← self_sub_monomial_natDegree_leadingCoeff, hn, map_add, map_sub, map_mul,
      aeval_monomial, aeval_C, aeval_X_pow]
    linear_combination hp + x ^ m * ha

end IsIntegrallyClosed

namespace ValuationRing

/-- **Kaplansky's criterion for valuation rings.** An integrally closed local domain `R` is a
valuation ring if every element of its fraction field is a root of a polynomial over `R` with a
unit coefficient. -/
theorem of_forall_exists_isUnit_coeff_aeval_eq_zero [IsDomain R]
    (h : ∀ x : K, ∃ p : R[X], (∃ i, IsUnit (p.coeff i)) ∧ aeval x p = 0) : ValuationRing R :=
  (iff_isInteger_or_isInteger R K).mpr fun x ↦ by
    obtain ⟨p, ⟨i, hi⟩, hp⟩ := h x
    exact IsIntegrallyClosed.isInteger_or_isInteger_inv_of_aeval_eq_zero hi hp

end ValuationRing
