/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Evaluation
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Uniform expansions along monomial curves

Suppose the Taylor coefficients of a polynomial `p` below an exponent `v` in lexicographic
order vanish at every point of a set `S`. An evaluator `c` separates `v` from all larger
exponents by weighted degree. There is then a single polynomial remainder, with coefficients
polynomial in the center `a`, such that on `S`

`p(a + y^c) = y^(weight c v) * (p_{a,v} + y * R(a,y))`.

The coefficient ring can itself be a polynomial ring in a further variable. In that case the
identity retains that variable, even when ordinary specialization vanishes identically. The
least removed Lazard exponent on a set supplies the required vanishing of lower coefficients;
for nonzero `p`, the leading term at every point attaining that minimum is its nonzero Lazard
evaluation.
This uniform identity is used to deform Lazard evaluations into ordinary fibers.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69.
See arXiv:1607.00264v2, Section 5.1, Proposition 5.6, equation (8).
-/

public section

namespace MvPolynomial

open Finsupp

section CommSemiring

variable {σ R : Type*} [LinearOrder σ] [CommSemiring R]

/-- If all Taylor coefficients lexicographically below `v` vanish on `S`, restriction to a
monomial curve with evaluator `c` factors uniformly as `X^(weight c v)` times the sum of the
coefficient at `v` and `X` times a remainder polynomial. The remainder is polynomial in the center
and the curve parameter, not a separately chosen polynomial at each center. No nonvanishing
of the coefficient at `v` is required. -/
theorem exists_aeval_monomialCurve_eq_pow_mul
    (p : MvPolynomial σ R) {S : Set (σ → R)} {V : Set (σ →₀ ℕ)} {v : σ →₀ ℕ}
    {c : σ → ℕ} (hv : v ∈ V) (hc : TauCeti.IsLazardEvaluator V c)
    (hzero : ∀ a ∈ S, ∀ u, toLex u < toLex v → (taylor a p).coeff u = 0) :
    ∃ Q : Polynomial (MvPolynomial σ R), ∀ a ∈ S,
      aeval (monomialCurve a c) p =
        Polynomial.X ^ weight c v *
          (Polynomial.C ((taylor a p).coeff v) + Polynomial.X * Q.map (eval a)) := by
  classical
  -- Keep the center formal so every coefficient of the remainder is polynomial in it.
  let T := taylor (X : σ → MvPolynomial σ R) (map C p)
  let A := T.support.filter (fun u ↦ toLex v < toLex u)
  let Q : Polynomial (MvPolynomial σ R) :=
    ∑ u ∈ A, Polynomial.monomial (weight c u - weight c v - 1) (T.coeff u)
  refine ⟨Q, fun a ha ↦ ?_⟩
  have hcoeff (u) : eval a (T.coeff u) = (taylor a p).coeff u :=
    eval_coeff_taylor_map_C p a u
  have hT : map (eval a) T = taylor a p := by
    ext u
    simpa only [coeff_map] using hcoeff u
  have hsum : aeval (monomialCurve a c) p =
      ∑ u ∈ T.support, Polynomial.monomial (weight c u) ((taylor a p).coeff u) := by
    rw [aeval_monomialCurve, ← hT]
    conv_lhs => rw [T.as_sum]
    simp only [map_sum, map_monomial, aeval_X_pow_left_monomial, hcoeff, hT]
  -- Terms at or below `v` reduce to the single term at `v`, also when it is absent
  -- from the universal support (then its coefficient vanishes at every center).
  have hlow :
      (∑ u ∈ T.support.filter (fun u ↦ ¬ toLex v < toLex u),
        Polynomial.monomial (weight c u) ((taylor a p).coeff u)) =
      Polynomial.monomial (weight c v) ((taylor a p).coeff v) := by
    refine Finset.sum_eq_single v (fun u hu huv ↦ ?_) (fun hmem ↦ ?_)
    · have huv' : toLex u < toLex v :=
        lt_of_le_of_ne (le_of_not_gt (Finset.mem_filter.1 hu).2) (toLex.injective.ne huv)
      simp [hzero a ha u huv']
    · have hvT : v ∉ T.support := by simpa using hmem
      have : (taylor a p).coeff v = 0 := by
        rw [← hcoeff, notMem_support_iff.1 hvT, map_zero]
      simp [this]
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not T.support
    (fun u ↦ toLex v < toLex u), hlow, add_comm]
  rw [mul_add, Polynomial.X_pow_mul_C, Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  -- Every retained exponent has strictly greater weight, so the natural subtractions
  -- in the remainder exponent recover its original weight after multiplication.
  simp only [Q, Polynomial.map_sum, Polynomial.map_monomial, hcoeff,
    Finset.mul_sum, Polynomial.X_mul_monomial, Polynomial.X_pow_mul_monomial]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := hc.weight_lt_weight hv (Finset.mem_filter.1 hu).2
  congr 2
  omega

end CommSemiring

section LazardExponent

variable {R : Type*} [CommRing R] {n : ℕ}

/-- On any nonempty set of base points, choose an evaluator for all removed Lazard exponents
and a prescribed finite set `V` of other exponents, and the lexicographic minimum of the removed
exponents. The polynomial admits a single remainder expansion on the whole set with that
minimum as the common factored exponent. For `R = A[Z]`, the remainder retains `Z` as well as the
center and the monomial-curve parameter. The coefficient at the minimum may vanish at points with
a larger removed exponent. The extra set `V` allows the same curve to detect the valuations of
leading coefficients, trailing coefficients, and discriminants. -/
theorem exists_isLazardEvaluator_aeval_monomialCurve_eq_pow_mul
    (p : MvPolynomial (Fin n) R) {S : Set (Fin n → R)} (hS : S.Nonempty)
    {V : Set (Fin n →₀ ℕ)} (hV : V.Finite) :
    ∃ (c : Fin n → ℕ) (v : Fin n →₀ ℕ) (Q : Polynomial (MvPolynomial (Fin n) R)),
      TauCeti.IsLazardEvaluator ((p.lazardExponent '' S) ∪ V) c ∧
      v ∈ p.lazardExponent '' S ∧
      ∀ a ∈ S, toLex v ≤ toLex (p.lazardExponent a) ∧
        aeval (monomialCurve a c) p =
          Polynomial.X ^ weight c v *
            (Polynomial.C ((taylor a p).coeff v) + Polynomial.X * Q.map (eval a)) := by
  have hfinite : (p.lazardExponent '' S).Finite :=
    (finite_range_lazardExponent p).subset (Set.image_subset_range _ _)
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image _ toLex hfinite (hS.image _)
  obtain ⟨c, hc⟩ := TauCeti.exists_isLazardEvaluator (hfinite.union hV)
  obtain ⟨Q, hQ⟩ := exists_aeval_monomialCurve_eq_pow_mul p (Set.mem_union_left V hv) hc
    (fun a ha u hu ↦
      coeff_taylor_eq_zero_of_lt_lazardExponent
        (hu.trans_le (hmin _ (Set.mem_image_of_mem _ ha))))
  exact ⟨c, v, Q, hc, hv, fun a ha ↦ ⟨hmin _ (Set.mem_image_of_mem _ ha), hQ a ha⟩⟩

end LazardExponent

end MvPolynomial
