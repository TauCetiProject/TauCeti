/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.IntegralNewton
import Mathlib.Tactic.Ring

/-!
# Newton identities for linear forms on geometric powers

For an algebra element satisfying `y * y = l • y`, integral Newton polynomials evaluated at
`τ (y ^ i)` are falling products in `τ y`. Vanishing in degree `d + 1` forces `τ y = j * l`
for a natural number `j ≤ d`. The cases `l = 1` and `l = 0` give bounded natural values on
idempotents and vanishing on square-zero elements, respectively.

## Main results

* `LinearMap.eval_integralNewtonPolynomial_of_geometric` gives the falling-product formula.
* `LinearMap.exists_nat_mul_of_integralNewtonPolynomial_eq_zero` extracts a bounded multiplicity.

## Provenance

These lemmas adapt `New.eval_newtonPoly_eq_pow_mul_prod_of_pow_succ_eq_smul` and
`New.exists_eq_nat_mul_of_eval_newtonPoly_eq_zero`
in `src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The commutative-ring formulation and quadratic hypothesis
are new here.

## References

* R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996),
  571–586. https://www.math.ucla.edu/~rouquier/papers.html
-/

public section

open MvPolynomial Finset TauCeti

namespace LinearMap

variable {k : Type*} [CommRing k]

/-- Let `τ` be a linear form on a `k`-algebra `A` and `y : A` with `y * y = l • y`.
At the values `τ (y ^ i)`, the Newton polynomial `integralNewtonPolynomial (j + 1) (m + 1)`
takes the value `l ^ m` times the product of `τ y - i * l` over `i ≤ j`. -/
lemma eval_integralNewtonPolynomial_of_geometric
    {A : Type*} [Semiring A] [Algebra k A]
    (τ : A →ₗ[k] k) {l : k} {y : A} (hy : y * y = l • y) (j : ℕ) :
    ∀ m : ℕ, eval (fun i : ℕ ↦ τ (y ^ i)) (integralNewtonPolynomial (j + 1) (m + 1)) =
      l ^ m * ∏ i ∈ Finset.range (j + 1), (τ y - i * l) := by
  have hpow (m : ℕ) : y ^ (m + 1) = l ^ m • y := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, smul_mul_assoc, hy, smul_smul, ← pow_succ]
  have htrace (m : ℕ) : τ (y ^ (m + 1)) = l ^ m * τ y := by
    rw [hpow, map_smul, smul_eq_mul]
  induction j with
  | zero => simp [integralNewtonPolynomial_succ, integralNewtonPolynomial_zero, htrace]
  | succ j ih =>
    intro m
    simp only [integralNewtonPolynomial_succ (j + 1), map_sub, map_mul, map_natCast,
      eval_X, ih, htrace, pow_zero, one_mul, nsmul_eq_mul]
    rw [prod_range_succ _ (j + 1)]
    ring

/-- Let `τ` be a linear form on a `k`-algebra `A` and `y : A` with `y * y = l • y`.
If `integralNewtonPolynomial (d + 1) 1` vanishes at `i ↦ τ (y ^ i)`, then
`τ y = j * l` for some natural number `j ≤ d`. -/
lemma exists_nat_mul_of_integralNewtonPolynomial_eq_zero
    [NoZeroDivisors k] {A : Type*} [Semiring A] [Algebra k A]
    (τ : A →ₗ[k] k) {l : k} {y : A} (hy : y * y = l • y) {d : ℕ}
    (h_zero : eval (fun i : ℕ ↦ τ (y ^ i)) (integralNewtonPolynomial (d + 1) 1) = 0) :
    ∃ j : ℕ, j ≤ d ∧ τ y = j * l := by
  rcases subsingleton_or_nontrivial k with h | h
  · exact ⟨0, Nat.zero_le d, Subsingleton.elim _ _⟩
  -- at `m = 0` the Newton polynomial is the product of the `τ y - i * l`, `i ≤ d`, so one vanishes
  have h_prod : ∏ i ∈ Finset.range (d + 1), (τ y - i * l) = 0 := by
    simpa using (τ.eval_integralNewtonPolynomial_of_geometric hy d 0).symm.trans h_zero
  obtain ⟨i, hi_mem, hi⟩ := prod_eq_zero_iff.mp h_prod
  exact ⟨i, Nat.le_of_lt_succ (Finset.mem_range.mp hi_mem), sub_eq_zero.mp hi⟩

end LinearMap
