/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Multiset

/-!
# Weights of finitely supported functions

If every variable has weight at most `c`, then the weight of a monomial `f : σ →₀ ℕ` is at most
`degree f • c`. With `c = -1` over `ℤ`, this says that a monomial all of whose variables have
negative weight has weight at most minus its total degree, which is how negatively graded
variables bound the degree of elements of powers of the ideal of the variables.

The weight of a multiset multiplicity function is the sum of the weights of its entries.

Weights also respect scaling of the weight vector and decompose into contributions before, at,
and after a chosen coordinate in a linear order. These identities support comparisons between
lexicographic order and weighted degree.

## Main results

* `Finsupp.weight_toFinsupp`: multiset multiplicities recover the sum of entry weights.
* `Finsupp.weight_le_degree_nsmul`: if `w s ≤ c` for all `s`, then `weight w f ≤ degree f • c`.
* `Finsupp.weight_filter_gt_add_smul_add_weight_filter_lt`: split a weight at a coordinate.
* `Finsupp.weight_smul_left`: scaling the weight vector scales the weight.
-/

public section

namespace Finsupp

/-- The weight of the multiplicity function of a multiset is the sum of its entry weights. -/
@[simp]
theorem weight_toFinsupp {σ M : Type*} [DecidableEq σ] [AddCommMonoid M]
    (w : σ → M) (s : Multiset σ) :
    weight w s.toFinsupp = (s.map w).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, map_add, weight_single]
    simpa using congrArg (w i + ·) ih

end Finsupp

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]

/-- If every variable has weight at most `c`, then the weight of `f` is at most its degree times
`c`. -/
theorem weight_le_degree_nsmul (f : σ →₀ ℕ) {w : σ → M} {c : M} (hw : ∀ s, w s ≤ c) :
    weight w f ≤ degree f • c := by
  rw [weight_apply, degree_apply, Finsupp.sum, ← Finset.sum_nsmul_assoc]
  gcongr with s
  exact hw s

end Finsupp

namespace Finsupp

variable {σ M : Type*} [LinearOrder σ]

/-- A finitely supported function splits into its values before `i`, at `i`, and after `i`. -/
theorem filter_gt_add_single_add_filter_lt [AddZeroClass M] (f : σ →₀ M) (i : σ) :
    f.filter (· < i) + single i (f i) + f.filter (i < ·) = f := by
  ext j
  rcases lt_trichotomy j i with hj | rfl | hj
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne]
  · simp
  · simp [hj, hj.not_gt, single_eq_of_ne hj.ne']

/-- The `c`-weight of an exponent `w` splits into the weights of its coordinates before `i`, at
`i`, and after `i`. -/
theorem weight_filter_gt_add_smul_add_weight_filter_lt [AddCommMonoid M] (c : σ → M)
    (w : σ →₀ ℕ) (i : σ) :
    weight c (w.filter (· < i)) + w i • c i + weight c (w.filter (i < ·)) = weight c w := by
  conv_rhs => rw [← filter_gt_add_single_add_filter_lt w i]
  rw [map_add, map_add, weight_single]

omit [LinearOrder σ] in
/-- Scaling the weight vector scales the weight. -/
theorem weight_smul_left {R S : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid S]
    [DistribMulAction S M] [SMulCommClass R S M] (s : S) (c : σ → M) (w : σ →₀ R) :
    weight (s • c) w = s • weight c w := by
  simp only [weight_apply, smul_sum, Pi.smul_apply]
  exact sum_congr fun _ _ ↦ smul_comm _ s _

end Finsupp
