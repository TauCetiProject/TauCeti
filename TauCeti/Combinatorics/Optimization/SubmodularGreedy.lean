/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Lattice.Submodular
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Greedy maximization of a monotone submodular set function

Let `f` be a monotone submodular function on the finite subsets of a type, and let
`s 0, s 1, ..., s l` be a sequence of finite sets in which each `s (i + 1)` is `s i` with one
element added, chosen so that the value of `f` after the addition is as large as possible. Then
for every finite set `T` with at most `k` elements,
`f T - f (s l) ≤ (1 - 1 / k) ^ l * (f T - f (s 0))`. For a greedy sequence that starts at the
empty set, after `k` steps the gap `f T - f (s k)` is at most `1 / e` times the gap
`f T - f ∅`, for every set `T` with at most `k` elements.

The proof bounds one step at a time: monotonicity and the marginal bound
`TauCeti.IsSubmodular.sub_le_sum_insert_sub` show that the increase of `f` at a greedy step is at
least the fraction `1 / k` of the remaining gap to `f T`.

## Main declarations

* `TauCeti.IsSubmodular.sub_le_pow_mul_sub_of_greedy`: the bound of Nemhauser, Wolsey and Fisher,
  with the factor `(1 - 1 / k) ^ l`.
* `TauCeti.IsSubmodular.sub_le_exp_mul_sub_of_greedy`: the same bound with the factor
  `Real.exp (-l / k)`.
* `TauCeti.IsSubmodular.one_sub_exp_neg_one_mul_le_of_greedy`: for a nonnegative `f` and `l = k`,
  the greedy set has at least the fraction `1 - 1 / e` of the value of every set with at most `k`
  elements.

## References

* G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, *An analysis of approximations for maximizing
  submodular set functions I*, Mathematical Programming 14 (1978), 265-294.
* A. Krause and D. Golovin, *Submodular function maximization*, Theorem 1.5.
* F. Bach, *Learning with submodular functions: a convex optimization perspective*,
  Proposition 11.1.
-/

public section

namespace TauCeti

namespace IsSubmodular

variable {α K : Type*} [DecidableEq α]

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One greedy step: if `insert x S` has the greatest value of `f` among the sets `insert y S`,
then the gap `f T - f (insert x S)` is at most `1 - 1 / k` times the gap `f T - f S`, for every
set `T` with at most `k` elements. -/
private theorem sub_le_one_sub_one_div_mul_sub {f : Finset α → K} (hf : IsSubmodular f)
    (hmono : Monotone f) {S T : Finset α} {k : ℕ} (hT : T.card ≤ k) {x : α}
    (hx : ∀ y, f (insert y S) ≤ f (insert x S)) :
    f T - f (insert x S) ≤ (1 - 1 / (k : K)) * (f T - f S) := by
  have hΔ : 0 ≤ f (insert x S) - f S := sub_nonneg.mpr (hmono (Finset.subset_insert x S))
  have hk : f T - f S ≤ k * (f (insert x S) - f S) :=
    calc f T - f S ≤ f (S ∪ T) - f S := sub_le_sub_right (hmono Finset.subset_union_right) _
      _ ≤ ∑ y ∈ T \ S, (f (insert y S) - f S) := hf.sub_le_sum_insert_sub S T
      _ ≤ (T \ S).card • (f (insert x S) - f S) :=
        Finset.sum_le_card_nsmul _ _ _ fun y _ ↦ sub_le_sub_right (hx y) _
      _ = ((T \ S).card : K) * (f (insert x S) - f S) := nsmul_eq_mul _ _
      _ ≤ k * (f (insert x S) - f S) := by
        gcongr
        exact (Finset.card_le_card Finset.sdiff_subset).trans hT
  have hdiv : 1 / (k : K) * (f T - f S) ≤ f (insert x S) - f S := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simpa using hΔ
    · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by exact_mod_cast hpos), mul_comm]
      exact hk
  linarith

/-- The bound of Nemhauser, Wolsey and Fisher for greedy maximization. Let `f` be a monotone
submodular set function and let `s 0, ..., s l` be a sequence of finite sets in which each
`s (i + 1)` is `insert x (s i)` for an `x` that gives the greatest value of `f` among the sets
`insert y (s i)`. Then for every finite set `T` with at most `k` elements,
`f T - f (s l) ≤ (1 - 1 / k) ^ l * (f T - f (s 0))`. For `k = 0` the factor is `1`, because
division by zero gives zero. -/
theorem sub_le_pow_mul_sub_of_greedy {f : Finset α → K} (hf : IsSubmodular f)
    (hmono : Monotone f) (s : ℕ → Finset α) (l : ℕ)
    (hs : ∀ i < l, ∃ x, s (i + 1) = insert x (s i) ∧
      ∀ y, f (insert y (s i)) ≤ f (insert x (s i)))
    {k : ℕ} {T : Finset α} (hT : T.card ≤ k) :
    f T - f (s l) ≤ (1 - 1 / (k : K)) ^ l * (f T - f (s 0)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨x, hsx, hx⟩ := hs l l.lt_succ_self
    rw [hsx, pow_succ', mul_assoc]
    exact (sub_le_one_sub_one_div_mul_sub hf hmono hT hx).trans <|
      mul_le_mul_of_nonneg_left (ih fun i hi ↦ hs i (hi.trans l.lt_succ_self))
        (Nat.one_sub_one_div_cast_nonneg k)

/-- The greedy bound with the gap measured from `f ∅`, which is nonnegative by monotonicity. -/
private theorem sub_le_pow_mul_sub_empty_of_greedy {f : Finset α → K} (hf : IsSubmodular f)
    (hmono : Monotone f) (s : ℕ → Finset α) (l : ℕ)
    (hs : ∀ i < l, ∃ x, s (i + 1) = insert x (s i) ∧
      ∀ y, f (insert y (s i)) ≤ f (insert x (s i)))
    {k : ℕ} {T : Finset α} (hT : T.card ≤ k) :
    f T - f (s l) ≤ (1 - 1 / (k : K)) ^ l * (f T - f ∅) :=
  (hf.sub_le_pow_mul_sub_of_greedy hmono s l hs hT).trans <|
    mul_le_mul_of_nonneg_left (sub_le_sub_left (hmono (Finset.empty_subset _)) _)
      (pow_nonneg (Nat.one_sub_one_div_cast_nonneg k) l)

end Field

/-- The bound of Nemhauser, Wolsey and Fisher with an exponential factor. Let `f` be a monotone
submodular real set function and let `s 0, ..., s l` be built by adding at each step an element that
gives the greatest value of `f`. Then for every finite set `T` with at most `k` elements,
`f T - f (s l) ≤ Real.exp (-l / k) * (f T - f ∅)`. -/
theorem sub_le_exp_mul_sub_of_greedy {f : Finset α → ℝ} (hf : IsSubmodular f)
    (hmono : Monotone f) (s : ℕ → Finset α) (l : ℕ)
    (hs : ∀ i < l, ∃ x, s (i + 1) = insert x (s i) ∧
      ∀ y, f (insert y (s i)) ≤ f (insert x (s i)))
    {k : ℕ} {T : Finset α} (hT : T.card ≤ k) :
    f T - f (s l) ≤ Real.exp (-l / k) * (f T - f ∅) := by
  have hpow : (1 - 1 / (k : ℝ)) ^ l ≤ Real.exp (-l / k) := by
    rw [show -(l : ℝ) / k = l * -(1 / k) by ring, Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (Nat.one_sub_one_div_cast_nonneg k) (Real.one_sub_le_exp_neg _) l
  exact (sub_le_pow_mul_sub_empty_of_greedy hf hmono s l hs hT).trans <|
    mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr (hmono (Finset.empty_subset _)))

/-- The approximation ratio `1 - 1 / e` of greedy maximization. Let `f` be a monotone submodular
real set function with `0 ≤ f ∅`, and let `s 0, ..., s k` be built by adding at each step an element
that gives the greatest value of `f`. Then `(1 - Real.exp (-1)) * f T ≤ f (s k)` for every finite
set `T` with at most `k` elements. -/
theorem one_sub_exp_neg_one_mul_le_of_greedy {f : Finset α → ℝ} (hf : IsSubmodular f)
    (hmono : Monotone f) (h₀ : 0 ≤ f ∅) (s : ℕ → Finset α) (k : ℕ)
    (hs : ∀ i < k, ∃ x, s (i + 1) = insert x (s i) ∧
      ∀ y, f (insert y (s i)) ≤ f (insert x (s i)))
    {T : Finset α} (hT : T.card ≤ k) :
    (1 - Real.exp (-1)) * f T ≤ f (s k) := by
  have hexp := Real.exp_pos (-1)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hT)]
    nlinarith [hmono (Finset.empty_subset (s 0))]
  have hpow : (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-1) :=
    Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hpos)
  nlinarith [sub_le_pow_mul_sub_empty_of_greedy hf hmono s k hs hT,
    mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr (hmono (Finset.empty_subset T)))]

end IsSubmodular

end TauCeti
