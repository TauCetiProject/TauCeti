/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Sums and products over `Fin n`

Successive differences along a finite sequence sum to the difference of its endpoints,
including the empty edge sequence. Reversing every difference reverses the endpoint difference.
The equivalence omitting the last index also reindexes sums by the preceding indices, and a
filtered product over `Fin (n + 1)` splits off its first index; when two such products agree and
so do their first factors, the products over the remaining indices agree.

Along a divisibility chain `d₀ ∣ d₁ ∣ ⋯`, the product of the first `k` entries divides the
product of the entries at any `k` distinct positions. This is what makes the leading `k × k`
minors of a diagonal matrix with chained entries the smallest ones in divisibility.

A tuple is determined by its leading partial sums `∑_{j < k} a j`, and in a canonically ordered
monoid each of them is at most the total. These are the facts about the dominance order of
exponent vectors (compare leading partial sums) that triangular expansions in Hecke rings use.
-/

public section

namespace Fin

/-- Successive differences telescope to the endpoint difference. -/
theorem sum_univ_succ_sub_castSucc {G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (last n) - f 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have hIic : Finset.Iic (last n) = Finset.univ := Finset.Iic_top
    simpa only [hIic, succ_last] using sum_Iic_sub (last n) f

/-- Reversed successive differences telescope to the reversed endpoint difference. -/
theorem sum_univ_castSucc_sub_succ {G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (last n) := by
  simpa only [neg_sub_neg] using sum_univ_succ_sub_castSucc (fun i ↦ -f i)

-- Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Chris Birkbeck), Apache-2.0, at
-- commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
-- `LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`, where it is a step in the uniqueness of
-- the Smith normal form; generalized here from `ℤ` to any commutative monoid.
/-- **The leading entries of a divisibility chain divide any equally many entries.** Along a
chain `d₀ ∣ d₁ ∣ ⋯`, the product of the first `k` entries divides the product of the entries
at any `k` distinct positions. -/
theorem prod_castLE_dvd_prod_of_injective {M : Type*} [CommMonoid M] {n : ℕ} {d : Fin n → M}
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j) {k : ℕ} (hk : k ≤ n) {f : Fin k → Fin n}
    (hf : Function.Injective f) :
    ∏ j : Fin k, d (Fin.castLE hk j) ∣ ∏ j : Fin k, d (f j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- the position `f j₀` of largest index is at least `k`, by injectivity
    obtain ⟨j₀, -, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun j ↦ (f j : ℕ)) Finset.univ_nonempty
    have hge : k ≤ (f j₀ : ℕ) := by
      by_contra hlt
      push Not at hlt
      have := Fintype.card_le_of_injective
        (fun j : Fin (k + 1) ↦ (⟨f j, (hmax j (Finset.mem_univ _)).trans_lt hlt⟩ : Fin k))
        (fun j₁ j₂ heq ↦ hf (Fin.ext (Fin.mk.inj heq)))
      simp at this
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succAbove _ j₀, mul_comm (d (f j₀))]
    exact mul_dvd_mul (ih (by omega) (hf.comp Fin.succAbove_right_injective))
      (hd (Fin.le_def.mpr hge))

/-- **A tuple is determined by its leading partial sums.** If the sums of the first `k` entries
of `a` and `b` agree for every `k ≤ n`, then `a = b`: entry `i` is what the sum of the first
`i + 1` entries adds to the sum of the first `i`. -/
theorem eq_of_forall_sum_castLE_eq {M : Type*} [AddCommMonoid M] [IsLeftCancelAdd M] {n : ℕ}
    {a b : Fin n → M}
    (h : ∀ (k : ℕ) (hk : k ≤ n), ∑ j : Fin k, a (castLE hk j) = ∑ j : Fin k, b (castLE hk j)) :
    a = b := by
  funext i
  have h₁ := h (i + 1) i.isLt
  simp only [sum_univ_castSucc, castLE_castSucc] at h₁
  rw [h i i.isLt.le] at h₁
  exact (congrArg a (Fin.ext rfl)).trans ((add_left_cancel h₁).trans (congrArg b (Fin.ext rfl)))

/-- A leading partial sum of a tuple in a canonically ordered monoid is at most its total. -/
theorem sum_castLE_le_sum {M : Type*} [AddCommMonoid M] [Preorder M] [CanonicallyOrderedAdd M]
    {n k : ℕ} (hk : k ≤ n) (f : Fin n → M) :
    ∑ j : Fin k, f (castLE hk j) ≤ ∑ i, f i :=
  calc ∑ j : Fin k, f (castLE hk j) = ∑ i ∈ Finset.univ.map (castLEEmb hk), f i := by simp
    _ ≤ ∑ i, f i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A product over the indices of `Fin (n + 1)` satisfying a predicate splits off the first
index. -/
@[to_additive /-- A sum over the indices of `Fin (n + 1)` satisfying a predicate splits off the
first index. -/]
theorem prod_filter_univ_succ {M : Type*} [CommMonoid M] {n : ℕ} (P : Fin (n + 1) → Prop)
    [DecidablePred P] (f : Fin (n + 1) → M) :
    ∏ i with P i, f i = (if P 0 then f 0 else 1) * ∏ i : Fin n with P i.succ, f i.succ := by
  rw [Finset.prod_filter, prod_univ_succ, Finset.prod_filter]

/-- If two filtered products over `Fin (n + 1)` agree, and their first factors are nonzero and
equal whenever the first index is selected, then the filtered products over the remaining indices
agree. -/
theorem prod_filter_succ_eq_of_prod_filter_eq {M : Type*} [CommMonoidWithZero M]
    [IsLeftCancelMulZero M] {n : ℕ}
    (P : Fin (n + 1) → Prop) [DecidablePred P] {f g : Fin (n + 1) → M}
    (h : ∏ i with P i, f i = ∏ i with P i, g i) (hf : P 0 → f 0 ≠ 0) (h0 : P 0 → f 0 = g 0) :
    ∏ i : Fin n with P i.succ, f i.succ = ∏ i : Fin n with P i.succ, g i.succ := by
  rw [prod_filter_univ_succ, prod_filter_univ_succ] at h
  by_cases hP : P 0
  · simp only [hP, ↓reduceIte, h0 hP] at h
    exact mul_left_cancel₀ (h0 hP ▸ hf hP) h
  · simpa only [hP, ↓reduceIte, one_mul] using h

end Fin

namespace TauCeti

/-- Reindex a sum over all indices except the last by the preceding finite ordinal. -/
theorem sum_finSuccAboveEquiv_last {M : Type*} [AddCommMonoid M] (n : ℕ)
    (z : {i : Fin (n + 1) // i ≠ Fin.last n} → M) :
    ∑ i : Fin n, z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ = ∑ j, z j := by
  simpa only [finSuccAboveEquiv_last_apply] using
    Equiv.sum_comp (finSuccAboveEquiv (Fin.last n)) z

end TauCeti
