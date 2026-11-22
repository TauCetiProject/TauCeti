/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.SuccPred.Archimedean

/-!
# Comparing weighted sums through their partial sums

If every initial partial sum of `f` is at most the corresponding partial sum of `g`, then the
same comparison holds after weighting both sequences by a nonnegative, antitone weight `w`:
`∑_{i < N} w i • f i ≤ ∑_{i < N} w i • g i`. This is Abel's inequality in its comparison form.
The sequences `f` and `g` take values in an ordered module over the ordered ring of weights;
for real or ring-valued sequences the scalar action is multiplication.
Summation by parts (`Finset.sum_range_by_parts`) writes the difference of the two weighted sums
as the last weight times the last partial-sum difference plus the successive decrements of `w`
times the earlier partial-sum differences, and every one of these products is nonnegative.

No sign condition on `f` or `g` is needed. The typical use takes `g` constant: a bound
`∑_{i < k} f i ≤ k • C` on all partial sums then gives `∑ w i • f i ≤ (∑ w i) • C` for every
nonnegative antitone weight.

The second result is the case where `g` is the indicator of the first `k` indices. Weights
`c i ∈ [0, 1]` of total mass at most `k`, placed against a nonnegative antitone sequence `w`,
give a weighted sum at most the sum of the `k` largest values of `w`: the mass is best spent on
the first `k` indices. Only `c i ≤ 1` for `i < k` and `0 ≤ c i` for `k ≤ i < N` are used. When
the mass is exactly `k`, no sign condition on `w` is needed. This is the step that turns
Bessel-type weight bounds into Ky Fan inequalities for singular values and eigenvalues.

Abel's tail estimate (`TauCeti.abs_sum_Ioc_mul_le`) bounds `|∑ j ∈ Ioc K m, f j * g j|` by
`2 * B * g (K + 1)` when the initial partial sums of `f` are bounded in absolute value by `B` and
the weights `g` are nonnegative and antitone on `Icc (K + 1) m`.

## Main results

* `TauCeti.sum_range_smul_le_sum_range_smul`: the weighted comparison.
* `TauCeti.sum_range_mul_le_sum_range_of_sum_le`: unit-bounded weights of total mass at most `k`
  against a nonnegative antitone sequence give at most the sum of its first `k` terms.
* `TauCeti.sum_range_mul_le_sum_range_of_sum_eq`: the same for weights of total mass exactly `k`,
  against an antitone sequence of any sign.
* `TauCeti.sum_range_eq_zero_of_sum_smul_eq_zero`: the equality case against a strictly decreasing
  weight; if `d` has nonnegative proper partial sums, vanishing total, and vanishing weighted sum,
  then all its partial sums vanish.
* `TauCeti.abs_sum_Ioc_mul_le`: Abel's tail estimate for bounded initial sums and nonnegative
  decreasing weights.

## Implementation notes

The proof of `TauCeti.sum_range_smul_le_sum_range_smul` follows Mathlib's ring-valued
`Finset.sum_mul_le_sum_mul_of_sum_range_le` in `Mathlib/Algebra/Order/Chebyshev.lean`: rewrite the
difference by `Finset.sum_range_by_parts` and bound each term by `Finset.sum_nonpos`. Following the
implementation notes of that file, which decouple the two factors by replacing multiplication with
a scalar action, the sequences `f` and `g` take values in an ordered module over the ring of
weights. The weight hypotheses are also weaker than Mathlib's: `w` need only be antitone on the
first `N` indices with `0 ≤ w (N - 1)`, rather than nonnegative everywhere.
-/

public section

namespace TauCeti

open Finset

variable {R M : Type*} [Ring R] [Preorder R] [IsOrderedAddMonoid R]

/-- **Abel's inequality, comparison form.** If the partial sums of `f` are dominated by those of
`g` up to `N`, and `w` is nonnegative and antitone on the first `N` indices, then
`∑_{i < N} w i • f i ≤ ∑_{i < N} w i • g i`. Only the last weight is required
to be nonnegative explicitly; the other signs follow from the successive comparisons
when `N > 0`. -/
theorem sum_range_smul_le_sum_range_smul [AddCommGroup M] [Preorder M] [IsOrderedAddMonoid M]
    [Module R M] [PosSMulMono R M] {f g : ℕ → M} {w : ℕ → R} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ range N, w i • f i ≤ ∑ i ∈ range N, w i • g i := by
  have hD (k : ℕ) (hk : k ≤ N) : 0 ≤ ∑ i ∈ range k, (g i - f i) := by
    simpa [sum_sub_distrib] using hfg k hk
  rw [← sub_nonneg, ← sum_sub_distrib]
  simp only [← smul_sub]
  rw [sum_range_by_parts, sub_nonneg]
  refine (sum_nonpos fun i hi ↦ ?_).trans (smul_nonneg hw0 (hD N le_rfl))
  rw [← neg_sub, neg_smul, neg_nonpos]
  exact smul_nonneg (sub_nonneg.2 (hw i (by grind))) (hD (i + 1) (by grind))

variable [PosMulMono R]

/-- Weights `c i` with total mass at most `k ≤ N`, at most `1` on the first `k` indices and
nonnegative on the remaining indices below `N`, placed against a sequence `w` that is antitone and
nonnegative on the first `N` indices, give at most the sum of the first `k` terms of `w`:
`∑_{i < N} w i * c i ≤ ∑_{i < k} w i`. In particular this applies to weights `c i ∈ [0, 1]`. -/
theorem sum_range_mul_le_sum_range_of_sum_le {w c : ℕ → R} {N k : ℕ} (hk : k ≤ N)
    (hc0 : ∀ i, k ≤ i → i < N → 0 ≤ c i) (hc1 : ∀ i < k, c i ≤ 1)
    (hck : ∑ i ∈ range N, c i ≤ k) (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i)
    (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ range N, w i * c i ≤ ∑ i ∈ range k, w i := by
  have hf (m : ℕ) : {i ∈ range m | i < k} = range (min m k) := by ext; simp
  have hg : ∑ i ∈ range N, w i * (if i < k then 1 else 0) = ∑ i ∈ range k, w i := by
    simp only [mul_ite, mul_one, mul_zero, ← sum_filter, hf, min_eq_right hk]
  rw [← hg]
  simp_rw [← smul_eq_mul]
  refine sum_range_smul_le_sum_range_smul (fun m hm ↦ ?_) hw hw0
  rw [← sum_filter, hf, sum_const, card_range, nsmul_one]
  rcases le_total m k with hmk | hkm
  · rw [min_eq_left hmk]
    exact (sum_le_card_nsmul _ _ 1 fun i hi ↦ hc1 i (by grind)).trans (by simp)
  · rw [min_eq_right hkm]
    refine (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hm) fun i hi hni ↦ ?_).trans hck
    exact hc0 i (by grind) (by grind)

/-- Weights `c i` with total mass exactly `k ≤ N`, at most `1` on the first `k` indices and
nonnegative on the remaining indices below `N`, placed against a sequence `w` that is antitone on
the first `N` indices, give at most the sum of the first `k` terms of `w`:
`∑_{i < N} w i * c i ≤ ∑_{i < k} w i`. Unlike `TauCeti.sum_range_mul_le_sum_range_of_sum_le`,
no sign condition on `w` is needed. -/
theorem sum_range_mul_le_sum_range_of_sum_eq {w c : ℕ → R} {N k : ℕ} (hk : k ≤ N)
    (hc0 : ∀ i, k ≤ i → i < N → 0 ≤ c i) (hc1 : ∀ i < k, c i ≤ 1)
    (hck : ∑ i ∈ range N, c i = k)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) :
    ∑ i ∈ range N, w i * c i ≤ ∑ i ∈ range k, w i := by
  -- Shift `w` by its last value, which makes it nonnegative without changing the comparison.
  have h := sum_range_mul_le_sum_range_of_sum_le (w := fun i ↦ w i - w (N - 1)) hk hc0 hc1
    hck.le (fun i hi ↦ sub_le_sub_right (hw i hi) _) (by simp)
  simpa [sub_mul, sum_sub_distrib, ← mul_sum, hck, Nat.cast_comm] using h

/-- **Equality case of Abel's inequality against a strictly decreasing weight.** If every proper
initial sum of `d` is nonnegative, the total sum of `d` over the first `N` indices vanishes, `w` is
strictly decreasing on the first `N` indices, and `∑_{i < N} w i • d i = 0`, then every initial
sum of `d` up to `N` vanishes. The sequence takes values in an ordered module, and positive
scalars act strictly monotonically; no multiplication on the target is required. -/
theorem sum_range_eq_zero_of_sum_smul_eq_zero {R M : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module R M] [PosSMulStrictMono R M] {d : ℕ → M} {w : ℕ → R} {N : ℕ}
    (hd : ∀ k < N, 0 ≤ ∑ i ∈ range k, d i) (hdN : ∑ i ∈ range N, d i = 0)
    (hw : ∀ i, i + 1 < N → w (i + 1) < w i) (hwd : ∑ i ∈ range N, w i • d i = 0) :
    ∀ k ≤ N, ∑ i ∈ range k, d i = 0 := by
  have hterms : ∀ k ∈ range (N - 1), 0 ≤ (w k - w (k + 1)) • ∑ i ∈ range (k + 1), d i :=
    fun k hk ↦ smul_nonneg (sub_nonneg.mpr (hw k (by grind)).le) (hd _ (by grind))
  have hsum : ∑ k ∈ range (N - 1), (w k - w (k + 1)) • ∑ i ∈ range (k + 1), d i = 0 := by
    have h := sum_range_by_parts w d N
    simp only [hdN, smul_zero, zero_sub, hwd, zero_eq_neg] at h
    rw [← neg_eq_zero, ← sum_neg_distrib, ← h]
    exact sum_congr rfl fun k _ ↦ by rw [← neg_smul, neg_sub]
  intro k hk
  rcases hk.eq_or_lt with rfl | hkN
  · exact hdN
  rcases k with _ | k
  · simp
  have hterm := (sum_eq_zero_iff_of_nonneg hterms).mp hsum k (mem_range.mpr (by omega))
  exact ((hd _ hkN).eq_or_lt.resolve_right fun h ↦
    (smul_pos (sub_pos.mpr (hw k hkN)) h).ne' hterm).symm

/-- **Abel's tail estimate for bounded initial sums.** If `0 ≤ B`, every initial sum
`∑ i ∈ range n, f i` for `K + 1 ≤ n ≤ m + 1` has absolute value at most `B`, and `g : ℕ → R` is
nonnegative at `K + 1` and `m` (when `K < m`) and antitone on `Icc (K + 1) m`, then
`|∑ j ∈ Ioc K m, f j * g j| ≤ 2 * B * g (K + 1)`. -/
theorem abs_sum_Ioc_mul_le {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
    {f g : ℕ → R} {B : R} {K m : ℕ}
    (hB : 0 ≤ B) (hf : ∀ n ∈ Icc (K + 1) (m + 1), |∑ i ∈ range n, f i| ≤ B)
    (hg_nonneg : 0 ≤ g (K + 1)) (hgm : K < m → 0 ≤ g m)
    (hg_anti : ∀ j ∈ Ico (K + 1) m, g (j + 1) ≤ g j) :
    |∑ j ∈ Ioc K m, f j * g j| ≤ 2 * B * g (K + 1) := by
  by_cases hKm : K < m
  swap
  · rw [Ioc_eq_empty hKm, sum_empty, abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hB) hg_nonneg
  have hg_antitone : AntitoneOn g (Set.Icc (K + 1) m) := by
    refine antitoneOn_of_succ_le Set.ordConnected_Icc fun j _ hj hsj ↦ ?_
    exact hg_anti j (mem_Ico.mpr ⟨hj.1, hsj.2⟩)
  let w : ℕ → R := fun i ↦ if i < m - K then g (K + 1 + i) else 0
  have hw₀ : 0 ≤ w := fun i ↦ by
    dsimp [w]
    split_ifs with hi
    · exact (hgm hKm).trans (hg_antitone ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩ (by omega))
    · exact le_rfl
  have hw_anti : AntitoneOn w (Set.Iio (m - K)) := by
    intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [w, hi, hj, ↓reduceIte]
    exact hg_antitone ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
  have hf' : ∀ k ≤ m - K, |∑ i ∈ range k, f (K + 1 + i)| ≤ 2 * B := by
    intro k hk
    have hsub : ∑ i ∈ range k, f (K + 1 + i) = ∑ j ∈ Ico (K + 1) (K + 1 + k), f j := by
      rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    rw [hsub, Finset.sum_Ico_eq_sub _ (by omega)]
    calc |∑ j ∈ range (K + 1 + k), f j - ∑ j ∈ range (K + 1), f j|
        ≤ |∑ j ∈ range (K + 1 + k), f j| + |∑ j ∈ range (K + 1), f j| := abs_sub _ _
      _ ≤ B + B := add_le_add
          (hf (K + 1 + k) (mem_Icc.mpr ⟨by omega, by omega⟩))
          (hf (K + 1) (mem_Icc.mpr ⟨le_rfl, by omega⟩))
      _ = 2 * B := (two_mul B).symm
  have hsum_eq : ∑ j ∈ Ioc K m, f j * g j = ∑ i ∈ range (m - K), f (K + 1 + i) * w i := by
    rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range, Nat.add_sub_add_right]
    exact sum_congr rfl fun i hi ↦ by simp [w, mem_range.mp hi]
  have hw0 : w 0 = g (K + 1) := by simp [w, Nat.sub_pos_of_lt hKm]
  rw [hsum_eq, ← hw0]
  exact Finset.abs_sum_mul_le_mul_of_abs_sum_range_le hf' hw₀ hw_anti

end TauCeti
