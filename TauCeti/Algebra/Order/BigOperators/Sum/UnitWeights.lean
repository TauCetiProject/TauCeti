/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Sums with weights in the unit interval

A sum `∑ i ∈ s, f i * c i` with weights `0 ≤ f i ≤ 1` lies between the sum of the negative terms
of `c` and the sum of its positive terms. Both are sums of `c` over subsets of `s`, so any bound
on the absolute values of all subset sums of `c` also bounds every such weighted sum. Applying
this once in each variable gives the corresponding statement for a matrix `w` tested against
two weight vectors.

In regularity arguments this upgrades a discrepancy bound on rectangles `s' × t'` to one for
tests `f i * g j` with values in `[0, 1]`, as needed for counting lemmas. Summing such a bound
over a further index then uses the crude estimate `|∑ i ∈ s, f i| ≤ #s • B` for terms bounded
by `B` in absolute value.

## Main results

* `Finset.abs_sum_mul_le_of_forall_subset`: weighted sums are controlled by subset sums.
* `Finset.abs_sum_sum_mul_mul_le_of_forall_subset`: the two-variable version.
* `Finset.abs_sum_le_card_nsmul`: a sum of `#s` terms bounded by `B` in absolute value is
  bounded by `#s • B`.
-/

public section

namespace Finset

variable {ι κ R : Type*}

section Ring

variable [Ring R] [LinearOrder R] [IsOrderedRing R]

/-- If every subset sum of `c` over `s` has absolute value at most `M`, then so has every sum
`∑ i ∈ s, f i * c i` with weights `0 ≤ f i ≤ 1`. -/
theorem abs_sum_mul_le_of_forall_subset {s : Finset ι} {f c : ι → R} {M : R}
    (hf₀ : ∀ i ∈ s, 0 ≤ f i) (hf₁ : ∀ i ∈ s, f i ≤ 1)
    (h : ∀ t ⊆ s, |∑ i ∈ t, c i| ≤ M) : |∑ i ∈ s, f i * c i| ≤ M := by
  classical
  refine abs_le.2 ⟨(neg_le_of_abs_le (h _ (filter_subset (fun i ↦ c i < 0) s))).trans ?_,
    le_trans ?_ (le_of_abs_le (h _ (filter_subset (fun i ↦ 0 < c i) s)))⟩
  · rw [sum_filter]
    refine sum_le_sum fun i hi ↦ ?_
    split_ifs with hc
    · simpa using mul_le_mul_of_nonpos_right (hf₁ i hi) hc.le
    · exact mul_nonneg (hf₀ i hi) (not_lt.1 hc)
  · rw [sum_filter]
    refine sum_le_sum fun i hi ↦ ?_
    split_ifs with hc
    · exact mul_le_of_le_one_left hc.le (hf₁ i hi)
    · exact mul_nonpos_of_nonneg_of_nonpos (hf₀ i hi) (not_lt.1 hc)

/-- If every rectangle sum `∑ i ∈ s', ∑ j ∈ t', w i j` with `s' ⊆ s` and `t' ⊆ t` has absolute
value at most `M`, then so has every sum `∑ i ∈ s, ∑ j ∈ t, f i * g j * w i j` with weights in
`[0, 1]`. -/
theorem abs_sum_sum_mul_mul_le_of_forall_subset {s : Finset ι} {t : Finset κ} {f : ι → R}
    {g : κ → R} {w : ι → κ → R} {M : R} (hf₀ : ∀ i ∈ s, 0 ≤ f i) (hf₁ : ∀ i ∈ s, f i ≤ 1)
    (hg₀ : ∀ j ∈ t, 0 ≤ g j) (hg₁ : ∀ j ∈ t, g j ≤ 1)
    (h : ∀ s' ⊆ s, ∀ t' ⊆ t, |∑ i ∈ s', ∑ j ∈ t', w i j| ≤ M) :
    |∑ i ∈ s, ∑ j ∈ t, f i * g j * w i j| ≤ M := by
  simp_rw [mul_assoc, ← mul_sum]
  refine abs_sum_mul_le_of_forall_subset hf₀ hf₁ fun s' hs' ↦ ?_
  rw [sum_comm]
  simp_rw [← mul_sum]
  refine abs_sum_mul_le_of_forall_subset hg₀ hg₁ fun t' ht' ↦ ?_
  rw [sum_comm]
  exact h s' hs' t' ht'

end Ring

/-- A sum of terms with absolute value at most `B` has absolute value at most `#s • B`. -/
theorem abs_sum_le_card_nsmul [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    {s : Finset ι} {f : ι → R} {B : R} (h : ∀ i ∈ s, |f i| ≤ B) : |∑ i ∈ s, f i| ≤ #s • B :=
  (abs_sum_le_sum_abs _ _).trans <| sum_le_card_nsmul s _ B h

end Finset
