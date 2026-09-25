/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear growth of weighted sums under a second-order inequality

Let `d_m(j) ≥ 0` be a family of vectors indexed by `m : ℕ`, and `c` a square matrix, with

```text
d_1(j) ≥ ∑_i c_{ij} d_0(i),        d_{m+2}(j) + d_m(j) ≥ ∑_i c_{ij} d_{m+1}(i).
```

If a nonnegative weight `δ` satisfies `2 δ_i ≤ ∑_j c_{ij} δ_j`, the weighted sums
`s_m = ∑_j δ_j d_m(j)` satisfy `s_1 ≥ 2 s_0` and `s_{m+2} + s_m ≥ 2 s_{m+1}`, so their successive
differences never decrease and never fall below `s_0`, whence `s_m ≥ (m + 1) s_0`.

These are the inequalities satisfied by the graded pieces of an algebra with quadratic relations
in the Golod--Shafarevich/Anick bound, where `c` counts the generators and `δ` witnesses that the
matrix `2I - c` is not positive definite; see
`TauCeti.PathAlgebra.not_module_finite_quotient_span_range_of_two_mul_le_sum`.

## Main results

* `TauCeti.add_one_mul_sum_mul_le_sum_mul`: under these hypotheses,
  `(m + 1) ∑_j δ_j d_0(j) ≤ ∑_j δ_j d_m(j)`.
-/

public section

namespace TauCeti

/-- **Linear growth of weighted sums under a second-order inequality.** If `d_m(j) ≥ 0` satisfy
`∑_i c_{ij} d_0(i) ≤ d_1(j)` and `∑_i c_{ij} d_{m+1}(i) ≤ d_{m+2}(j) + d_m(j)`, and a
nonnegative weight `δ` satisfies `2 δ_i ≤ ∑_j c_{ij} δ_j`, then the weighted sums
`s_m = ∑_j δ_j d_m(j)` grow at least linearly: `(m + 1) s_0 ≤ s_m`. -/
theorem add_one_mul_sum_mul_le_sum_mul {ι : Type*} [Fintype ι] {S : Type*} [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] (c : ι → ι → S) {δ : ι → S} (hδ0 : 0 ≤ δ)
    (hδ : ∀ i, 2 * δ i ≤ ∑ j, c i j * δ j) {d : ℕ → ι → S} (hd0 : ∀ m j, 0 ≤ d m j)
    (h1 : ∀ j, ∑ i, c i j * d 0 i ≤ d 1 j)
    (h2 : ∀ m j, ∑ i, c i j * d (m + 1) i ≤ d (m + 2) j + d m j) (m : ℕ) :
    ((m : S) + 1) * ∑ j, δ j * d 0 j ≤ ∑ j, δ j * d m j := by
  set s : ℕ → S := fun m => ∑ j, δ j * d m j with hs
  -- Weighting a lower bound `∑_i c_{ij} e_i ≤ f_j` by `δ` doubles the weighted sum of `e`.
  have key : ∀ e f : ι → S, 0 ≤ e → (∀ j, ∑ i, c i j * e i ≤ f j) →
      2 * ∑ i, δ i * e i ≤ ∑ j, δ j * f j := by
    intro e f he hef
    calc 2 * ∑ i, δ i * e i = ∑ i, (2 * δ i) * e i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, (∑ j, c i j * δ j) * e i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hδ i) (he i)
      _ = ∑ j, δ j * ∑ i, c i j * e i := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ j, δ j * f j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hef j) (hδ0 j)
  have hs1 : 2 * s 0 ≤ s 1 := key _ _ (hd0 0) h1
  have hs2 : ∀ m, 2 * s (m + 1) ≤ s (m + 2) + s m := by
    intro m
    simpa only [hs, mul_add, Finset.sum_add_distrib] using key _ _ (hd0 (m + 1)) (h2 m)
  have hstep : ∀ m, s 0 ≤ s (m + 1) - s m ∧ ((m : S) + 1) * s 0 ≤ s m := by
    intro m
    induction m with
    | zero => constructor <;> [linarith; simp]
    | succ m ih =>
      have := hs2 m
      push_cast
      constructor <;> linarith [ih.1, ih.2]
  exact (hstep m).2

end TauCeti
