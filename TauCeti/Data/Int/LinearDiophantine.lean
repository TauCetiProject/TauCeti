/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Interval

/-!
# Small solutions below a solution of one homogeneous linear Diophantine equation

A nonzero solution `x` in natural numbers of one homogeneous linear equation
`∑ j, a j * x j = 0` with integer coefficients of absolute value at most `H` lies coordinatewise
above a nonzero solution `y ≤ x` whose entries add up to at most `2 * H + 1`. The bound depends
only on `H`, not on the number of unknowns; small solutions of this kind are the first step
towards bounds on small solutions of linear Diophantine systems over the natural numbers.

The bound comes from the one-dimensional case of the argument of Eisenbrand and Weismantel:
the unit vectors that add up to `x` can be ordered so that the value of the linear form on the
partial sums stays in `[-H, H]`, and two of the first `2 * H + 2` partial sums take the same
value.

## Main results

* `TauCeti.exists_le_sum_mul_eq_zero`: a nonzero solution of total size at most `2 * H + 1`
  below a given nonzero solution.

## References

* F. Eisenbrand, R. Weismantel, *Proximity results and faster algorithms for integer
  programming using the Steinitz lemma*, ACM Trans. Algorithms 16 (2020), Art. 5
  (arXiv:1707.00481).
* J. von zur Gathen, M. Sieveking, *A bound on solutions of linear integer equalities and
  inequalities*, Proc. Amer. Math. Soc. 72 (1978), 155–158, for bounds on small solutions of
  systems.
* V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups and
  monoids with involution*, arXiv:1405.5133, §1.4 and §3.2, where small solutions of linear
  Diophantine systems over the natural numbers are used.
-/

public section

namespace TauCeti

open Finset

variable {ι : Type*} [Fintype ι]

/- Below a solution `x`, a vector `z ≠ x` whose value lies in `[-H, H]` can be increased by one
unit in some coordinate without leaving `[-H, H]`. -/
private lemma exists_lt_abs_sum_add_le {a : ι → ℤ} {H : ℕ} (ha : ∀ j, |a j| ≤ H) {x z : ι → ℕ}
    (hx : ∑ j, a j * x j = 0) (hzx : z ≤ x) (hne : z ≠ x) (hz : |∑ j, a j * z j| ≤ H) :
    ∃ j, z j < x j ∧ |∑ i, a i * z i + a j| ≤ H := by
  wlog h0 : 0 ≤ ∑ j, a j * z j generalizing a
  · obtain ⟨j, hj, h⟩ := this (a := -a) (by simpa using ha) (by simp [hx]) (by simpa using hz)
      (by simp only [Pi.neg_apply, neg_mul, sum_neg_distrib]; lia)
    have hneg : ∑ i, (-a) i * (z i : ℤ) + (-a) j = -(∑ i, a i * z i + a j) := by
      simp only [Pi.neg_apply, neg_mul, sum_neg_distrib, neg_add]
    exact ⟨j, hj, by rwa [hneg, abs_neg] at h⟩
  by_contra! hcon
  have hpos : ∀ j, z j < x j → 0 < a j := fun j hj => by
    have := hcon j hj
    have := ha j
    grind [abs_le]
  have hterm : ∀ i, z i < x i → 0 < a i * ((x i : ℤ) - z i) := fun i hi =>
    mul_pos (hpos i hi) (sub_pos.mpr (by exact_mod_cast hi))
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hlt : 0 < ∑ i, a i * ((x i : ℤ) - z i) := by
    refine sum_pos' (fun i _ => ?_) ⟨j, mem_univ _, hterm j ((hzx j).lt_of_ne hj)⟩
    rcases (hzx i).lt_or_eq with h | h
    · exact (hterm i h).le
    · simp [h]
  simp only [mul_sub, sum_sub_distrib, hx] at hlt
  lia

/- Starting from `0`, the coordinates of a solution `x` can be filled in one unit at a time so
that the value of the linear form stays in `[-H, H]`: a monotone sequence below `x`, with values
in `[-H, H]`, whose `t`-th term has total size `t` for `t ≤ n`. -/
private lemma exists_monotone_abs_sum_le {a : ι → ℤ} {H : ℕ} (ha : ∀ j, |a j| ≤ H) {x : ι → ℕ}
    (hx : ∑ j, a j * x j = 0) {n : ℕ} (hn : n ≤ ∑ j, x j) :
    ∃ z : ℕ → ι → ℕ, Monotone z ∧ (∀ t, z t ≤ x) ∧ (∀ t, |∑ j, a j * z t j| ≤ H) ∧
      ∀ t ≤ n, ∑ j, z t j = t := by
  classical
  induction n with
  | zero => exact ⟨fun _ => 0, monotone_const, fun _ _ => Nat.zero_le _, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨z, hmono, hzx, hzH, hsum⟩ := ih (by lia)
    obtain ⟨j, hj, hjH⟩ := exists_lt_abs_sum_add_le ha hx (hzx n)
      (fun h => by grind) (hzH n)
    let w := z n + Pi.single j 1
    have hzw : z n ≤ w := le_add_of_nonneg_right fun _ => Nat.zero_le _
    refine ⟨fun t => if t ≤ n then z t else w, fun s t hst => ?_, fun t i => ?_, fun t => ?_,
      fun t ht => ?_⟩ <;> dsimp only
    · split_ifs with hs ht ht
      exacts [hmono hst, (hmono hs).trans hzw, by lia, le_rfl]
    · split_ifs
      · exact hzx t i
      · rcases eq_or_ne i j with rfl | hij
        · simpa [w, Nat.add_one_le_iff] using hj
        · simpa [w, hij] using hzx n i
    · split_ifs
      · exact hzH t
      · simpa [w, mul_add, sum_add_distrib, Pi.single_apply] using hjH
    · split_ifs with h
      · exact hsum t h
      · simp [w, sum_add_distrib, hsum n le_rfl]
        lia

/- Two of the `2 * H + 2` values `∑ j, a j * z t j` with `t ≤ 2 * H + 1` coincide when they all
lie in `[-H, H]`. -/
private lemma exists_lt_le_sum_mul_eq {a : ι → ℤ} {H : ℕ} {z : ℕ → ι → ℕ}
    (hzH : ∀ t, |∑ j, a j * z t j| ≤ H) :
    ∃ p q, p < q ∧ q ≤ 2 * H + 1 ∧ ∑ j, a j * z p j = ∑ j, a j * z q j := by
  obtain ⟨p, hp, q, hq, hpq, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (2 * H + 2)) (t := Icc (-(H : ℤ)) H) (f := fun t => ∑ j, a j * z t j)
    (by simp; lia) (fun t _ => by simpa [abs_le] using hzH t)
  rw [mem_range] at hp hq
  rcases hpq.lt_or_gt with h | h
  exacts [⟨p, q, h, by lia, heq⟩, ⟨q, p, h, by lia, heq.symm⟩]

/-- A nonzero solution in natural numbers of one homogeneous linear equation with integer
coefficients of absolute value at most `H` lies coordinatewise above a nonzero solution whose
entries add up to at most `2 * H + 1`. -/
theorem exists_le_sum_mul_eq_zero (a : ι → ℤ) (H : ℕ) (ha : ∀ j, |a j| ≤ H) (x : ι → ℕ)
    (hx : ∑ j, a j * x j = 0) (hx0 : x ≠ 0) :
    ∃ y : ι → ℕ, y ≠ 0 ∧ y ≤ x ∧ ∑ j, a j * y j = 0 ∧ ∑ j, y j ≤ 2 * H + 1 := by
  by_cases hN : ∑ j, x j ≤ 2 * H + 1
  · exact ⟨x, hx0, le_rfl, hx, hN⟩
  obtain ⟨z, hmono, hzx, hzH, hsum⟩ := exists_monotone_abs_sum_le ha hx (n := 2 * H + 1) (by lia)
  obtain ⟨p, q, hpq, hq, heq⟩ := exists_lt_le_sum_mul_eq hzH
  have hle : z p ≤ z q := hmono hpq.le
  -- The small solution is the difference `z q - z p`, of total size `q - p`.
  have hsub : ∑ j, (z q - z p) j = q - p := by
    simp only [Pi.sub_apply]
    rw [sum_tsub_distrib _ fun j _ => hle j, hsum q hq, hsum p (by lia)]
  refine ⟨z q - z p, fun h => ?_, fun j => (Nat.sub_le _ _).trans (hzx q j), ?_, by lia⟩
  · rw [h] at hsub
    simp at hsub
    lia
  · simp only [Pi.sub_apply, Nat.cast_sub (hle _), mul_sub, sum_sub_distrib]
    exact sub_eq_zero.mpr heq.symm

end TauCeti
