/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Tactic.Linarith

/-!
# Taking a remainder along a direction in `ℤ^ι`

Let `v` be a family of positive integers and `w` a family of integers with a negative entry. Move
`v` along `w` by the largest integer `t` that keeps every entry of `v + t w` positive. This is a
simultaneous Euclidean division: `t` is the least of the quotients `⌊(v i - 1) / |w i|⌋` over the
negative entries `w i`, and an entry `i₀` realising it has remainder `v i₀ + t w i₀ ≤ |w i₀|`.
These quotients are nonnegative integers, so the least one exists over any index type.

## Main results

* `Int.exists_add_mul_pos_le`: the multiple `t` and the entry `i₀`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.4.3, proof of Lemma 27, where one length is replaced by such a remainder.
-/

public section

namespace Int

/-- **Remainder along a direction.** If `v` is a family of positive integers and `w j < 0` for
some `j`, there is an integer `t` keeping every entry of `v + t w` positive, and an entry `i₀` with
`w i₀ < 0` at which `v i₀ + t w i₀` is at most `-w i₀`. -/
theorem exists_add_mul_pos_le {ι : Type*} {v w : ι → ℤ} (hv : ∀ i, 0 < v i) {j : ι}
    (hj : w j < 0) :
    ∃ t : ℤ, ∃ i₀, w i₀ < 0 ∧ (∀ i, 0 < v i + t * w i) ∧ v i₀ + t * w i₀ ≤ -w i₀ := by
  have hq {i} (hi : w i < 0) : 0 ≤ (v i - 1) / -w i :=
    ediv_nonneg (by linarith [hv i]) (by linarith)
  obtain ⟨_, ⟨i₀, hi₀, rfl⟩, hmin⟩ := exists_least_of_bdd
    (P := fun t => ∃ i, w i < 0 ∧ (v i - 1) / -w i = t)
    ⟨0, by rintro _ ⟨i, hi, rfl⟩; exact hq hi⟩ ⟨_, j, hj, rfl⟩
  refine ⟨(v i₀ - 1) / -w i₀, i₀, hi₀, fun i => ?_, ?_⟩
  · rcases lt_or_ge (w i) 0 with hi | hi
    · nlinarith [hmin _ ⟨i, hi, rfl⟩, Int.ediv_mul_le (v i - 1) (by linarith : -w i ≠ 0)]
    · nlinarith [hv i, hq hi₀]
  · nlinarith [lt_ediv_add_one_mul_self (v i₀ - 1) (by linarith : 0 < -w i₀)]

end Int
