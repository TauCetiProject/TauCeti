/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ekeland's variational principle

Let `φ` be a lower semicontinuous real function, bounded below, on a complete metric space, and
let `ε > 0`. **Ekeland's variational principle** produces, from any starting point `x`, a point
`y` with `φ y + ε * dist y x ≤ φ x` which is the strict global minimum of the perturbed function
`z ↦ φ z + ε * dist z y`.

In Banach space theory this is the device behind the Bishop–Phelps theorem: applied to minus the
real part of a functional on a closed set, it produces a point admitting a supporting cone.

## Main results

* `LowerSemicontinuous.exists_add_mul_dist_le_and_lt_add_mul_dist`: Ekeland's variational
  principle.

## References

* I. Ekeland, *On the variational principle*, J. Math. Anal. Appl. 47 (1974), 324–353.
* R. R. Phelps, *Convex Functions, Monotone Operators and Differentiability*, 2nd ed.,
  Lecture Notes in Mathematics 1364, Springer, 1993, Chapter 3.
-/

public section

open Filter Set Topology

namespace LowerSemicontinuous

variable {X : Type*} [MetricSpace X] [CompleteSpace X] {φ : X → ℝ}

/-- **Ekeland's variational principle.** Let `φ` be a lower semicontinuous function, bounded below,
on a complete metric space, and let `ε > 0`. For every `x` there is a point `y` such that
`φ y + ε * dist y x ≤ φ x` and `y` is the strict global minimum of `z ↦ φ z + ε * dist z y`. -/
theorem exists_add_mul_dist_le_and_lt_add_mul_dist (hφ : LowerSemicontinuous φ)
    (hbdd : BddBelow (range φ)) {ε : ℝ} (hε : 0 < ε) (x : X) :
    ∃ y, φ y + ε * dist y x ≤ φ x ∧ ∀ z, z ≠ y → φ y < φ z + ε * dist z y := by
  -- `S a` is the set of points improving on `a` by at least `ε` times their distance from `a`.
  set S : X → Set X := fun a ↦ {b | φ b + ε * dist b a ≤ φ a}
  have hS_self (a : X) : a ∈ S a := by simp [S]
  have hS_closed (a : X) : IsClosed (S a) :=
    (hφ.add (continuous_const.mul (continuous_id.dist continuous_const)).lowerSemicontinuous)
      |>.isClosed_preimage (φ a)
  have hS_trans {a b c : X} (hb : b ∈ S a) (hc : c ∈ S b) : c ∈ S a := by
    simp only [S, mem_ofPred_eq] at hb hc ⊢
    nlinarith [dist_triangle c b a]
  -- From any `a`, one can move to a point of `S a` which nearly minimizes `φ` on `S a`, up to
  -- `δ > 0`; the improvement set of such a point has radius at most `δ / ε`.
  have hnext (a : X) {δ : ℝ} (hδ : 0 < δ) : ∃ b ∈ S a, ∀ c ∈ S b, ε * dist c b ≤ δ := by
    have hne : (φ '' S a).Nonempty := ⟨_, mem_image_of_mem _ (hS_self a)⟩
    have hbdd' : BddBelow (φ '' S a) := hbdd.mono (image_subset_range _ _)
    obtain ⟨_, ⟨b, hb, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hδ)
    refine ⟨b, hb, fun c hc ↦ ?_⟩
    have hinf : sInf (φ '' S a) ≤ φ c := csInf_le hbdd' (mem_image_of_mem _ (hS_trans hb hc))
    simp only [S, mem_ofPred_eq] at hc
    linarith
  choose next hnext_mem hnext_le using fun (a : X) (n : ℕ) ↦
    hnext a (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  let u : ℕ → X := fun n ↦ Nat.rec (next x 0) (fun n a ↦ next a (n + 1)) n
  have hu_succ (n : ℕ) : u (n + 1) = next (u n) (n + 1) := rfl
  have hu_le (n : ℕ) : ∀ c ∈ S (u n), ε * dist c (u n) ≤ 1 / (n + 1) := by
    cases n with
    | zero => exact hnext_le x 0
    | succ n => exact hu_succ n ▸ hnext_le (u n) (n + 1)
  have hu_mono {m n : ℕ} (h : n ≤ m) : u m ∈ S (u n) := by
    induction h with
    | refl => exact hS_self _
    | step _ ih => exact hS_trans ih (hu_succ _ ▸ hnext_mem _ _)
  have hu_dist {m n : ℕ} (h : n ≤ m) : dist (u n) (u m) ≤ 1 / (n + 1) / ε := by
    rw [le_div_iff₀ hε, dist_comm, mul_comm]
    exact hu_le n _ (hu_mono h)
  have hb : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) / ε) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.div_const ε
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_tendsto_0' _ (fun _ _ h ↦ hu_dist h) hb)
  -- The limit `y` lies in every `S (u n)`, which are closed and eventually contain `u`.
  have hyS (n : ℕ) : y ∈ S (u n) :=
    (hS_closed _).mem_of_tendsto hy (eventually_atTop.2 ⟨n, fun _ ↦ hu_mono⟩)
  refine ⟨y, hS_trans (hnext_mem x 0) (hyS 0), fun z hzy ↦ ?_⟩
  -- A point `z` with `φ z + ε * dist z y ≤ φ y` would lie in every `S (u n)`, so `u` would
  -- converge to `z` as well.
  by_contra! hz
  have hzS (n : ℕ) : z ∈ S (u n) := hS_trans (hyS n) hz
  have hz_lim : Tendsto u atTop (𝓝 z) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hb)
    rw [le_div_iff₀ hε, dist_comm, mul_comm]
    exact hu_le n z (hzS n)
  exact hzy (tendsto_nhds_unique hz_lim hy)

end LowerSemicontinuous
