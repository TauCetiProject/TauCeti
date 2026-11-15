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
    linarith [mul_le_mul_of_nonneg_left (dist_triangle c b a) hε.le]
  -- From any `a`, one can move to a point of `S a` which nearly minimizes `φ` on `S a`, up to
  -- `δ > 0`; the improvement set of such a point has radius at most `δ / ε`.
  have hnext (a : X) {δ : ℝ} (hδ : 0 < δ) : ∃ b ∈ S a, ∀ c ∈ S b, dist b c ≤ δ / ε := by
    obtain ⟨_, ⟨b, hb, rfl⟩, hlt⟩ :=
      Real.lt_sInf_add_pos (Set.Nonempty.image φ ⟨a, hS_self a⟩) hδ
    refine ⟨b, hb, fun c hc ↦ ?_⟩
    have hinf : sInf (φ '' S a) ≤ φ c :=
      csInf_le (hbdd.mono (image_subset_range _ _)) (mem_image_of_mem _ (hS_trans hb hc))
    simp only [S, mem_ofPred_eq] at hc
    rw [le_div_iff₀ hε, dist_comm, mul_comm]
    linarith
  choose next hnext_mem hnext_le using fun (a : X) (n : ℕ) ↦
    hnext a (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  -- The sequence starts at `u 0 = x` and moves by `u (n + 1) = next (u n) n`.
  let u : ℕ → X := fun n ↦ Nat.rec x (fun n a ↦ next a n) n
  have hu_succ (n : ℕ) : u (n + 1) = next (u n) n := rfl
  have hu_mono {m n : ℕ} (h : n ≤ m) : u m ∈ S (u n) := by
    induction h with
    | refl => exact hS_self _
    | step _ ih => exact hS_trans ih (hu_succ _ ▸ hnext_mem _ _)
  -- Past the first step, every `S (u (n + 1))` lies within `1 / (n + 1) / ε` of `u (n + 1)`.
  have hu_le (n : ℕ) {c : X} (hc : c ∈ S (u (n + 1))) : dist (u (n + 1)) c ≤ 1 / (n + 1) / ε := by
    rw [hu_succ] at hc ⊢
    exact hnext_le (u n) n c hc
  have hb : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) / ε) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.div_const ε
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete <| cauchySeq_of_le_tendsto_0'
    (s := fun n ↦ u (n + 1)) _ (fun _ _ h ↦ hu_le _ (hu_mono (Nat.succ_le_succ h))) hb
  -- The limit `y` lies in every `S (u n)`, which are closed and eventually contain `u (· + 1)`.
  have hyS (n : ℕ) : y ∈ S (u n) := (hS_closed _).mem_of_tendsto hy <|
    eventually_atTop.2 ⟨n, fun _ h ↦ hu_mono (Nat.le_succ_of_le h)⟩
  refine ⟨y, hyS 0, fun z hzy ↦ ?_⟩
  -- A point `z` with `φ z + ε * dist z y ≤ φ y` would lie in every `S (u n)`, so `u (· + 1)`
  -- would converge to `z` as well.
  by_contra! hz
  have hz_lim : Tendsto (fun n ↦ u (n + 1)) atTop (𝓝 z) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ hu_le n (hS_trans (hyS (n + 1)) hz)) hb
  exact hzy (tendsto_nhds_unique hz_lim hy)

end LowerSemicontinuous
