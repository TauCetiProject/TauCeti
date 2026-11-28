/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.StationaryPhase.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! # Cutoffs for stationary phase -/

public section

open Filter Metric Set
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A uniform bound for derivatives of a scalar-weighted amplitude. -/
theorem norm_iteratedFDeriv_smul_le_of_uniform_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E → ℝ} {a : E → V}
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {N : ℕ} (hf : ContDiffOn ℝ N f U) (ha : ContDiffOn ℝ N a U) {A B : ℝ}
    (hfb : ∀ i ≤ N, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hab : ∀ i ≤ N, ‖iteratedFDeriv ℝ i a x‖ ≤ B) (i : ℕ) (hi : i ≤ N) :
    ‖iteratedFDeriv ℝ i (fun y ↦ f y • a y) x‖ ≤ 2 ^ N * A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hfb 0 (Nat.zero_le _))
  have hB : 0 ≤ B := (norm_nonneg _).trans (hab 0 (Nat.zero_le _))
  refine (norm_iteratedFDeriv_smul_le_of_isOpen hU hf ha hx (by exact_mod_cast hi)).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * A * B := by
      gcongr with k hk
      · exact hfb k ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)).trans hi)
      · exact hab _ ((Nat.sub_le ..).trans hi)
    _ = 2 ^ i * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose i
    _ ≤ _ := by gcongr; norm_num

/-- A smooth cutoff between concentric balls, with bounds on every derivative up to a fixed
order. -/
theorem exists_bounded_smooth_cutoff (N : ℕ) {r R : ℝ} (hrR : r < R) :
    ∃ χ : E → ℝ, ∃ D : ℝ, 0 ≤ D ∧ ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ ball 0 R ∧
      (∀ x ∈ closedBall 0 r, χ =ᶠ[nhds x] fun _ ↦ 1) ∧
      ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ D := by
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ :=
    (isCompact_closedBall (0 : E) r).exists_contDiff_cutoff_eventuallyEq_one isOpen_ball
      (closedBall_subset_ball hrR)
  have hχn : ContDiffOn ℝ N χ univ := (hχ.of_le (by simp)).contDiffOn
  obtain ⟨D, hD, hDb⟩ := hχn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    isOpen_univ hχc.isCompact (subset_univ _)
  refine ⟨χ, D, hD, hχ, hχs, hχ1, fun j hj x ↦ ?_⟩
  by_cases hx : x ∈ tsupport χ
  · exact hDb j (by exact_mod_cast hj) x hx
  · have h0 := image_eq_zero_of_notMem_tsupport
      (show x ∉ tsupport (iteratedFDeriv ℝ j χ) from fun hx' ↦
        hx (tsupport_iteratedFDeriv_subset j hx'))
    rw [h0, norm_zero]
    exact hD

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

/-- Analytic functions on a fixed ball with a common norm bound can be extended smoothly
from a smaller closed ball, with uniform real derivative bounds. -/
theorem exists_contDiff_extension_of_analyticOnNhd_ball (N : ℕ) {r R : ℝ} (hrR : r < R) (M : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : E → F, AnalyticOnNhd ℂ f (ball 0 R) →
      (∀ x ∈ ball 0 R, ‖f x‖ ≤ M) →
      ∃ f' : E → F, ContDiff ℝ N f' ∧ (∀ x ∈ closedBall 0 r, f' =ᶠ[nhds x] f) ∧
        ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j f' x‖ ≤ D := by
  let ρ := (r + R) / 2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨χ, A, hA, hχ, hs, hχ1, hχb⟩ :=
    exists_bounded_smooth_cutoff (E := E) N hrρ
  choose C hC hCb using fun j : ℕ ↦
    exists_norm_iteratedFDeriv_le_of_analyticOnNhd_ball (E := E) (F := F) j (c := 0) hρR
  let B := (∑ j ∈ Finset.range (N + 1), C j) * max 0 M
  have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC j) (le_max_left ..)
  refine ⟨2 ^ N * A * B, by positivity, fun f hf hM ↦ ?_⟩
  let f' (x : E) := χ x • f x
  have hfn : ContDiffOn ℝ N f (ball 0 R) := fun x hx ↦
    ((hf x hx).restrictScalars (𝕜 := ℝ)).contDiffAt.contDiffWithinAt
  have hχn : ContDiff ℝ N χ := hχ.of_le (by simp)
  have hsR : tsupport χ ⊆ ball 0 R := hs.trans (ball_subset_ball hρR.le)
  refine ⟨f', hfn.contDiff_smul_of_tsupport_subset isOpen_ball hχn.contDiffOn hsR, ?_, ?_⟩
  · intro x hx
    filter_upwards [hχ1 x hx] with y hy
    simp [f', hy]
  · intro j hj x
    by_cases hx : x ∈ tsupport χ
    · have hxR := hsR hx
      have hfb (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i f x‖ ≤ B := by
        rw [← ((hf x hxR).contDiffAt (n := i)).restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
        change ‖(iteratedFDeriv ℂ i f x).restrictScalars ℝ‖ ≤ B
        rw [ContinuousMultilinearMap.norm_restrictScalars]
        have hCi : C i ≤ ∑ j ∈ Finset.range (N + 1), C j :=
          Finset.single_le_sum (fun k _ ↦ hC k) (Finset.mem_range.2 (by omega))
        exact (hCb i f M hf hM x (ball_subset_closedBall (hs hx))).trans
          (mul_le_mul_of_nonneg_left (le_max_right 0 M) (hC i) |>.trans
            (mul_le_mul_of_nonneg_right hCi (le_max_left 0 M)))
      exact norm_iteratedFDeriv_smul_le_of_uniform_bounds isOpen_ball hxR hχn.contDiffOn hfn
        (fun i hi ↦ hχb i hi x) hfb j hj
    · have h0 : f' =ᶠ[nhds x] fun _ ↦ 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
        simp [f', hy]
      rw [(h0.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
      change ‖iteratedFDeriv ℝ j (0 : E → F) x‖ ≤ _
      rw [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      positivity

end TauCeti
