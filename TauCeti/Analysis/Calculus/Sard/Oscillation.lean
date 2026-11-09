/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Null images of sets with a small oscillation modulus

A bounded subset of an n-dimensional real product has null image if the function has a
uniform little-o modulus of order n there. The proof partitions a containing ball into small
Borel pieces, applies `HolderOnWith.hausdorffMeasure_image_le` on each, and lets the Hölder
constant tend to zero. Neither the set nor its image needs to be measurable.

This is the measure estimate in the scalar Morse--Sard theorem. The input statement is adapted
from KLS at commit `65810c73f9dd7945fc646ab484cb19d673f5291d`,
`Analysis/Sard/QuadraticCover.lean`; the proof uses Mathlib's Hausdorff-measure API instead of
its coordinate grid count. See A. Norton, *A critical set with nonnull image has large Hausdorff
dimension*, Trans. Amer. Math. Soc. 296 (1986), Section 5, Lemma 1.
-/

public section

open Set MeasureTheory Filter Topology
open scoped MeasureTheory NNReal ENNReal

namespace TauCeti

/-- A bounded subset of an n-dimensional real product on which `f` has a uniform little-o
modulus of order n has Lebesgue-null image. The set need not be measurable. -/
theorem volume_image_eq_zero_of_oscillation_pow {n : ℕ} {A : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ n) :
    volume (f '' A) = 0 := by
  classical
  rcases n with _ | n
  · refine Set.Subsingleton.measure_zero ?_ _
    exact Set.Subsingleton.image (fun a _ b _ ↦ Subsingleton.elim a b) f
  obtain ⟨R, hR, hAR⟩ := hA.exists_pos_norm_le
  let B : Set (Fin (n + 1) → ℝ) := Metric.closedBall 0 R
  let μ : Measure (Fin (n + 1) → ℝ) := μH[(Module.finrank ℝ (Fin (n + 1) → ℝ) : ℝ)]
  have hAB : A ⊆ B := fun x hx ↦ by
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hAR x hx
  have hμ : μ B ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  -- A measurable partition of a containing ball bounds the outer measures of the pieces.
  have key (ε : ℝ≥0) (hε : 0 < ε) : volume (f '' A) ≤ (ε : ℝ≥0∞) * μ B := by
    obtain ⟨δ, hδ, hd⟩ := hosc ε hε
    obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq (Fin (n + 1) → ℝ)
    let T : ℕ → Set (Fin (n + 1) → ℝ) := disjointed fun j ↦ Metric.ball (c j) (δ / 2)
    have hTsub : ∀ j, T j ⊆ Metric.ball (c j) (δ / 2) := disjointed_subset _
    have hTunion : ⋃ j, T j = univ := by
      rw [iUnion_disjointed, eq_univ_iff_forall]
      intro y
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hc y (δ / 2) (by linarith)
      exact mem_iUnion.2 ⟨j, hj⟩
    have hhol (j : ℕ) : HolderOnWith ε ((n + 1 : ℕ) : ℝ≥0) f (A ∩ T j) := by
      intro x hx y hy
      have hdist : dist y x < δ := by
        have h1 := hTsub j hx.2
        have h2 := hTsub j hy.2
        calc dist y x ≤ dist y (c j) + dist x (c j) := dist_triangle_right _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add h2 h1
          _ = δ := by ring
      have hreal : dist (f x) (f y) ≤ (ε : ℝ) * dist x y ^ (n + 1) := by
        simpa [Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev] using
          hd x hx.1 y hy.1 (by simpa [dist_eq_norm] using hdist)
      simpa only [edist_dist, ENNReal.ofReal_mul ε.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow dist_nonneg,
        NNReal.coe_natCast, ENNReal.rpow_natCast] using ENNReal.ofReal_le_ofReal hreal
    calc volume (f '' A)
        ≤ volume (⋃ j, f '' (A ∩ T j)) := by
          apply measure_mono
          rw [← image_iUnion, ← inter_iUnion, hTunion, inter_univ]
      _ ≤ ∑' j, volume (f '' (A ∩ T j)) := measure_iUnion_le _
      _ ≤ ∑' j, (ε : ℝ≥0∞) * μ (B ∩ T j) := tsum_le_tsum fun j ↦ by
          have hh := (hhol j).hausdorffMeasure_image_le (by positivity) (d := 1) zero_le_one
          have hsub : A ∩ T j ⊆ B ∩ T j := inter_subset_inter_left _ hAB
          have hh' : volume (f '' (A ∩ T j)) ≤ (ε : ℝ≥0∞) * μ (A ∩ T j) := by
            simpa [μ, hausdorffMeasure_real] using hh
          exact hh'.trans (mul_le_mul (le_refl _) (measure_mono hsub) bot_le bot_le)
      _ = (ε : ℝ≥0∞) * μ B := by
          rw [ENNReal.tsum_mul_left, ← measure_iUnion
            (fun i j hij ↦ (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right)
            (fun j ↦ measurableSet_closedBall.inter
              (MeasurableSet.disjointed (fun _ ↦ measurableSet_ball) j)),
            ← inter_iUnion, hTunion, inter_univ]
  -- The containing ball has finite measure, so arbitrarily small Hölder constants force nullity.
  have htend : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) * μ B) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ENNReal.continuous_coe.tendsto (0 : ℝ≥0)
    simpa using (ENNReal.Tendsto.mul_const h0 (Or.inr hμ)).mono_left nhdsWithin_le_nhds
  exact le_antisymm (ge_of_tendsto htend (eventually_nhdsWithin_of_forall key)) bot_le

end TauCeti
