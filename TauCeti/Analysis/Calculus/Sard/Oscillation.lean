/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Null images of sets with a small oscillation modulus

Let `E` and `F` be finite-dimensional real normed spaces of dimensions `m` and `d ≥ 1`. A bounded
subset `A` of `E` has null image under a map `f : E → F` if `f` has a uniform little-o modulus of
order `r` on `A`, that is `‖f y - f x‖ = o(‖y - x‖ ^ r)` uniformly for `x, y ∈ A`, and `m ≤ r * d`.
The proof partitions a containing ball into small Borel pieces, applies
`HolderOnWith.hausdorffMeasure_image_le` on each, and lets the Hölder constant tend to zero. The
Hausdorff measures `μH[m]` on `E` and `μH[d]` on `F` are additive Haar measures, which is where the
dimensions enter. Neither the set nor its image needs to be measurable.

This is the measure estimate in the Morse--Sard theorem. The input statement is adapted from KLS
at commit `65810c73f9dd7945fc646ab484cb19d673f5291d`, `Analysis/Sard/QuadraticCover.lean`; the
proof uses Mathlib's Hausdorff-measure API instead of its coordinate grid count. See A. Norton,
*A critical set with nonnull image has large Hausdorff dimension*, Trans. Amer. Math. Soc. 296
(1986), Section 5, Lemma 1.
-/

public section

open Set MeasureTheory Filter Topology Module
open scoped MeasureTheory NNReal ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  [MeasurableSpace F] [BorelSpace F]

/-- A bounded subset of a finite-dimensional real normed space `E`, on which `f` has a uniform
little-o modulus of order `r`, has null image in a nontrivial finite-dimensional space `F` as soon
as `finrank ℝ E ≤ r * finrank ℝ F`. The set need not be measurable. -/
theorem addHaar_image_eq_zero_of_oscillation_pow (ν : Measure F) [ν.IsAddHaarMeasure]
    {r : ℕ} {A : Set E} {f : E → F} (hA : Bornology.IsBounded A)
    (hr : finrank ℝ E ≤ r * finrank ℝ F)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ r) :
    ν (f '' A) = 0 := by
  classical
  borelize E
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have : Subsingleton E := Module.finrank_zero_iff.mp (by simpa using hr)
    exact (Set.Subsingleton.image (fun a _ b _ ↦ Subsingleton.elim a b) f).measure_zero ν
  apply Measure.absolutelyContinuous_isAddHaarMeasure ν (μH[finrank ℝ F] : Measure F)
  obtain ⟨R, -, hAR⟩ := hA.exists_pos_norm_le
  let B : Set E := Metric.closedBall 0 R
  let μ : Measure E := μH[((r : ℝ≥0) : ℝ) * finrank ℝ F]
  have hAB : A ⊆ B := fun x hx ↦ by
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hAR x hx
  -- The containing ball has finite measure for the Hausdorff measure of dimension `r * d ≥ m`.
  have hμ : μ B ≠ ∞ := by
    refine ((Measure.hausdorffMeasure_mono (d₁ := finrank ℝ E) ?_ B).trans_lt
      (isCompact_closedBall (0 : E) R).measure_lt_top).ne
    simpa [← Nat.cast_mul] using hr
  -- A measurable partition of a containing ball bounds the outer measures of the pieces.
  have key (ε : ℝ≥0) (hε : 0 < ε) :
      μH[finrank ℝ F] (f '' A) ≤ (ε : ℝ≥0∞) ^ finrank ℝ F * μ B := by
    obtain ⟨δ, hδ, hd⟩ := hosc ε hε
    obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq E
    let T : ℕ → Set E := disjointed fun j ↦ Metric.ball (c j) (δ / 2)
    have hTsub : ∀ j, T j ⊆ Metric.ball (c j) (δ / 2) := disjointed_subset _
    have hTunion : ⋃ j, T j = univ := by
      rw [iUnion_disjointed, eq_univ_iff_forall]
      intro y
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hc y (δ / 2) (by linarith)
      exact mem_iUnion.2 ⟨j, hj⟩
    have hhol (j : ℕ) : HolderOnWith ε (r : ℝ≥0) f (A ∩ T j) := by
      intro x hx y hy
      have hdist : dist y x < δ := by
        have h1 := hTsub j hx.2
        have h2 := hTsub j hy.2
        calc dist y x ≤ dist y (c j) + dist x (c j) := dist_triangle_right _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add h2 h1
          _ = δ := by ring
      have hreal : dist (f x) (f y) ≤ (ε : ℝ) * dist x y ^ r := by
        simpa [dist_eq_norm, norm_sub_rev] using
          hd x hx.1 y hy.1 (by simpa [dist_eq_norm] using hdist)
      simpa only [edist_dist, ENNReal.ofReal_mul ε.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow dist_nonneg,
        NNReal.coe_natCast, ENNReal.rpow_natCast] using ENNReal.ofReal_le_ofReal hreal
    calc μH[finrank ℝ F] (f '' A)
        ≤ μH[finrank ℝ F] (⋃ j, f '' (A ∩ T j)) := by
          apply measure_mono
          rw [← image_iUnion, ← inter_iUnion, hTunion, inter_univ]
      _ ≤ ∑' j, μH[finrank ℝ F] (f '' (A ∩ T j)) := measure_iUnion_le _
      _ ≤ ∑' j, (ε : ℝ≥0∞) ^ finrank ℝ F * μ (B ∩ T j) := tsum_le_tsum fun j ↦ by
          have hh := (hhol j).hausdorffMeasure_image_le (by exact_mod_cast hr0)
            (Nat.cast_nonneg (finrank ℝ F))
          rw [ENNReal.rpow_natCast] at hh
          exact hh.trans (by gcongr)
      _ = (ε : ℝ≥0∞) ^ finrank ℝ F * μ B := by
          rw [ENNReal.tsum_mul_left, ← measure_iUnion
            (fun i j hij ↦ (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right)
            (fun j ↦ measurableSet_closedBall.inter
              (MeasurableSet.disjointed (fun _ ↦ measurableSet_ball) j)),
            ← inter_iUnion, hTunion, inter_univ]
  -- The ball has finite measure, so arbitrarily small Hölder constants force nullity.
  have htend : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) ^ finrank ℝ F * μ B) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) ^ finrank ℝ F) (𝓝 0) (𝓝 0) := by
      simpa [Function.comp_def, zero_pow (Module.finrank_pos (R := ℝ) (M := F)).ne'] using
        ((ENNReal.continuous_pow (finrank ℝ F)).comp ENNReal.continuous_coe).tendsto (0 : ℝ≥0)
    simpa using (ENNReal.Tendsto.mul_const h0 (Or.inr hμ)).mono_left nhdsWithin_le_nhds
  exact le_antisymm (ge_of_tendsto htend (eventually_nhdsWithin_of_forall key)) bot_le

end TauCeti
