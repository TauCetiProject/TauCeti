/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Null images of sets with a small oscillation modulus

Let `A` be a bounded subset of `Fin n → ℝ` and `f` a map from `Fin n → ℝ` to a finite power
`ι → ℝ`. If `f` has a uniform little-o modulus of order `k` on `A` and `n ≤ k * card ι`, then
`f '' A` is Lebesgue-null. On small pieces of `A` the modulus is a Hölder bound of exponent
`n / card ι` with an arbitrarily small constant, so the proof partitions a containing ball into
small Borel pieces, applies `HolderOnWith.hausdorffMeasure_image_le` on each, and lets the Hölder
constant tend to zero. Neither the set nor its image needs to be measurable.

This is the measure estimate in the Morse--Sard theorem at the sharp regularity. The input
statement is adapted from KLS at commit `65810c73f9dd7945fc646ab484cb19d673f5291d`,
`Analysis/Sard/QuadraticCover.lean`, which treats a real-valued `f` of order `n`; the proof uses
Mathlib's Hausdorff-measure API instead of its coordinate grid count. See A. Norton, *A critical
set with nonnull image has large Hausdorff dimension*, Trans. Amer. Math. Soc. 296 (1986),
Section 5, Lemma 1.
-/

public section

open Set MeasureTheory Filter Topology
open scoped MeasureTheory NNReal ENNReal

namespace TauCeti

/-- A bounded subset of `Fin n → ℝ` on which a map to `ι → ℝ` has a uniform little-o modulus of
order `k`, with `n ≤ k * card ι`, has Lebesgue-null image. The set need not be measurable. -/
theorem volume_image_eq_zero_of_oscillation_pow {n k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {A : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ι → ℝ} (hA : Bornology.IsBounded A)
    (hnk : n ≤ k * Fintype.card ι)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k) :
    volume (f '' A) = 0 := by
  classical
  rcases n with _ | n
  · refine Set.Subsingleton.measure_zero ?_ _
    exact Set.Subsingleton.image (fun a _ b _ ↦ Subsingleton.elim a b) f
  set d : ℕ := Fintype.card ι with hd
  have hd0 : 0 < d := Fintype.card_pos
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hnk
  -- On pieces of diameter at most one, the modulus of order `k` is a Hölder bound of exponent
  -- `r = (n + 1) / d`, and `r * d` is the dimension of the source.
  set r : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) / d with hr
  have hr0 : 0 < r := div_pos (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast hd0)
  have hrk : (r : ℝ) ≤ k := by
    rw [hr, NNReal.coe_div, div_le_iff₀ (by exact_mod_cast hd0)]
    exact_mod_cast hnk
  have hrd : (r : ℝ) * d = ((n + 1 : ℕ) : ℝ) := by
    rw [hr, NNReal.coe_div]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    push_cast
    field_simp
  obtain ⟨R, hR, hAR⟩ := hA.exists_pos_norm_le
  let B : Set (Fin (n + 1) → ℝ) := Metric.closedBall 0 R
  let μ : Measure (Fin (n + 1) → ℝ) := μH[((n + 1 : ℕ) : ℝ)]
  have hAB : A ⊆ B := fun x hx ↦ by
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hAR x hx
  have hμ : μ B ≠ ∞ := by
    have h := (isCompact_closedBall (0 : Fin (n + 1) → ℝ) R).measure_lt_top
      (μ := μH[(Module.finrank ℝ (Fin (n + 1) → ℝ) : ℝ)])
    simpa [μ] using h.ne
  -- A measurable partition of a containing ball bounds the outer measures of the pieces.
  have key (ε : ℝ≥0) (hε : 0 < ε) : volume (f '' A) ≤ (ε : ℝ≥0∞) ^ (d : ℝ) * μ B := by
    obtain ⟨δ, hδ, hδA⟩ := hosc ε hε
    set δ' := min δ 1 with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ one_pos
    obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq (Fin (n + 1) → ℝ)
    let T : ℕ → Set (Fin (n + 1) → ℝ) := disjointed fun j ↦ Metric.ball (c j) (δ' / 2)
    have hTsub : ∀ j, T j ⊆ Metric.ball (c j) (δ' / 2) := disjointed_subset _
    have hTunion : ⋃ j, T j = univ := by
      rw [iUnion_disjointed, eq_univ_iff_forall]
      intro y
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hc y (δ' / 2) (by linarith)
      exact mem_iUnion.2 ⟨j, hj⟩
    have hhol (j : ℕ) : HolderOnWith ε r f (A ∩ T j) := by
      intro x hx y hy
      have hdist : dist y x < δ' := by
        have h1 := hTsub j hx.2
        have h2 := hTsub j hy.2
        calc dist y x ≤ dist y (c j) + dist x (c j) := dist_triangle_right _ _ _
          _ < δ' / 2 + δ' / 2 := add_lt_add h2 h1
          _ = δ' := by ring
      have hpow : dist x y ^ k ≤ dist x y ^ (r : ℝ) := by
        rw [← Real.rpow_natCast]
        refine Real.rpow_le_rpow_of_exponent_ge_of_imp dist_nonneg ?_ hrk fun _ h ↦ ?_
        · rw [dist_comm]
          exact hdist.le.trans (min_le_right _ _)
        · exact absurd h (by exact_mod_cast hk0.ne')
      have hreal : dist (f x) (f y) ≤ (ε : ℝ) * dist x y ^ (r : ℝ) := by
        have h := hδA x hx.1 y hy.1
          (by simpa [dist_eq_norm] using hdist.trans_le (min_le_left _ _))
        rw [← dist_eq_norm, ← dist_eq_norm, dist_comm, dist_comm y] at h
        exact h.trans (mul_le_mul_of_nonneg_left hpow ε.coe_nonneg)
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul ε.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal hreal
    calc volume (f '' A)
        ≤ volume (⋃ j, f '' (A ∩ T j)) := by
          apply measure_mono
          rw [← image_iUnion, ← inter_iUnion, hTunion, inter_univ]
      _ ≤ ∑' j, volume (f '' (A ∩ T j)) := measure_iUnion_le _
      _ ≤ ∑' j, (ε : ℝ≥0∞) ^ (d : ℝ) * μ (B ∩ T j) := tsum_le_tsum fun j ↦ by
          have hh := (hhol j).hausdorffMeasure_image_le hr0 (d := d) (Nat.cast_nonneg _)
          have hsub : A ∩ T j ⊆ B ∩ T j := inter_subset_inter_left _ hAB
          rw [hrd, hd, hausdorffMeasure_pi_real] at hh
          exact hh.trans (mul_le_mul (le_refl _) (measure_mono hsub) bot_le bot_le)
      _ = (ε : ℝ≥0∞) ^ (d : ℝ) * μ B := by
          rw [ENNReal.tsum_mul_left, ← measure_iUnion
            (fun i j hij ↦ (disjoint_disjointed _ hij).mono inter_subset_right inter_subset_right)
            (fun j ↦ measurableSet_closedBall.inter
              (MeasurableSet.disjointed (fun _ ↦ measurableSet_ball) j)),
            ← inter_iUnion, hTunion, inter_univ]
  -- The containing ball has finite measure, so arbitrarily small Hölder constants force nullity.
  have htend : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) ^ (d : ℝ) * μ B) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ≥0 ↦ (ε : ℝ≥0∞) ^ (d : ℝ)) (𝓝 0) (𝓝 0) := by
      have h := (ENNReal.continuous_rpow_const (y := d)).tendsto 0 |>.comp
        (ENNReal.continuous_coe.tendsto (0 : ℝ≥0))
      simpa [Function.comp_def,
        ENNReal.zero_rpow_of_pos (show (0 : ℝ) < d by exact_mod_cast hd0)] using h
    simpa using (ENNReal.Tendsto.mul_const h0 (Or.inr hμ)).mono_left nhdsWithin_le_nhds
  exact le_antisymm (ge_of_tendsto htend (eventually_nhdsWithin_of_forall key)) bot_le

end TauCeti
