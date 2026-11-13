/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.RankBound
public import TauCeti.Analysis.Matrix.SpectralMeasure.ResolventStability
public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence

/-!
# Negligible diagonal perturbations of empirical spectral measures

A diagonal perturbation preserves weak spectral limits if, for each positive threshold, the
proportion of its entries exceeding that threshold in absolute value tends to zero. Neither
its operator norm nor its normalized Frobenius norm needs to tend to zero.

The quantitative estimate splits the diagonal into a part of operator norm at most `ε` and a
part whose rank is at most the number of entries larger than `ε`. Applying the operator-norm
and rank bounds to their resolvent transforms yields weak-limit stability. This permits
removing heavy-tailed diagonals in global spectral laws without a moment hypothesis.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), proof of Theorem 2.1 (removal of the diagonal).
-/

public section

open Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Splitting a real diagonal at `ε` bounds the change in the spectral transform by a small
operator-norm error and a rank error counting the entries larger than `ε`. -/
theorem norm_resolventTransform_spectralMeasure_add_diagonal_sub_le
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (d : n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform ((A + diagonal (fun i ↦ (d i : ℂ))).spectralMeasure
          (hA.add (by simp [isHermitian_diagonal_iff, isSelfAdjoint_iff])) : Measure ℝ) z -
        resolventTransform (A.spectralMeasure hA : Measure ℝ) z‖ ≤
      ε / |z.im| ^ 2 +
        ((Finset.univ.filter fun i ↦ ε < |d i|).card : ℝ) /
          ((Fintype.card n : ℝ) * |z.im|) := by
  classical
  -- Separate the diagonal into small entries and the sparse remainder.
  let s : n → ℂ := fun i ↦ if |d i| ≤ ε then (d i : ℂ) else 0
  let t : n → ℂ := fun i ↦ if |d i| ≤ ε then 0 else (d i : ℂ)
  have hs : (diagonal s).IsHermitian := by
    apply isHermitian_diagonal_iff.2
    intro i
    dsimp [s]
    split_ifs <;> simp [isSelfAdjoint_iff]
  have ht : (diagonal t).IsHermitian := by
    apply isHermitian_diagonal_iff.2
    intro i
    dsimp [t]
    split_ifs <;> simp [isSelfAdjoint_iff]
  have hsplit : A + diagonal (fun i ↦ (d i : ℂ)) = (A + diagonal s) + diagonal t := by
    rw [add_assoc, diagonal_add]
    congr 2
    ext i
    dsimp [s, t]
    split_ifs <;> simp
  have hnorm : ‖diagonal s‖ ≤ ε := by
    rw [l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hε).2
    intro i
    dsimp [s]
    split_ifs with hi
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hi
    · simpa using hε
  have hrank : (diagonal t).rank ≤ (Finset.univ.filter fun i ↦ ε < |d i|).card := by
    rw [rank_diagonal, Fintype.card_subtype]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra! h
    exact hi (by simp [t, h])
  -- The two resolvent estimates control these parts independently of the ambient matrix.
  simp only [hsplit]
  have hsmall := norm_resolventTransform_spectralMeasure_sub_le_matrix
    (hA.add hs) hA hz
  have hlarge := (hA.add hs |>.add ht).norm_resolventTransform_spectralMeasure_sub_le_rank
    (hA.add hs) hz
  simp only [add_sub_cancel_left, norm_neg, sub_add_cancel_left] at hsmall hlarge
  calc
    _ ≤ ‖resolventTransform (((A + diagonal s) + diagonal t).spectralMeasure
            ((hA.add hs).add ht) : Measure ℝ) z -
          resolventTransform ((A + diagonal s).spectralMeasure (hA.add hs) : Measure ℝ) z‖ +
        ‖resolventTransform ((A + diagonal s).spectralMeasure (hA.add hs) : Measure ℝ) z -
          resolventTransform (A.spectralMeasure hA : Measure ℝ) z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (diagonal t).rank / ((Fintype.card n : ℝ) * |z.im|) +
        |z.im|⁻¹ * ‖diagonal s‖ * |z.im|⁻¹ := add_le_add hlarge hsmall
    _ ≤ ((Finset.univ.filter fun i ↦ ε < |d i|).card : ℝ) /
          ((Fintype.card n : ℝ) * |z.im|) + |z.im|⁻¹ * ε * |z.im|⁻¹ := by
      gcongr
    _ = _ := by ring

variable {ι : Type*} {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] {l : Filter ι}

/-- If the proportion of entries of a real diagonal larger than any fixed positive threshold
tends to zero, adding that diagonal changes each nonreal spectral transform by a quantity
tending to zero. -/
theorem tendsto_resolventTransform_spectralMeasure_add_diagonal_sub
    (A : (i : ι) → Matrix (m i) (m i) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (d : (i : ι) → m i → ℝ)
    (hd : ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦
      ((Finset.univ.filter fun j ↦ ε < |d i j|).card : ℝ) / Fintype.card (m i)) l (𝓝 0))
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun i ↦
      resolventTransform ((A i + diagonal (fun j ↦ (d i j : ℂ))).spectralMeasure
          ((hA i).add (by simp [isHermitian_diagonal_iff, isSelfAdjoint_iff])) : Measure ℝ) z -
        resolventTransform ((A i).spectralMeasure (hA i) : Measure ℝ) z) l (𝓝 0) := by
  classical
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun i ↦ ha.trans_le (norm_nonneg _)
  · intro δ hδ
    let ε := δ * |z.im| ^ 2 / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have htail := (hd ε hε).div_const |z.im|
    have htail' : Tendsto (fun i ↦
        ((Finset.univ.filter fun j ↦ ε < |d i j|).card : ℝ) /
          ((Fintype.card (m i) : ℝ) * |z.im|)) l (𝓝 0) := by
      simpa only [div_div, zero_div] using htail
    filter_upwards [htail'.eventually (gt_mem_nhds (half_pos hδ))] with i hi
    have h := norm_resolventTransform_spectralMeasure_add_diagonal_sub_le
      (A i) (hA i) (d i) hε.le hz
    have heq : ε / |z.im| ^ 2 = δ / 2 := by
      dsimp [ε]
      field_simp
    rw [heq] at h
    linarith

/-- Real diagonal perturbations with a vanishing proportion of entries above each positive
threshold preserve weak spectral limits, in both directions. The dimensions may vary, and
the limiting probability measure may have atoms. -/
theorem tendsto_spectralMeasure_add_diagonal_iff [l.IsCountablyGenerated]
    (A : (i : ι) → Matrix (m i) (m i) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (d : (i : ι) → m i → ℝ)
    (hd : ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦
      ((Finset.univ.filter fun j ↦ ε < |d i j|).card : ℝ) / Fintype.card (m i)) l (𝓝 0))
    (μ : ProbabilityMeasure ℝ) :
    Tendsto (fun i ↦ (A i + diagonal (fun j ↦ (d i j : ℂ))).spectralMeasure
        ((hA i).add (by simp [isHermitian_diagonal_iff, isSelfAdjoint_iff]))) l (𝓝 μ) ↔
      Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_resolventTransform,
    ProbabilityMeasure.tendsto_iff_tendsto_resolventTransform]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  exact tendsto_iff_of_dist <| by
    simpa only [dist_eq_norm, norm_zero] using
      (tendsto_resolventTransform_spectralMeasure_add_diagonal_sub A hA d hd hz.ne').norm

end Matrix
