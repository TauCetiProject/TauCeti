/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Realization
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.DyadicSymbol
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.Normed.Operator.OfTendsto
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Completeness of homogeneous Besov spaces below the critical regularity

Let `n` be the dimension of `E` and let `s < n / p`, or `s = n / p` and `q = 1`
(`TauCeti.HomogeneousBesovSpace.RealizationCondition`, with `1 ≤ q`). Then the homogeneous Besov
space `\dot B^s_{p,q}` is complete
(`TauCeti.HomogeneousBesovSpace.completeSpace`). Its separation quotient, the normed space of
distributions in `\dot B^s_{p,q}` modulo those with spectrum at the origin, is then a Banach space
by `SeparationQuotient.instCompleteSpace`.

The proof shows that the realisation `u ↦ ∑_{j ∈ ℤ} Pⱼ u`
(`TauCeti.HomogeneousBesovSpace.realization`) depends continuously on `u`
(`TauCeti.HomogeneousBesovSpace.continuous_realization`), by splitting it at frequency `1` into
two parts that converge in Banach spaces.

* **Low frequencies.** By Bernstein's inequality
  (`TemperedDistribution.exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le`) the blocks
  `Pⱼ u`, `j ≤ 0`, are bounded functions with `‖Pⱼ u‖_∞ ≤ C 2^{jn/p} ‖Pⱼ u‖_p`. Since
  `2^{js} ‖Pⱼ u‖_p ≤ ‖u‖`, the sum over `j ≤ 0` converges in `L^∞` with norm `O(‖u‖)`:
  geometrically when `s < n / p`, and when `s = n / p`, `q = 1` because the weighted block norms
  sum to `‖u‖`.
* **High frequencies.** For `j ≥ 1` the block `Pⱼ` is the inhomogeneous block `Δⱼ`, and the Bessel
  potential `J^{s-1}` maps `Δⱼ u` to an `Lᵖ` function of norm `O(2^{j(s-1)} ‖Δⱼ u‖_p)`
  (`TemperedDistribution.exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le`), that is
  `O(2^{-j} ‖u‖)`. So `∑_{j ≥ 1} J^{s-1} Pⱼ u` converges in `Lᵖ` with norm `O(‖u‖)`, and the
  high-frequency part of the realisation is `J^{1-s}` of this sum.

A Cauchy sequence `uₖ` in `\dot B^s_{p,q}` therefore has realisations converging in the tempered
distributions, to some `v`, while its weighted blocks converge in `ℓ^q(ℤ, Lᵖ)`, to some `w`. The
blocks of `v` are the limits of the blocks of `uₖ`, so `w` is the sequence of weighted blocks of
`v`, and `uₖ → v` in `\dot B^s_{p,q}`. This is the argument for the inhomogeneous spaces
(`TauCeti.BesovSpace`), with the realisation in place of the distribution itself.

## Main declarations

* `TauCeti.HomogeneousBesovSpace.continuous_realization`: the realisation is continuous from
  `\dot B^s_{p,q}` to the tempered distributions.
* `TauCeti.HomogeneousBesovSpace.completeSpace`: `\dot B^s_{p,q}` is complete below the critical
  regularity.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Theorem 2.25.
-/

public section

noncomputable section

open MeasureTheory Filter Topology TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.HomogeneousBesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

variable (F φ s p q) in
/-- The partial sum `∑_{a < j ≤ b} Pⱼ u` of the homogeneous blocks, as a linear map of `u`. -/
private def blockSum (a b : ℤ) : HomogeneousBesovSpace F φ s p q →ₗ[ℂ] 𝓢'(E, F) where
  toFun u := ∑ j ∈ Finset.Ioc a b, homogeneousLittlewoodPaleyBlock F φ j u.toDistr
  map_add' u v := by simp only [toDistr_add, map_add, Finset.sum_add_distrib]
  map_smul' c u := by simp only [toDistr_smul, map_smul, Finset.smul_sum, RingHom.id_apply]

private theorem blockSum_apply (a b : ℤ) (u : HomogeneousBesovSpace F φ s p q) :
    blockSum F φ s p q a b u =
      ∑ j ∈ Finset.Ioc a b, homogeneousLittlewoodPaleyBlock F φ j u.toDistr := (rfl)

variable [Fact (1 ≤ q)]

/-- Below the critical regularity, the norms `‖Pⱼ u‖_p` weighted by `2^{jn/p}` are summable over
`j ≤ 0` (`Memℓp.summable_two_rpow_mul_neg`), with sum at most `K ‖u‖`: geometrically when
`s < n / p`, and when `s = n / p`, `q = 1` because the weighted block norms `2^{js} ‖Pⱼ u‖_p` sum
to `‖u‖`. -/
private theorem exists_summable_two_rpow_mul_norm_block_neg_and_tsum_le
    (hs : RealizationCondition E s p q) :
    ∃ K : ℝ, ∀ u : HomogeneousBesovSpace F φ s p q,
      Summable (fun k : ℕ ↦
        (2 : ℝ) ^ (Module.finrank ℝ E * p.toReal⁻¹ * (-k : ℤ)) * ‖u.block (-k)‖) ∧
      ∑' k : ℕ, (2 : ℝ) ^ (Module.finrank ℝ E * p.toReal⁻¹ * (-k : ℤ)) * ‖u.block (-k)‖ ≤
        K * ‖u‖ := by
  -- The weighted block norms `2^{js} ‖Pⱼ u‖_p` form an `ℓ^q` sequence.
  have hsum (u : HomogeneousBesovSpace F φ s p q) : Summable fun k : ℕ ↦
      (2 : ℝ) ^ (Module.finrank ℝ E * p.toReal⁻¹ * (-k : ℤ)) * ‖u.block (-k)‖ := by
    refine ((memℓp_norm_iff.2 u.weightedBlocks.prop).summable_two_rpow_mul_neg
      (fun _ ↦ norm_nonneg _) hs).congr fun k ↦ ?_
    rw [norm_weightedBlocks_apply, ← mul_assoc, Real.rpow_sub_mul_mul_rpow_mul two_pos]
  rcases hs with hs | ⟨rfl, hq⟩
  · -- The weights `2^{-k (n/p - s)}` decay geometrically, and `2^{-ks} ‖P₋ₖ u‖_p ≤ ‖u‖`.
    set r : ℝ := 2 ^ (-(Module.finrank ℝ E * p.toReal⁻¹ - s))
    have hr : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    have hle (u : HomogeneousBesovSpace F φ s p q) (k : ℕ) :
        (2 : ℝ) ^ (Module.finrank ℝ E * p.toReal⁻¹ * (-k : ℤ)) * ‖u.block (-k)‖ ≤ ‖u‖ * r ^ k := by
      have hw : (2 : ℝ) ^ (Module.finrank ℝ E * p.toReal⁻¹ * (-k : ℤ)) =
          r ^ k * 2 ^ (s * (-k : ℤ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
        push_cast
        ring_nf
      rw [hw, mul_assoc, mul_comm ‖u‖]
      exact mul_le_mul_of_nonneg_left (rpow_mul_norm_block_le u (-k)) (by positivity)
    have hgeom := summable_geometric_of_lt_one (by positivity) hr
    refine ⟨(1 - r)⁻¹, fun u ↦ ⟨hsum u, ?_⟩⟩
    calc _ ≤ ∑' k : ℕ, ‖u‖ * r ^ k := (hsum u).tsum_le_tsum (hle u) (hgeom.mul_left ‖u‖)
      _ = (1 - r)⁻¹ * ‖u‖ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr, mul_comm]
  · -- At the critical regularity `q = 1`, and the weighted block norms sum to at most `‖u‖`.
    obtain rfl : q = 1 := le_antisymm hq Fact.out
    refine ⟨1, fun u ↦ ⟨hsum u, (hsum u).tsum_le_of_sum_le fun t ↦ ?_⟩⟩
    have hinj : Function.Injective fun k : ℕ ↦ -(k : ℤ) := neg_injective.comp Nat.cast_injective
    simpa [Finset.sum_map, norm_weightedBlocks_apply, norm_weightedBlocks] using
      lp.sum_rpow_le_norm_rpow (by simp) u.weightedBlocks (t.map ⟨_, hinj⟩)

/-- **The low-frequency blocks sum in `L^∞`.** Below the critical regularity there is `C` such
that for every `u ∈ \dot B^s_{p,q}` the partial sums `∑_{a < j ≤ 0} Pⱼ u` converge, as `a → -∞`,
to a bounded function `g` with `‖g‖_∞ ≤ C ‖u‖`. -/
private theorem exists_tendsto_blockSum_atBot_and_norm_le (hs : RealizationCondition E s p q) :
    ∃ C : ℝ, ∀ u : HomogeneousBesovSpace F φ s p q, ∃ g : Lp F ∞ (volume : Measure E),
      Tendsto (fun a ↦ blockSum F φ s p q a 0 u) atBot
        (𝓝 (Lp.toTemperedDistributionCLM F volume ∞ g)) ∧ ‖g‖ ≤ C * ‖u‖ := by
  obtain ⟨C₀, hC₀, hB⟩ :=
    exists_homogeneousLittlewoodPaleyBlock_eq_and_norm_le_of_le (F := F) φ (le_top : p ≤ ∞)
  obtain ⟨K, hK⟩ := exists_summable_two_rpow_mul_norm_block_neg_and_tsum_le (φ := φ) (F := F) hs
  refine ⟨C₀ * K, fun u ↦ ?_⟩
  -- Bernstein's inequality: `‖P₋ₖ u‖_∞ ≤ C₀ 2^{-kn/p} ‖P₋ₖ u‖_p`.
  choose g hg hgn using fun k : ℕ ↦ hB (-k) u.toDistr (u.block (-k)) (coe_block u (-k)).symm
  simp only [ENNReal.toReal_top, inv_zero, sub_zero] at hgn
  have hgn' (k : ℕ) : ‖g k‖ ≤ C₀ *
      ((2 : ℝ) ^ (Module.finrank ℝ E * p.toReal⁻¹ * (-k : ℤ)) * ‖u.block (-k)‖) :=
    (hgn k).trans_eq (mul_assoc _ _ _)
  obtain ⟨w, hw⟩ := ((hK u).1.mul_left C₀).of_norm_bounded hgn'
  refine ⟨w, ?_, ?_⟩
  · have hlow := hw.map (Lp.toTemperedDistributionCLM F volume ∞)
      (Lp.toTemperedDistributionCLM F volume ∞).continuous
    simp only [Function.comp_def, Lp.toTemperedDistributionCLM_apply, ← hg] at hlow
    simpa only [blockSum_apply, Lp.toTemperedDistributionCLM_apply] using
      hlow.tendsto_sum_Ioc_atBot
  · refine (hw.norm_le_of_bounded ((hK u).1.mul_left C₀).hasSum hgn').trans ?_
    rw [tsum_mul_left, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK u).2 hC₀

/-- **The high-frequency blocks sum after a Bessel potential.** There is `C` such that for every
`u ∈ \dot B^s_{p,q}` the series `∑_{j ≥ 1} J^{s-1} Pⱼ u` converges in `Lᵖ` to some `h` with
`‖h‖_p ≤ C ‖u‖`, and the partial sums `∑_{0 < j ≤ b} Pⱼ u` converge to `J^{1-s} h` as `b → ∞`. -/
private theorem exists_tendsto_blockSum_atTop_and_norm_le :
    ∃ C : ℝ, ∀ u : HomogeneousBesovSpace F φ s p q, ∃ h : Lp F p (volume : Measure E),
      Tendsto (fun b ↦ blockSum F φ s p q 0 b u) atTop
        (𝓝 ((besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p) h)) ∧
        ‖h‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hJ⟩ :=
    exists_besselPotential_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ (s - 1)
  refine ⟨2 * C, fun u ↦ ?_⟩
  -- For `j ≥ 1` the homogeneous block `Pⱼ u` is the inhomogeneous block `Δⱼ u`.
  have hΔ (k : ℕ) : littlewoodPaleyBlock F φ (k + 1) u.toDistr = u.block ((k : ℤ) + 1) := by
    rw [coe_block, ← homogeneousLittlewoodPaleyBlock_natCast φ k.add_one_ne_zero, Nat.cast_add_one]
  choose g hg hgn using fun k : ℕ ↦ hJ (k + 1) u.toDistr _ (hΔ k)
  -- Since `2^{(k+1)s} ‖P_{k+1} u‖_p ≤ ‖u‖`, the `k`-th term is `O(2^{-k} ‖u‖)`.
  obtain ⟨w, hw, hwn⟩ := exists_hasSum_and_norm_le_of_two_rpow_mul_le
    (t := fun k ↦ ((k + 1 : ℕ) : ℝ)) hC0 (fun k ↦ by simp)
    (fun k ↦ by simpa using rpow_mul_norm_block_le u ((k : ℤ) + 1)) hgn
  refine ⟨w, ?_, hwn⟩
  · -- `J^{1-s} J^{s-1} P_{k+1} u = P_{k+1} u`.
    have hhigh := hw.map (besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p)
      (besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p).continuous
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply,
      Lp.toTemperedDistributionCLM_apply, ← hg, besselPotential_besselPotential_apply,
      show s - 1 + (1 - s) = 0 by ring, besselPotential_zero, ContinuousLinearMap.id_apply,
      hΔ, coe_block] at hhigh
    simpa only [blockSum_apply, ContinuousLinearMap.comp_apply,
      Lp.toTemperedDistributionCLM_apply] using hhigh.tendsto_sum_Ioc_atTop

variable (F φ s p q) in
/-- The low-frequency part `∑_{j ≤ 0} Pⱼ u` of the realisation, as a bounded linear map into
`L^∞`. -/
private def lowFrequencyLp (hs : RealizationCondition E s p q) :
    HomogeneousBesovSpace F φ s p q →L[ℂ] Lp F ∞ (volume : Measure E) :=
  .ofTendstoOfInjective (Lp.toTemperedDistributionCLM F volume ∞)
    (fun _ _ h ↦ Lp.toTemperedDistribution_injective h) (fun a ↦ blockSum F φ s p q a 0)
    (exists_tendsto_blockSum_atBot_and_norm_le hs).choose_spec

variable (F φ s p q) in
/-- The high-frequency part `∑_{j ≥ 1} J^{s-1} Pⱼ u` of the realisation, after the Bessel
potential `J^{s-1}`, as a bounded linear map into `Lᵖ`. -/
private def highFrequencyLp : HomogeneousBesovSpace F φ s p q →L[ℂ] Lp F p (volume : Measure E) :=
  .ofTendstoOfInjective (besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p)
    ((besselPotential_injective _).comp Lp.toTemperedDistribution_injective)
    (fun b ↦ blockSum F φ s p q 0 b) exists_tendsto_blockSum_atTop_and_norm_le.choose_spec

/-- The realisation is the sum of its low-frequency part and of `J^{1-s}` of its high-frequency
part. -/
private theorem realization_eq_add (hs : RealizationCondition E s p q)
    (u : HomogeneousBesovSpace F φ s p q) :
    realization hs u = Lp.toTemperedDistributionCLM F volume ∞ (lowFrequencyLp F φ s p q hs u) +
      (besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p)
        (highFrequencyLp F φ s p q u) := by
  have hlow : Tendsto (fun a ↦ blockSum F φ s p q a 0 u) atBot
      (𝓝 (Lp.toTemperedDistributionCLM F volume ∞ (lowFrequencyLp F φ s p q hs u))) :=
    ContinuousLinearMap.tendsto_ofTendstoOfInjective _ _ _ _ u
  have hhigh : Tendsto (fun b ↦ blockSum F φ s p q 0 b u) atTop
      (𝓝 ((besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p)
        (highFrequencyLp F φ s p q u))) :=
    ContinuousLinearMap.tendsto_ofTendstoOfInjective _ _ _ _ u
  simp only [blockSum_apply] at hlow hhigh
  exact tendsto_nhds_unique (tendsto_sum_realization hs u) (hlow.sum_Ioc_prod_atBot_atTop hhigh)

/-- **The realisation is continuous.** Below the critical regularity, the realisation
`u ↦ ∑_{j ∈ ℤ} Pⱼ u` is continuous from `\dot B^s_{p,q}` to the tempered distributions. -/
@[fun_prop]
theorem continuous_realization (hs : RealizationCondition E s p q) :
    Continuous (realization hs : HomogeneousBesovSpace F φ s p q → 𝓢'(E, F)) :=
  Continuous.congr (by fun_prop) fun u ↦ (realization_eq_add hs u).symm

/-- **Homogeneous Besov spaces are complete below the critical regularity.** For `1 ≤ q` and
`s < n / p`, or `s = n / p` and `q = 1`, where `n` is the dimension of `E`, the homogeneous Besov
space `\dot B^s_{p,q}` is complete. So is its separation quotient, the normed space of
distributions in `\dot B^s_{p,q}` modulo those with spectrum at the origin, by
`SeparationQuotient.instCompleteSpace`. -/
theorem completeSpace (hs : RealizationCondition E s p q) :
    CompleteSpace (HomogeneousBesovSpace F φ s p q) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  -- The weighted blocks converge in `ℓ^q(ℤ, Lᵖ)` to some `w`, and the two parts of the
  -- realisation converge in `L^∞` and `Lᵖ`, so the realisations converge to some `v`.
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    ((weightedBlocksₗᵢ F φ s p q).isometry.uniformContinuous.comp_cauchySeq hu)
  replace hw : Tendsto (fun n ↦ (u n).weightedBlocks) atTop (𝓝 w) := by
    simpa only [Function.comp_def, weightedBlocksₗᵢ_apply] using hw
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    ((lowFrequencyLp F φ s p q hs).uniformContinuous.comp_cauchySeq hu)
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete
    ((highFrequencyLp F φ s p q).uniformContinuous.comp_cauchySeq hu)
  set T := besselPotential E F (1 - s) ∘L Lp.toTemperedDistributionCLM F volume p
  have hv : Tendsto (fun n ↦ realization hs (u n)) atTop
      (𝓝 (Lp.toTemperedDistributionCLM F volume ∞ g + T h)) := by
    simp only [realization_eq_add hs]
    exact (((Lp.toTemperedDistributionCLM F volume ∞).continuous.tendsto g).comp hg).add
      ((T.continuous.tendsto h).comp hh)
  -- The blocks of `v` are the limits of the blocks of `u n`, so `w` is its sequence of weighted
  -- blocks.
  have hwv (j : ℤ) : (w j : 𝓢'(E, F)) = (((2 : ℝ) ^ (s * j) : ℝ) : ℂ) •
      homogeneousLittlewoodPaleyBlock F φ j (Lp.toTemperedDistributionCLM F volume ∞ g + T h) := by
    refine lp.map_apply_eq_of_tendsto hw hv (Lp.toTemperedDistributionCLM F volume p).continuous
      ((((2 : ℝ) ^ (s * j) : ℝ) : ℂ) • homogeneousLittlewoodPaleyBlock F φ j).continuous
      fun n ↦ ?_
    rw [FunLike.coe_smul, Pi.smul_apply,
      ← homogeneousLittlewoodPaleyBlock_eq_of_isVanishingOn_fourier_sub φ
        (isVanishingOn_fourier_toDistr_sub_realization hs (u n)) j]
    exact (u n).coe_weightedBlocks_apply j
  refine ⟨⟨_, w, hwv⟩, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  refine (tendsto_iff_norm_sub_tendsto_zero.1 hw).congr fun n ↦ ?_
  rw [← norm_weightedBlocks, weightedBlocks_sub]

end TauCeti.HomogeneousBesovSpace
