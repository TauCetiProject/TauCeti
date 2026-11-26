/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Bernstein
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The critical homogeneous Besov space `\dot B^{n/2}_{2,1}` lies in `L^∞`

Let `V` be a nontrivial real inner product space of dimension `n` and let `Pⱼ`, `j ∈ ℤ`, be the
homogeneous Littlewood–Paley blocks built from a bump function `φ`, acting on `L²(V, F)` as the
Fourier multipliers with the cutoffs `ψⱼ` (`ContDiffBump.littlewoodPaley`). For `f ∈ L²(V, F)`,

`‖f‖_∞ ≤ C ∑ⱼ 2^{jn/2} ‖Pⱼ f‖₂`

with `C` depending only on `φ`
(`ContDiffBump.exists_eLpNorm_top_le_tsum_fourierMultiplierCLM_littlewoodPaley`). The right-hand
side is the norm of `f` in the homogeneous Besov space `\dot B^{n/2}_{2,1}`, so an `L²` function
of that space is essentially bounded
(`TemperedDistribution.MemHomogeneousBesov.memLp_top`).

This is the embedding behind the Strichartz estimates at the spatial exponent `r = ∞`, such as the
bound `‖cos(tD) f‖_{L^∞_t L^∞_x} ≤ C ‖f‖_{\dot B^{n/2}_{2,1}}` for the wave equation. The space
`\dot B^{n/2}_{2,1}` cannot be replaced there by the homogeneous Sobolev space
`\dot H^{n/2} = \dot B^{n/2}_{2,2}`, which is not contained in `L^∞`; see
`TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.LogLogExample`.

## The argument

Bernstein's inequality (`ContDiffBump.eLpNorm_dyadicMultiplier_le_of_le`) bounds each block,
`‖Pⱼ f‖_∞ ≤ C 2^{jn/2} ‖Pⱼ f‖₂`: some dyadic multiplier `Qⱼ` reproduces `Pⱼ`, and its kernel has
`L²` norm `2^{jn/2}` times that of `Q₀`. The partial sums `∑_{-N < j ≤ N} Pⱼ f` converge to `f` in
`L²` (`ContDiffBump.tendsto_sum_fourierMultiplierCLM_littlewoodPaley`), hence almost everywhere
along a subsequence, and their `L^∞` norms are at most `∑ⱼ ‖Pⱼ f‖_∞`. Fatou's lemma for the
essential supremum (`MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`) passes this bound to `f`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Chapter 2 (the
  embedding of `\dot B^{n/p}_{p,1}` into the bounded continuous functions).
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal FourierTransform SchwartzMap

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace ContDiffBump

variable (φ : ContDiffBump (0 : V))

/-- **The critical homogeneous Besov space `\dot B^{n/2}_{2,1}` lies in `L^∞`.** Let `V` be a
nontrivial real inner product space of dimension `n` and let `Pⱼ` be the `L²` Fourier multiplier
with the homogeneous Littlewood–Paley cutoff `ψⱼ` built from `φ`. There is `C` such that every
`f ∈ L²(V, F)` satisfies

`‖f‖_∞ ≤ C ∑ⱼ 2^{jn/2} ‖Pⱼ f‖₂`.

The right-hand side may be infinite. -/
theorem exists_eLpNorm_top_le_tsum_fourierMultiplierCLM_littlewoodPaley [Nontrivial V] :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure V),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm f ∞ volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ V : ℝ) / 2 * j)) *
            ‖Lp.fourierMultiplierCLM F (m j) f‖ₑ := by
  obtain ⟨σ, hσ⟩ := φ.exists_fourierMultiplierCLM_dyadicMultiplier_eq (F := F)
  set B := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + (∞ : ℝ≥0∞)⁻¹ - 2⁻¹)⁻¹ volume
  have hB : ((B.toNNReal : ℝ≥0) : ℝ≥0∞) = B :=
    ENNReal.coe_toNNReal (φ.memLp_fourierInv_dyadicDilate σ 0 _).eLpNorm_ne_top
  refine ⟨B.toNNReal, fun m hm f ↦ ?_⟩
  set P : ℤ → Lp F 2 (volume : Measure V) := fun j ↦ Lp.fourierMultiplierCLM F (m j) f
  -- Bernstein's inequality for each block: `‖Pⱼ f‖_∞ ≤ B 2^{jn/2} ‖Pⱼ f‖₂`.
  have hblock (j : ℤ) : eLpNorm (P j) ∞ volume ≤
      B * (ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ V : ℝ) / 2 * j)) * ‖P j‖ₑ) := by
    have hQP : φ.dyadicMultiplier F σ j (P j) = P j := by
      rw [dyadicMultiplier_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_comm,
        ← dyadicMultiplier_def, hσ j (m j) (hm j)]
    have h := φ.eLpNorm_dyadicMultiplier_le_of_le σ j (P j) one_le_two le_top
    rw [hQP] at h
    refine h.trans (le_of_eq ?_)
    rw [Lp.eNorm_def, ← Real.rpow_intCast, ← Real.rpow_mul zero_le_two]
    simp only [ENNReal.toReal_ofNat, ENNReal.toReal_top, inv_zero, sub_zero]
    rw [mul_comm (j : ℝ), mul_comm _ B, mul_assoc, div_eq_mul_inv]
  -- The partial sums converge to `f` in `L²`, hence almost everywhere along a subsequence.
  set S : ℕ → Lp F 2 (volume : Measure V) := fun N ↦ ∑ j ∈ Finset.Ioc (-(N : ℤ)) N, P j
  have hS : Tendsto S atTop (𝓝 f) := φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm f
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' S f).1 hS)).exists_seq_tendsto_ae
  -- Each partial sum is bounded in `L^∞` by the full sum of the block norms.
  have hSle (N : ℕ) : eLpNorm (S N) ∞ volume ≤ ∑' j, eLpNorm (P j) ∞ volume := by
    rw [eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)]
    exact (eLpNorm_sum_le le_top).trans (sum_le_tsum _)
  calc eLpNorm f ∞ volume
      ≤ atTop.liminf fun i ↦ eLpNorm (S (ns i)) ∞ volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun i ↦ Lp.aestronglyMeasurable _) f
          (Lp.aestronglyMeasurable f) hns
    _ ≤ ∑' j, eLpNorm (P j) ∞ volume :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun i ↦ hSle (ns i))
    _ ≤ ∑' j : ℤ, B * (ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ V : ℝ) / 2 * j)) *
          ‖P j‖ₑ) :=
        tsum_le_tsum hblock
    _ = _ := by rw [ENNReal.tsum_mul_left, hB]

end ContDiffBump

namespace TemperedDistribution

/-- **An `L²` function in `\dot B^{n/2}_{2,1}` is essentially bounded.** On a nontrivial real
inner product space `V` of dimension `n`, if the tempered distribution of `f ∈ L²(V, F)` lies in
the homogeneous Besov space `\dot B^{n/2}_{2,1}`, then `f ∈ L^∞`. The norm bound is
`ContDiffBump.exists_eLpNorm_top_le_tsum_fourierMultiplierCLM_littlewoodPaley`. -/
theorem MemHomogeneousBesov.memLp_top [Nontrivial V]
    {φ : ContDiffBump (0 : V)} {f : Lp F 2 (volume : Measure V)}
    (hf : (f : 𝓢'(V, F)).MemHomogeneousBesov φ ((Module.finrank ℝ V : ℝ) / 2) 2 1) :
    MemLp f ∞ volume := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_top_le_tsum_fourierMultiplierCLM_littlewoodPaley (F := F)
  set m : ℤ → Lp ℂ ∞ (volume : Measure V) := fun j ↦
    (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  -- The homogeneous blocks of `f` are the `L²` blocks `Pⱼ f`, and their weighted norms are
  -- summable.
  have hsum := (memHomogeneousBesov_iff_memℓp (f := fun j ↦ Lp.fourierMultiplierCLM F (m j) f)
    fun j ↦ homogeneousLittlewoodPaleyBlock_toTemperedDistribution φ (hm j) f).1 hf
  replace hsum : Summable fun j : ℤ ↦
      (2 : ℝ) ^ ((Module.finrank ℝ V : ℝ) / 2 * j) * ‖Lp.fourierMultiplierCLM F (m j) f‖ := by
    simpa using hsum.summable_of_one
  refine (hC m hm f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
  have hfin := ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hsum
  refine (le_of_eq ?_).trans_lt (hfin ▸ ENNReal.ofReal_lt_top)
  refine tsum_congr fun j ↦ ?_
  rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]

end TemperedDistribution
