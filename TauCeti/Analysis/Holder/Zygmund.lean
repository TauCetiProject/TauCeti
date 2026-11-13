/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
public import TauCeti.Analysis.Holder.Normed
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder–Zygmund distributions of order `0 < α < 1` are Hölder functions

The Hölder–Zygmund space `𝒞^α = B^α_{∞,∞}` consists of the tempered distributions `u` whose
Littlewood–Paley blocks are bounded functions with `‖Δⱼ u‖_∞ ≤ 2^{-jα} ‖u‖`. For `0 < α < 1`
every such `u` is a bounded continuous `α`-Hölder function `f`, with

`‖f‖_∞ ≤ C ‖u‖` and `|f(x) - f(y)| ≤ C ‖u‖ ‖x - y‖^α`,

where `C` does not depend on `u`; it is built from `α` and the kernel of the bump function `φ` of
the partition. This is the inclusion
`𝒞^α ⊆ C^{0,α}` of the identification of the Hölder–Zygmund scale with the classical Hölder
spaces at non-integer order below one; it is the form in which `𝒞^α` regularity of a
distribution yields a pointwise Hölder bound.

Each block `Δⱼ u` has spectrum in the ball of radius `2^j φ.rOut`, so it is reproduced by the
low-pass multiplier `φ (2^{-(j + n₀)} ·)`, which equals one there once `φ.rOut ≤ 2^{n₀} φ.rIn`.
That multiplier is convolution with the `L¹`-normalised dilate `Kⱼ` of the Schwartz kernel
`K = 𝓕⁻ φ`, so `Gⱼ = Kⱼ ⋆ Δⱼ u` is an everywhere-defined representative of the block with
`‖Gⱼ‖_∞ ≤ ‖K‖₁ ‖Δⱼ u‖_∞` and Lipschitz constant `2^{j + n₀} ‖DK‖₁ ‖Δⱼ u‖_∞`. Summing the
Lipschitz bounds below the scale of `|x - y|` and the sup bounds above it gives the Hölder bound
for `f = ∑ⱼ Gⱼ` (`exists_holderWith_tsum_of_rpow_mul_le`). The partial sums of the blocks
converge to `f` in `L^∞` and to `u` in `𝓢'`, so `f` represents `u`.

## Main declarations

* `TauCeti.BesovSpace.exists_toLpTop_eq_and_norm_le_and_holderWith`: every `u ∈ 𝒞^α`,
  `0 < α < 1`, is the tempered distribution of a bounded continuous `α`-Hölder function `f` with
  `‖f‖_∞ ≤ C ‖u‖` and Hölder constant `C ‖u‖`.
* `TauCeti.BesovSpace.toHolderSpace`: the inclusion `𝒞^α → C^{0,α}` as a continuous linear map
  into the Hölder space with norm `‖f‖_∞ + [f]_α`, characterised by
  `TauCeti.BesovSpace.toHolderSpace_eq_iff` and `TauCeti.BesovSpace.toLpTop_toHolderSpace`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Section 2.5.7.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution ContinuousLinearMap Module Filter
open scoped ENNReal NNReal SchwartzMap Convolution Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

section Kernel

variable (φ : ContDiffBump (0 : E))

/-- The low-pass symbol `ξ ↦ φ (2^{-N} ξ)`, equal to one on the ball of radius `2^N φ.rIn`, as a
Schwartz function. -/
private def lowPass (N : ℕ) : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun ξ ↦ ((φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℝ) : ℂ))
    ((φ.hasCompactSupport.comp_smul (inv_ne_zero (pow_ne_zero _ two_ne_zero))).comp_left
      Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp (contDiff_const_smul _)))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_lowPass (N : ℕ) :
    ⇑(lowPass φ N) = fun ξ ↦ ((φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℝ) : ℂ) :=
  funext (HasCompactSupport.toSchwartzMap_toFun _ _)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_lowPass_eq_comp (N : ℕ) :
    ⇑(lowPass φ N) = fun ξ ↦ lowPass φ 0 (((2 : ℝ) ^ N)⁻¹ • ξ) := by
  simp [coe_lowPass]

/-- The kernel `𝓕⁻ (φ (2^{-N} ·))` is the `L¹`-normalised dilate `2^{Nn} K₀ (2^N ·)`. -/
private theorem fourierInv_lowPass_apply (N : ℕ) (y : E) :
    𝓕⁻ (⇑(lowPass φ N)) y =
      (((2 : ℝ) ^ N) ^ finrank ℝ E) • 𝓕⁻ (⇑(lowPass φ 0)) (((2 : ℝ) ^ N) • y) := by
  rw [coe_lowPass_eq_comp, fourierInv_comp_smul, inv_inv, inv_pow, abs_inv, inv_inv,
    abs_of_pos (by positivity)]

private theorem integral_norm_fourierInv_lowPass (N : ℕ) :
    ∫ y, ‖𝓕⁻ (⇑(lowPass φ N)) y‖ = ∫ y, ‖𝓕⁻ (⇑(lowPass φ 0)) y‖ := by
  rw [coe_lowPass_eq_comp]
  exact integral_norm_fourierInv_comp_smul _ (inv_ne_zero (pow_ne_zero _ two_ne_zero))

/-- Translating the kernel at scale `2^N` by `h` moves it in `L¹` by at most `D 2^N ‖h‖`. -/
private theorem integral_norm_fourierInv_lowPass_add_sub_le (N : ℕ) (h : E) :
    ∫ y, ‖𝓕⁻ (⇑(lowPass φ N)) (y + h) - 𝓕⁻ (⇑(lowPass φ N)) y‖ ≤
      (eLpNorm (fderiv ℝ (𝓕⁻ (lowPass φ 0) : 𝓢(E, ℂ))) 1 volume).toReal * (2 ^ N * ‖h‖) := by
  set K : 𝓢(E, ℂ) := 𝓕⁻ (lowPass φ 0)
  have hK : 𝓕⁻ (⇑(lowPass φ 0)) = ⇑K := (SchwartzMap.fourierInv_coe _).symm
  set c : ℝ := 2 ^ N
  have hc : 0 < c := by positivity
  -- Rescale to the kernel at scale `1`, translated by `c h`.
  have hscale : ∫ y, ‖𝓕⁻ (⇑(lowPass φ N)) (y + h) - 𝓕⁻ (⇑(lowPass φ N)) y‖ =
      ∫ z, ‖K (z + c • h) - K z‖ := by
    have hpt : ∀ y, 𝓕⁻ (⇑(lowPass φ N)) (y + h) - 𝓕⁻ (⇑(lowPass φ N)) y =
        (c ^ finrank ℝ E) • (K (c • y + c • h) - K (c • y)) := fun y ↦ by
      rw [fourierInv_lowPass_apply φ N, fourierInv_lowPass_apply φ N, hK, smul_add, smul_sub]
    simp_rw [hpt, norm_smul]
    rw [integral_const_mul, Measure.integral_comp_smul volume (fun z ↦ ‖K (z + c • h) - K z‖) c,
      smul_eq_mul, ← mul_assoc, Real.norm_eq_abs, abs_of_pos (by positivity),
      abs_inv, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_mul]
  have hfin : eLpNorm (fderiv ℝ ⇑K) 1 volume ≠ ∞ := by
    have : fderiv ℝ ⇑K = ⇑(SchwartzMap.fderivCLM ℝ E ℂ K) := by
      ext1 x
      rw [SchwartzMap.fderivCLM_apply]
    rw [this]
    exact (SchwartzMap.eLpNorm_lt_top _ 1 volume).ne
  have htrans := (K.smooth 1).eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv
    (mu := (volume : Measure E)) le_rfl (c • h)
  have hmeas : AEStronglyMeasurable (fun z ↦ K (z + c • h) - K z) volume :=
    ((K.continuous.comp (continuous_id.add continuous_const)).sub K.continuous).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_eNorm hmeas] at htrans
  rw [hscale]
  calc ∫ z, ‖K (z + c • h) - K z‖
      = (∫⁻ z, ‖K (z + c • h) - K z‖ₑ).toReal := integral_norm_eq_lintegral_eNorm hmeas
    _ ≤ (‖c • h‖ₑ * eLpNorm (fderiv ℝ ⇑K) 1 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top eNorm_ne_top hfin) htrans
    _ = _ := by
        rw [ENNReal.toReal_mul, toReal_eNorm, norm_smul, Real.norm_of_nonneg hc.le]
        ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- On the support of `ψⱼ` the low-pass symbol at scale `2^{j + n₀}` equals one, once
`φ.rOut ≤ 2^{n₀} φ.rIn`. -/
private theorem inhomogeneousLittlewoodPaley_mul_lowPass {n₀ : ℕ}
    (hn₀ : φ.rOut ≤ 2 ^ n₀ * φ.rIn) (j : ℕ) :
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) * ⇑(lowPass φ (j + n₀)) =
      fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
  ext ξ
  rw [Pi.mul_apply, coe_lowPass]
  by_cases hξ : φ.inhomogeneousLittlewoodPaley j ξ = 0
  · simp [hξ]
  have hball : ‖ξ‖ ≤ 2 ^ j * φ.rOut := mem_closedBall_zero_iff.1 <|
    φ.tsupport_inhomogeneousLittlewoodPaley_subset_closedBall j (subset_tsupport _ hξ)
  dsimp only
  rw [φ.one_of_mem_closedBall, Complex.ofReal_one, mul_one]
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity),
    inv_mul_le_iff₀ (by positivity), pow_add, mul_assoc]
  exact hball.trans (by gcongr)

/-- The smoothing `Kⱼ ⋆ g` of an `L^∞` function by the kernel `Kⱼ = 𝓕⁻ (φ (2^{-(j + n₀)} ·))`,
an everywhere-defined function. -/
private def smoothBlock (n₀ j : ℕ) (g : Lp F ∞ (volume : Measure E)) : E → F :=
  𝓕⁻ (⇑(lowPass φ (j + n₀))) ⋆[lsmul ℂ ℂ] (g : E → F)

private theorem integrable_fourierInv_lowPass (N : ℕ) : Integrable (𝓕⁻ (⇑(lowPass φ N))) := by
  rw [← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ (lowPass φ N)).integrable

omit [CompleteSpace F] in
/-- The smoothing of `g` is bounded by `‖K₀‖₁ ‖g‖_∞`. -/
private theorem norm_smoothBlock_le (n₀ j : ℕ) (g : Lp F ∞ (volume : Measure E)) (x : E) :
    ‖smoothBlock φ n₀ j g x‖ ≤ (∫ y, ‖𝓕⁻ (⇑(lowPass φ 0)) y‖) * ‖g‖ := by
  rw [← integral_norm_fourierInv_lowPass φ (j + n₀)]
  exact norm_convolution_lsmul_le_integral_norm_mul_norm (integrable_fourierInv_lowPass φ _) g x

omit [CompleteSpace F] in
/-- The smoothing of `g` at scale `2^{j + n₀}` is Lipschitz with constant
`‖D K₀‖₁ 2^{j + n₀} ‖g‖_∞`. -/
private theorem dist_smoothBlock_le (n₀ j : ℕ) (g : Lp F ∞ (volume : Measure E)) (x y : E) :
    dist (smoothBlock φ n₀ j g x) (smoothBlock φ n₀ j g y) ≤
      (eLpNorm (fderiv ℝ (𝓕⁻ (lowPass φ 0) : 𝓢(E, ℂ))) 1 volume).toReal * 2 ^ n₀ * 2 ^ j *
        dist x y * ‖g‖ := by
  have h := norm_convolution_lsmul_add_sub_le (integrable_fourierInv_lowPass φ (j + n₀)) g y
    (x - y)
  rw [add_sub_cancel] at h
  rw [dist_eq_norm]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (integral_norm_fourierInv_lowPass_add_sub_le φ (j + n₀) (x - y)).trans_eq ?_
  rw [dist_eq_norm, pow_add]
  ring

/-- **Reproducing a block.** An `L^∞` Littlewood–Paley block `g = Δⱼ v` is almost everywhere its
own smoothing at scale `2^{j + n₀}`, once `φ.rOut ≤ 2^{n₀} φ.rIn`. -/
private theorem ae_eq_smoothBlock {n₀ : ℕ} (hn₀ : φ.rOut ≤ 2 ^ n₀ * φ.rIn) {j : ℕ}
    {v : 𝓢'(E, F)} {g : Lp F ∞ (volume : Measure E)} (hg : littlewoodPaleyBlock F φ j v = g) :
    g =ᵐ[volume] smoothBlock φ n₀ j g := by
  have hrep : fourierMultiplierCLM F (lowPass φ (j + n₀)) (g : 𝓢'(E, F)) = g := by
    rw [← hg, littlewoodPaleyBlock_apply, fourierMultiplierCLM_fourierMultiplierCLM_apply
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)
      (lowPass φ (j + n₀)).hasTemperateGrowth, inhomogeneousLittlewoodPaley_mul_lowPass φ hn₀]
  exact ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq hrep

end Kernel

namespace BesovSpace

open BoundedContinuousFunction

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **Representing a distribution by a uniform limit.** If the `L^∞` blocks of `u` have
everywhere-defined representatives `Gⱼ` whose partial sums converge uniformly to a bounded
continuous `f`, then `f` is the tempered distribution `u`: the partial sums of the blocks converge
to `f` in `L^∞` and to `u` in `𝓢'`. -/
private theorem toLpTop_eq_toDistr_of_tendsto {s : ℝ} {q : ℝ≥0∞} {u : BesovSpace F φ s ∞ q}
    {G : ℕ → E → F} (hG : ∀ j, (u.block j : E → F) =ᵐ[volume] G j) {f : E →ᵇ F} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (htail : ∀ N x, ‖∑ j ∈ Finset.range N, G j x - f x‖ ≤ ε N) :
    (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr := by
  have hL : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, u.block j) atTop
      (𝓝 (toLpTop volume ℂ f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) hε
    refine Lp.norm_top_le_of_ae_bound ((norm_nonneg _).trans (htail N 0)) ?_
    filter_upwards [Lp.coeFn_sub (∑ j ∈ Finset.range N, u.block j) (toLpTop volume ℂ f),
      Lp.coeFn_finsetSum (Finset.range N) u.block, coeFn_toLpTop (𝕜 := ℂ) volume f,
      ae_all_iff.2 hG] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.sub_apply, h₂, h₃, Finset.sum_apply]
    simp_rw [h₄]
    exact htail N x
  refine tendsto_nhds_unique (((Lp.toTemperedDistributionCLM F volume ∞).continuous.tendsto _).comp
    hL) ?_
  simpa [Function.comp_def, map_sum] using tendsto_sum_littlewoodPaleyBlock φ u.toDistr

/-- **Hölder–Zygmund distributions of order `0 < α < 1` are Hölder functions.** There is a
constant `C` such that every `u ∈ 𝒞^α = B^α_{∞,∞}` is the tempered distribution of a bounded
continuous function `f` with `‖f‖_∞ ≤ C ‖u‖` which is `α`-Hölder with constant `C ‖u‖`. -/
theorem exists_toLpTop_eq_and_norm_le_and_holderWith (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ u : BesovSpace F φ α ∞ ∞, ∃ f : E →ᵇ F,
      (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr ∧ ‖f‖ ≤ C * ‖u‖ ∧
        HolderWith (C * ‖u‖₊) α f := by
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, φ.rOut ≤ 2 ^ n₀ * φ.rIn := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) (one_lt_two (α := ℝ))
    exact ⟨n, ((div_lt_iff₀ φ.rIn_pos).1 hn).le⟩
  obtain ⟨C₀, hC₀⟩ := exists_holderWith_tsum_of_rpow_mul_le (X := E) (Y := F) hα0 hα1
  -- The `L¹` norm `A` and the `L¹` modulus `D` of the kernel at scale `1`, and the ratio `q`.
  set A : ℝ := ∫ y, ‖𝓕⁻ (⇑(lowPass φ 0)) y‖
  set D : ℝ := (eLpNorm (fderiv ℝ (𝓕⁻ (lowPass φ 0) : 𝓢(E, ℂ))) 1 volume).toReal
  set q : ℝ := ((2 : ℝ) ^ (α : ℝ))⁻¹ with hq_def
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  have _ : 0 ≤ D := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hα0)
  have _ : 0 < 1 - q := sub_pos.2 hq1
  set C : ℝ≥0 := C₀ * (A.toNNReal + (D * 2 ^ n₀).toNNReal) + (A * (1 - q)⁻¹).toNNReal
  refine ⟨C, fun u ↦ ?_⟩
  -- The smoothed blocks `Gⱼ` represent the blocks `Δⱼ u`, which have `‖Δⱼ u‖_∞ ≤ ‖u‖ q^j`.
  set G : ℕ → E → F := fun j ↦ smoothBlock φ n₀ j (u.block j)
  have hblock := u.rpow_mul_norm_block_le
  have hGq : ∀ j x, ‖G j x‖ ≤ A * ‖u‖ * q ^ j := fun j x ↦ by
    have h := hblock j
    rw [Real.rpow_mul_natCast zero_le_two, ← inv_inv ((2 : ℝ) ^ (α : ℝ)), ← hq_def, inv_pow,
      inv_mul_le_iff₀ (by positivity)] at h
    exact (norm_smoothBlock_le φ n₀ j _ x).trans (by rw [mul_assoc]; gcongr; linarith)
  have ha : ∀ (j : ℕ) x, 2 ^ ((α : ℝ) * j) * ‖G j x‖ ≤ ((A.toNNReal * ‖u‖₊ : ℝ≥0) : ℝ) := by
    intro j x
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hA, coe_nnNorm]
    calc 2 ^ ((α : ℝ) * j) * ‖G j x‖ ≤ 2 ^ ((α : ℝ) * j) * (A * ‖u.block j‖) := by
          gcongr
          exact norm_smoothBlock_le φ n₀ j _ x
      _ = A * (2 ^ ((α : ℝ) * j) * ‖u.block j‖) := by ring
      _ ≤ A * ‖u‖ := by gcongr; exact hblock j
  have hb : ∀ (j : ℕ) x y, 2 ^ ((α : ℝ) * j) * dist (G j x) (G j y) ≤
      (((D * 2 ^ n₀).toNNReal * ‖u‖₊ : ℝ≥0) : ℝ) * 2 ^ j * dist x y := by
    intro j x y
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), coe_nnNorm]
    calc 2 ^ ((α : ℝ) * j) * dist (G j x) (G j y)
        ≤ 2 ^ ((α : ℝ) * j) * (D * 2 ^ n₀ * 2 ^ j * dist x y * ‖u.block j‖) := by
          gcongr
          exact dist_smoothBlock_le φ n₀ j _ x y
      _ = D * 2 ^ n₀ * 2 ^ j * dist x y * (2 ^ ((α : ℝ) * j) * ‖u.block j‖) := by ring
      _ ≤ D * 2 ^ n₀ * 2 ^ j * dist x y * ‖u‖ := by gcongr; exact hblock j
      _ = D * 2 ^ n₀ * ‖u‖ * 2 ^ j * dist x y := by ring
  -- The sum `f = ∑ⱼ Gⱼ` is Hölder and converges uniformly.
  have hH := hC₀ G _ _ ha hb
  have hsum : ∀ x, HasSum (fun j ↦ G j x) (∑' j, G j x) := fun x ↦
    (Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left (A * ‖u‖))
      fun j ↦ hGq j x).hasSum
  have htail : ∀ (N : ℕ) x, ‖∑ j ∈ Finset.range N, G j x - ∑' j, G j x‖ ≤
      A * ‖u‖ * q ^ N / (1 - q) := fun N x ↦
    norm_sub_le_of_geometric_bound_of_hasSum hq1 (fun j ↦ hGq j x) (hsum x) N
  have hbound : ∀ x, ‖∑' j, G j x‖ ≤ A * (1 - q)⁻¹ * ‖u‖ := fun x ↦ by
    simpa [norm_neg, div_eq_mul_inv, mul_right_comm] using htail 0 x
  have hCA : A * (1 - q)⁻¹ ≤ C :=
    calc A * (1 - q)⁻¹ = ((A * (1 - q)⁻¹).toNNReal : ℝ) :=
          (Real.coe_toNNReal _ (by positivity)).symm
      _ ≤ C := by exact_mod_cast le_add_self
  refine ⟨ofNormedAddCommGroup _ (hH.continuous hα0) _ hbound, ?_, ?_, ?_⟩
  · refine toLpTop_eq_toDistr_of_tendsto φ
      (fun j ↦ ae_eq_smoothBlock φ hn₀ (u.coe_block j).symm) ?_ (fun N x ↦ htail N x)
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (A * ‖u‖)).div_const
      (1 - q)
  · refine (norm_le (by positivity)).2 fun x ↦ (hbound x).trans ?_
    gcongr
  · refine hH.mono ?_
    rw [← add_mul, ← mul_assoc]
    gcongr
    exact le_self_add

/-- The constant of `exists_toLpTop_eq_and_norm_le_and_holderWith`. -/
private def holderConst (hα0 : 0 < α) (hα1 : α < 1) : ℝ≥0 :=
  (exists_toLpTop_eq_and_norm_le_and_holderWith (F := F) φ hα0 hα1).choose

/-- The bounded continuous `α`-Hölder function representing `u`. -/
private def holderRepr (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    E →ᵇ F :=
  ((exists_toLpTop_eq_and_norm_le_and_holderWith (F := F) φ hα0 hα1).choose_spec u).choose

private theorem holderRepr_spec (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    (toLpTop volume ℂ (holderRepr φ hα0 hα1 u) : 𝓢'(E, F)) = u.toDistr ∧
      ‖holderRepr φ hα0 hα1 u‖ ≤ holderConst (F := F) φ hα0 hα1 * ‖u‖ ∧
        HolderWith (holderConst (F := F) φ hα0 hα1 * ‖u‖₊) α (holderRepr φ hα0 hα1 u) :=
  ((exists_toLpTop_eq_and_norm_le_and_holderWith (F := F) φ hα0 hα1).choose_spec u).choose_spec

/-- A bounded continuous function representing `u` is `holderRepr u`. -/
private theorem holderRepr_eq (hα0 : 0 < α) (hα1 : α < 1) {u : BesovSpace F φ α ∞ ∞}
    {f : E →ᵇ F} (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) :
    holderRepr φ hα0 hα1 u = f :=
  toTemperedDistribution_toLpTop_injective (μ := volume) <| by
    dsimp only
    rw [(holderRepr_spec φ hα0 hα1 u).1, hf]

variable (F) in
/-- **The inclusion `𝒞^α ⊆ C^{0,α}`** for `0 < α < 1`: an element of the Hölder–Zygmund space
`B^α_{∞,∞}`, as the bounded continuous `α`-Hölder function representing it. -/
def toHolderSpace (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ α ∞ ∞ →L[ℝ] HolderSpace α E F :=
  LinearMap.mkContinuous
    { toFun u := HolderSpace.ofBoundedContinuousFunction (holderRepr φ hα0 hα1 u)
        (holderRepr_spec φ hα0 hα1 u).2.2.memHolder
      map_add' u v := HolderSpace.toBoundedContinuousFunction_injective <| by
        rw [HolderSpace.toBoundedContinuousFunction_add,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
        refine holderRepr_eq φ hα0 hα1 ?_
        rw [map_add, Lp.toTemperedDistribution_add, (holderRepr_spec φ hα0 hα1 _).1,
          (holderRepr_spec φ hα0 hα1 _).1, toDistr_add]
      map_smul' c u := HolderSpace.toBoundedContinuousFunction_injective <| by
        rw [RingHom.id_apply, HolderSpace.toBoundedContinuousFunction_smul,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
        refine holderRepr_eq φ hα0 hα1 ?_
        rw [← Complex.coe_smul c (holderRepr φ hα0 hα1 u), map_smul,
          Lp.toTemperedDistribution_smul, (holderRepr_spec φ hα0 hα1 _).1,
          ← Complex.coe_smul c u, toDistr_smul] }
    (2 * holderConst (F := F) φ hα0 hα1) fun u ↦ by
      obtain ⟨-, hnorm, hH⟩ := holderRepr_spec φ hα0 hα1 u
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      have hcoe : ⇑(HolderSpace.ofBoundedContinuousFunction (holderRepr φ hα0 hα1 u)
          (holderRepr_spec φ hα0 hα1 u).2.2.memHolder) = holderRepr φ hα0 hα1 u :=
        funext (HolderSpace.ofBoundedContinuousFunction_apply _ _)
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith
        (mul_nonneg (holderConst (F := F) φ hα0 hα1).coe_nonneg (norm_nonneg u))
        (fun x ↦ ?_) (hcoe ▸ hH)).trans ?_
      · rw [hcoe]
        exact ((holderRepr φ hα0 hα1 u).norm_coe_le_norm x).trans hnorm
      · push_cast
        linarith

private theorem toHolderSpace_apply (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    toHolderSpace F φ hα0 hα1 u = HolderSpace.ofBoundedContinuousFunction
      (holderRepr φ hα0 hα1 u) (holderRepr_spec φ hα0 hα1 u).2.2.memHolder :=
  (rfl)

private theorem toBoundedContinuousFunction_toHolderSpace (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ α ∞ ∞) :
    (toHolderSpace F φ hα0 hα1 u).toBoundedContinuousFunction = holderRepr φ hα0 hα1 u := by
  rw [toHolderSpace_apply, HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]

/-- The Hölder function `toHolderSpace F φ hα0 hα1 u` represents `u`: its tempered distribution is
`u`. -/
@[simp]
theorem toLpTop_toHolderSpace (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    (toLpTop volume ℂ (toHolderSpace F φ hα0 hα1 u).toBoundedContinuousFunction : 𝓢'(E, F)) =
      u.toDistr := by
  rw [toBoundedContinuousFunction_toHolderSpace]
  exact (holderRepr_spec φ hα0 hα1 u).1

/-- `toHolderSpace F φ hα0 hα1 u` is the only Hölder function representing `u`. -/
theorem toHolderSpace_eq_iff (hα0 : 0 < α) (hα1 : α < 1) {u : BesovSpace F φ α ∞ ∞}
    {f : HolderSpace α E F} :
    toHolderSpace F φ hα0 hα1 u = f ↔
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u.toDistr := by
  refine ⟨fun h ↦ h ▸ toLpTop_toHolderSpace φ hα0 hα1 u, fun h ↦ ?_⟩
  refine HolderSpace.toBoundedContinuousFunction_injective ?_
  rw [toBoundedContinuousFunction_toHolderSpace]
  exact holderRepr_eq φ hα0 hα1 h

end BesovSpace

end TauCeti
