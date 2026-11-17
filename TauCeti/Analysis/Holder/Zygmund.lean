/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder–Zygmund spaces of non-integer order are the Hölder spaces `C_b^{k,α}`

The Hölder–Zygmund space `𝒞^s = B^s_{∞,∞}` consists of the tempered distributions `u` whose
Littlewood–Paley blocks are bounded functions with `‖Δⱼ u‖_∞ ≤ 2^{-js} ‖u‖`. For non-integer
`s = k + α`, with `k : ℕ` and `0 < α < 1`, every such `u` is a bounded `C^k` function `f` whose
derivatives through order `k` are bounded and whose `k`-th derivative is `α`-Hölder:

`‖D^i f‖_∞ ≤ C ‖u‖` for `i ≤ k` and `‖D^k f(x) - D^k f(y)‖ ≤ C ‖u‖ ‖x - y‖^α`,

where `C` does not depend on `u`; it is built from `k`, `α` and the kernel of the bump function
`φ` of the partition. This is the inclusion `𝒞^{k+α} ⊆ C_b^{k,α}` of the identification of the
Hölder–Zygmund scale with the classical Hölder spaces at non-integer order; it is the form in
which `𝒞^s` regularity of a distribution yields pointwise bounds on its derivatives. For `k = 0`
it is the inclusion `𝒞^α ⊆ C^{0,α}` into the bounded Hölder functions.

Each block `Δⱼ u` has spectrum in the ball of radius `2^j φ.rOut`, so it is reproduced by the
low-pass multiplier `φ (2^{-(j + n₀)} ·)`, which equals one there once `φ.rOut ≤ 2^{n₀} φ.rIn`.
That multiplier is convolution with the `L¹`-normalised dilate
`Kⱼ = 2^{(j + n₀) n} K (2^{j + n₀} ·)` of the Schwartz kernel `K = 𝓕⁻ φ`, so `Gⱼ = Kⱼ ⋆ Δⱼ u` is
a smooth, everywhere-defined representative of the block. Its derivatives are convolutions of
`Δⱼ u` with the derivatives of `Kⱼ`, and `‖D^m Kⱼ‖₁ = 2^{(j + n₀) m} ‖D^m K‖₁`, so

`‖D^m Gⱼ‖_∞ ≤ 2^{(j + n₀) m} ‖D^m K‖₁ ‖Δⱼ u‖_∞ ≤ C_m 2^{j (m - k - α)} ‖u‖`.

For `m ≤ k` these bounds are summable in `j`, so `f = ∑ⱼ Gⱼ` is `C^k` with `D^m f = ∑ⱼ D^m Gⱼ`.
For the `k`-th derivatives, the sup bounds `O(2^{-jα})` together with the Lipschitz bounds
`O(2^{j (1 - α)})` coming from `m = k + 1` give the Hölder bound
(`exists_holderWith_tsum_of_rpow_mul_le`). The partial sums of the blocks converge to `f` in `L^∞`
and to `u` in `𝓢'`, so `f` represents `u`.

Conversely, every bounded `C^k` function `f` with `α`-Hölder `k`-th derivative, for any `α ≥ 0`,
is an element of `𝒞^{k+α}`: with `L` the Hölder constant of `D^k f`,

`‖Δⱼ f‖_∞ ≤ C 2^{-j (k + α)} (‖f‖_∞ + L)`.

For `j = 0` this is the uniform `L^∞` bound on the blocks. For `j ≥ 1` the block is the
convolution with the kernel `𝓕⁻ ψⱼ`, whose Fourier transform `ψⱼ` vanishes near the origin, so the
kernel annihilates every polynomial
(`ContDiffBump.integral_fourierInv_inhomogeneousLittlewoodPaley_succ_smul_apply_eq_zero`). Hence
`Δⱼ f (x)` is the integral of the kernel against the Taylor remainder of `f` at `x` of order `k`,
which is at most `L ‖y‖ ^ (k + α) / k!`
(`TauCeti.norm_map_add_sub_sum_iteratedFDeriv_le_of_holderWith`), and the moment of order `k + α`
of `𝓕⁻ ψⱼ` is `O(2^{-j (k + α)})`. Together with the first inclusion this identifies
`𝒞^{k+α}` with `C_b^{k,α}`, and `𝒞^α` with `C^{0,α}`, as Banach spaces, with equivalent norms,
for `0 < α < 1`.

## Main declarations

* `TauCeti.BesovSpace.exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith`:
  every `u ∈ 𝒞^{k+α}`, `0 < α < 1`, is the tempered distribution of a bounded `C^k` function `f`
  whose derivatives through order `k` are bounded by `C ‖u‖` and whose `k`-th derivative is
  `α`-Hölder with constant `C ‖u‖`.
* `TauCeti.BesovSpace.toCkHolderSpace`: the inclusion `𝒞^{k+α} → C_b^{k,α}` as a continuous
  linear map, characterised by `TauCeti.BesovSpace.toCkHolderSpace_eq_iff` and
  `TauCeti.BesovSpace.toLpTop_toCkHolderSpace`.
* `TauCeti.BesovSpace.exists_toLpTop_eq_and_norm_le_and_holderWith`: the case `k = 0`, every
  `u ∈ 𝒞^α` is a bounded continuous `α`-Hölder function.
* `TauCeti.BesovSpace.toHolderSpace`: the inclusion `𝒞^α → C^{0,α}` as a continuous linear map
  into the Hölder space with norm `‖f‖_∞ + [f]_α`, characterised by
  `TauCeti.BesovSpace.toHolderSpace_eq_iff` and `TauCeti.BesovSpace.toLpTop_toHolderSpace`.
* `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith`: conversely, every
  bounded `C^k` function with `α`-Hölder `k`-th derivative lies in `𝒞^{k+α}`, and
  `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_holderWith` is the case `k = 0`.
* `TauCeti.BesovSpace.ofCkHolderSpace` and `TauCeti.BesovSpace.ofHolderSpace`: the inclusions
  `C_b^{k,α} → 𝒞^{k+α}` and `C^{0,α} → 𝒞^α` as continuous linear maps, characterised by
  `TauCeti.BesovSpace.toDistr_ofCkHolderSpace` and `TauCeti.BesovSpace.toDistr_ofHolderSpace`.
* `TauCeti.BesovSpace.ckHolderSpaceEquiv` and `TauCeti.BesovSpace.holderSpaceEquiv`: for
  `0 < α < 1`, the isomorphisms `𝒞^{k+α} ≃ C_b^{k,α}` and `𝒞^α ≃ C^{0,α}`.

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

/-- The Schwartz kernel `𝓕⁻ (φ (2^{-N} ·))` of the low-pass multiplier at scale `2^N`. -/
private def kernel (N : ℕ) : 𝓢(E, ℂ) :=
  𝓕⁻ (lowPass φ N)

private theorem coe_kernel (N : ℕ) : ⇑(kernel φ N) = 𝓕⁻ (⇑(lowPass φ N)) :=
  SchwartzMap.fourierInv_coe _

/-- The derivatives of the kernel at scale `2^N`:
`‖D^m K_N y‖ = 2^{N n} 2^{N m} ‖D^m K₀ (2^N y)‖`. -/
private theorem norm_iteratedFDeriv_kernel (N m : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ m (kernel φ N) y‖ = ((2 : ℝ) ^ N) ^ finrank ℝ E *
      (((2 : ℝ) ^ N) ^ m * ‖iteratedFDeriv ℝ m (kernel φ 0) (((2 : ℝ) ^ N) • y)‖) := by
  have hK : ContDiff ℝ m (kernel φ 0) := ((kernel φ 0).smooth ⊤).of_le (by exact_mod_cast le_top)
  have hdil : ⇑(kernel φ N) =
      fun y ↦ (((2 : ℝ) ^ N) ^ finrank ℝ E) • kernel φ 0 (((2 : ℝ) ^ N) • y) := by
    funext y
    rw [coe_kernel, fourierInv_lowPass_apply, coe_kernel]
  rw [hdil, iteratedFDeriv_const_smul_apply' (f := fun y ↦ kernel φ 0 (((2 : ℝ) ^ N) • y))
      (hK.comp (contDiff_const_smul _)).contDiffAt,
    iteratedFDeriv_comp_const_smul _ hK, norm_smul, norm_smul, norm_pow, norm_pow,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]

/-- `‖D^m K_N‖₁ = 2^{N m} ‖D^m K₀‖₁`. -/
private theorem integral_norm_iteratedFDeriv_kernel (N m : ℕ) :
    ∫ y, ‖iteratedFDeriv ℝ m (kernel φ N) y‖ =
      ((2 : ℝ) ^ N) ^ m * ∫ y, ‖iteratedFDeriv ℝ m (kernel φ 0) y‖ := by
  simp_rw [norm_iteratedFDeriv_kernel φ N m]
  rw [integral_const_mul, integral_const_mul,
    Measure.integral_comp_smul volume (fun z ↦ ‖iteratedFDeriv ℝ m (kernel φ 0) z‖), smul_eq_mul,
    abs_of_pos (by positivity)]
  field_simp

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
  ⇑(kernel φ (j + n₀)) ⋆[lsmul ℝ ℂ] (g : E → F)

omit [CompleteSpace F] in
/-- The smoothing of an `L^∞` function is smooth. -/
private theorem contDiff_smoothBlock (n₀ j : ℕ) (g : Lp F ∞ (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothBlock φ n₀ j g) :=
  contDiff_convolution_left_of_dominated _ ((kernel φ (j + n₀)).smooth ⊤)
    (fun n _ ↦ (kernel φ (j + n₀)).exists_integrable_norm_iteratedFDeriv_add_le n)
    (Lp.aestronglyMeasurable g) (Lp.ae_norm_le_norm_top g)

omit [CompleteSpace F] in
/-- The derivatives of the smoothing of `g` at scale `2^{j + n₀}`:
`‖D^m (Kⱼ ⋆ g)‖ ≤ ‖D^m K₀‖₁ 2^{(j + n₀) m} ‖g‖_∞`. -/
private theorem norm_iteratedFDeriv_smoothBlock_le (n₀ j m : ℕ)
    (g : Lp F ∞ (volume : Measure E)) (x : E) :
    ‖iteratedFDeriv ℝ m (smoothBlock φ n₀ j g) x‖ ≤
      (∫ y, ‖iteratedFDeriv ℝ m (kernel φ 0) y‖) * ((2 : ℝ) ^ (j + n₀)) ^ m * ‖g‖ := by
  -- The bilinear map of the differentiated convolution, `(A, b) ↦ (v ↦ A v • b)`, is bounded by
  -- the product of the norms.
  set L := ((compContinuousMultilinearMapL ℝ (fun _ : Fin m ↦ E) ℂ F).comp
    (lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).flip).flip
  have hL : ∀ A b, ‖L A b‖ ≤ ‖A‖ * ‖b‖ := fun A b ↦ by
    simp only [L, flip_apply, comp_apply, compContinuousMultilinearMapL_apply]
    calc ‖((lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).flip b).compContinuousMultilinearMap A‖
        ≤ ‖(lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).flip b‖ * ‖A‖ :=
          norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖b‖ * ‖A‖ := by
          gcongr
          exact opNorm_le_bound _ (norm_nonneg b) fun a ↦ by
            rw [flip_apply, lsmul_apply, norm_smul, mul_comm]
      _ = ‖A‖ * ‖b‖ := mul_comm _ _
  have hK : Integrable (iteratedFDeriv ℝ m (kernel φ (j + n₀))) :=
    (integrable_norm_iff (((kernel φ (j + n₀)).smooth ⊤).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).aestronglyMeasurable).1
      ((kernel φ (j + n₀)).integrable_norm_iteratedFDeriv m)
  rw [smoothBlock, iteratedFDeriv_convolution_left_of_dominated _ ((kernel φ (j + n₀)).smooth ⊤)
    (fun n _ ↦ (kernel φ (j + n₀)).exists_integrable_norm_iteratedFDeriv_add_le n)
    (Lp.aestronglyMeasurable g) (Lp.ae_norm_le_norm_top g) (by exact_mod_cast le_top),
    mul_comm (∫ y, _), ← integral_norm_iteratedFDeriv_kernel]
  refine (norm_convolution_le_integral_norm_mul_norm L hK g x).trans ?_
  rw [mul_assoc]
  exact mul_le_of_le_one_left (by positivity)
    (opNorm_le_bound₂ L zero_le_one fun A b ↦ by rw [one_mul]; exact hL A b)

/-- The constant `2^{n₀ m} ‖D^m K₀‖₁`, which bounds the `m`-th derivatives of the smoothing of a
block `Δⱼ u` at scale `2^{j + n₀}` by `2^{jm} ‖Δⱼ u‖_∞` times itself. -/
private def blockConst (n₀ m : ℕ) : ℝ :=
  (∫ y, ‖iteratedFDeriv ℝ m (kernel φ 0) y‖) * ((2 : ℝ) ^ n₀) ^ m

private theorem blockConst_nonneg (n₀ m : ℕ) : 0 ≤ blockConst φ n₀ m :=
  mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)

/-- **Reproducing a block.** An `L^∞` Littlewood–Paley block `g = Δⱼ v` is almost everywhere its
own smoothing at scale `2^{j + n₀}`, once `φ.rOut ≤ 2^{n₀} φ.rIn`. -/
private theorem ae_eq_smoothBlock {n₀ : ℕ} (hn₀ : φ.rOut ≤ 2 ^ n₀ * φ.rIn) {j : ℕ}
    {v : 𝓢'(E, F)} {g : Lp F ∞ (volume : Measure E)} (hg : littlewoodPaleyBlock F φ j v = g) :
    g =ᵐ[volume] smoothBlock φ n₀ j g := by
  have hrep : fourierMultiplierCLM F (lowPass φ (j + n₀)) (g : 𝓢'(E, F)) = g := by
    rw [← hg, littlewoodPaleyBlock_apply, fourierMultiplierCLM_fourierMultiplierCLM_apply
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)
      (lowPass φ (j + n₀)).hasTemperateGrowth, inhomogeneousLittlewoodPaley_mul_lowPass φ hn₀]
  have hconv : 𝓕⁻ (⇑(lowPass φ (j + n₀))) ⋆[lsmul ℂ ℂ] (g : E → F) = smoothBlock φ n₀ j g := by
    ext x
    simp only [smoothBlock, coe_kernel, convolution_def, lsmul_apply]
  exact hconv ▸ ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq hrep

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


/-- **The derivatives of the smoothed blocks.** For `u ∈ 𝒞^{k+α}`, the smoothing `Gⱼ` of the block
`Δⱼ u` at scale `2^{j + n₀}` satisfies `2^{jk} 2^{jα} ‖D^m Gⱼ‖ ≤ 2^{jm} 2^{n₀ m} ‖D^m K₀‖₁ ‖u‖`. -/
private theorem pow_mul_rpow_mul_norm_iteratedFDeriv_smoothBlock_le {k : ℕ} (n₀ m j : ℕ)
    (u : BesovSpace F φ (k + α) ∞ ∞) (x : E) :
    ((2 : ℝ) ^ j) ^ k * (2 ^ ((α : ℝ) * j) *
        ‖iteratedFDeriv ℝ m (smoothBlock φ n₀ j (u.block j)) x‖) ≤
      ((2 : ℝ) ^ j) ^ m * (blockConst φ n₀ m * ‖u‖) := by
  have hsplit : (2 : ℝ) ^ (((k : ℝ) + α) * j) = ((2 : ℝ) ^ j) ^ k * 2 ^ ((α : ℝ) * j) := by
    rw [add_mul, Real.rpow_add two_pos, mul_comm (k : ℝ), Real.rpow_mul_natCast zero_le_two,
      Real.rpow_natCast]
  calc ((2 : ℝ) ^ j) ^ k * (2 ^ ((α : ℝ) * j) *
        ‖iteratedFDeriv ℝ m (smoothBlock φ n₀ j (u.block j)) x‖)
      ≤ 2 ^ (((k : ℝ) + α) * j) * ((∫ y, ‖iteratedFDeriv ℝ m (kernel φ 0) y‖) *
          ((2 : ℝ) ^ (j + n₀)) ^ m * ‖u.block j‖) := by
        rw [hsplit, mul_assoc]
        gcongr
        exact norm_iteratedFDeriv_smoothBlock_le φ n₀ j m _ x
    _ = ((2 : ℝ) ^ j) ^ m * blockConst φ n₀ m * (2 ^ (((k : ℝ) + α) * j) * ‖u.block j‖) := by
        rw [blockConst, pow_add, mul_pow]
        ring
    _ ≤ ((2 : ℝ) ^ j) ^ m * blockConst φ n₀ m * ‖u‖ := mul_le_mul_of_nonneg_left
        (u.rpow_mul_norm_block_le j) (mul_nonneg (by positivity) (blockConst_nonneg φ n₀ m))
    _ = _ := mul_assoc _ _ _

/-- Through order `k`, the smoothed blocks of `u ∈ 𝒞^{k+α}` satisfy
`2^{jα} ‖D^m Gⱼ‖ ≤ 2^{n₀ m} ‖D^m K₀‖₁ ‖u‖`. -/
private theorem rpow_mul_norm_iteratedFDeriv_smoothBlock_le {k m : ℕ} (hm : m ≤ k) (n₀ j : ℕ)
    (u : BesovSpace F φ (k + α) ∞ ∞) (x : E) :
    2 ^ ((α : ℝ) * j) * ‖iteratedFDeriv ℝ m (smoothBlock φ n₀ j (u.block j)) x‖ ≤
      blockConst φ n₀ m * ‖u‖ :=
  le_of_mul_le_mul_left ((pow_mul_rpow_mul_norm_iteratedFDeriv_smoothBlock_le φ n₀ m j u x).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_pow₀ one_le_two) hm)
      (mul_nonneg (blockConst_nonneg φ n₀ m) (norm_nonneg u)))) (by positivity)

/-- The `k`-th derivatives of the smoothed blocks of `u ∈ 𝒞^{k+α}` are Lipschitz, by the bound of
order `k + 1`: `2^{jα} ‖D^k Gⱼ x - D^k Gⱼ y‖ ≤ 2^j 2^{n₀ (k + 1)} ‖D^{k+1} K₀‖₁ ‖u‖ ‖x - y‖`. -/
private theorem rpow_mul_dist_iteratedFDeriv_smoothBlock_le {k : ℕ} (n₀ j : ℕ)
    (u : BesovSpace F φ (k + α) ∞ ∞) (x y : E) :
    2 ^ ((α : ℝ) * j) * dist (iteratedFDeriv ℝ k (smoothBlock φ n₀ j (u.block j)) x)
        (iteratedFDeriv ℝ k (smoothBlock φ n₀ j (u.block j)) y) ≤
      blockConst φ n₀ (k + 1) * ‖u‖ * 2 ^ j * dist x y := by
  set G := smoothBlock φ n₀ j (u.block j)
  have hpos : (0 : ℝ) < 2 ^ ((α : ℝ) * j) := by positivity
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k G) :=
    (contDiff_smoothBlock φ n₀ j _).differentiable_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top k)
  have hM : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ k G) z‖ ≤
      blockConst φ n₀ (k + 1) * ‖u‖ * 2 ^ j / 2 ^ ((α : ℝ) * j) := fun z ↦ by
    rw [norm_fderiv_iteratedFDeriv, le_div_iff₀ hpos, mul_comm]
    exact le_of_mul_le_mul_left
      ((pow_mul_rpow_mul_norm_iteratedFDeriv_smoothBlock_le φ n₀ (k + 1) j u z).trans_eq
        (by ring)) (by positivity : (0 : ℝ) < ((2 : ℝ) ^ j) ^ k)
  have hlip := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hdiff z)
    (fun z _ ↦ hM z) (Set.mem_univ y) (Set.mem_univ x)
  rw [dist_eq_norm, dist_eq_norm]
  calc 2 ^ ((α : ℝ) * j) * ‖iteratedFDeriv ℝ k G x - iteratedFDeriv ℝ k G y‖
      ≤ 2 ^ ((α : ℝ) * j) *
          (blockConst φ n₀ (k + 1) * ‖u‖ * 2 ^ j / 2 ^ ((α : ℝ) * j) * ‖x - y‖) := by
        gcongr
    _ = blockConst φ n₀ (k + 1) * ‖u‖ * 2 ^ j * ‖x - y‖ := by field_simp

/-- **Hölder–Zygmund distributions of non-integer order are `C^{k,α}` functions.** Let `k : ℕ` and
`0 < α < 1`. There is a constant `C` such that every `u ∈ 𝒞^{k+α} = B^{k+α}_{∞,∞}` is the tempered
distribution of a bounded continuous `C^k` function `f` whose derivatives through order `k` are
bounded by `C ‖u‖` and whose `k`-th derivative is `α`-Hölder with constant `C ‖u‖`. -/
theorem exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (k : ℕ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ u : BesovSpace F φ (k + α) ∞ ∞, ∃ f : E →ᵇ F,
      (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr ∧ ContDiff ℝ k f ∧
        (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C * ‖u‖) ∧
          HolderWith (C * ‖u‖₊) α (iteratedFDeriv ℝ k f) := by
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, φ.rOut ≤ 2 ^ n₀ * φ.rIn := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) (one_lt_two (α := ℝ))
    exact ⟨n, ((div_lt_iff₀ φ.rIn_pos).1 hn).le⟩
  obtain ⟨C₀, hC₀⟩ := exists_holderWith_tsum_of_rpow_mul_le (X := E) (Y := E [×k]→L[ℝ] F) hα0 hα1
  -- `B m = 2^{n₀ m} ‖D^m K₀‖₁` bounds the `m`-th derivatives of the smoothed blocks, and
  -- `q = 2^{-α}` is the ratio of the geometric series they form.
  set B : ℕ → ℝ := blockConst φ n₀
  set q : ℝ := ((2 : ℝ) ^ (α : ℝ))⁻¹ with hq_def
  have hB : ∀ m, 0 ≤ B m := blockConst_nonneg φ n₀
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hα0)
  have hq1' : 0 < 1 - q := sub_pos.2 hq1
  set D : ℝ := (∑ i ∈ Finset.range (k + 1), B i) * (1 - q)⁻¹
  have hD : 0 ≤ D := mul_nonneg (Finset.sum_nonneg fun i _ ↦ hB i) (inv_nonneg.2 hq1'.le)
  set C : ℝ≥0 := C₀ * ((B k).toNNReal + (B (k + 1)).toNNReal) + D.toNNReal
  refine ⟨C, fun u ↦ ?_⟩
  -- The smoothed blocks `Gⱼ` represent the blocks `Δⱼ u`.
  set G : ℕ → E → F := fun j ↦ smoothBlock φ n₀ j (u.block j)
  have hG : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j) := fun j ↦ contDiff_smoothBlock φ n₀ j _
  have hgeom : ∀ m ≤ k, ∀ (j : ℕ) (x : E), ‖iteratedFDeriv ℝ m (G j) x‖ ≤ B m * ‖u‖ * q ^ j := by
    intro m hm j x
    have h := rpow_mul_norm_iteratedFDeriv_smoothBlock_le φ hm n₀ j u x
    rw [Real.rpow_mul_natCast zero_le_two, ← inv_inv ((2 : ℝ) ^ (α : ℝ)), ← hq_def, inv_pow,
      inv_mul_le_iff₀ (by positivity)] at h
    exact h.trans_eq (mul_comm _ _)
  -- The sum `f = ∑ⱼ Gⱼ` is `C^k`, and its derivatives are the sums of the derivatives.
  set f₀ : E → F := fun x ↦ ∑' j, G j x
  have hGk : ∀ j, ContDiff ℝ k (G j) := fun j ↦ (hG j).of_le (by exact_mod_cast le_top)
  have hf₀ : ContDiff ℝ k f₀ :=
    contDiff_tsum_of_norm_iteratedFDeriv_le_geometric hGk hq0 hq1 hgeom
  have hDf₀ : ∀ i ≤ k, iteratedFDeriv ℝ i f₀ = fun x ↦ ∑' j, iteratedFDeriv ℝ i (G j) x :=
    fun i hi ↦ iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric hGk hq0 hq1 hgeom hi
  have hDf₀_le : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f₀ x‖ ≤ D * ‖u‖ := fun i hi x ↦ by
    refine (norm_iteratedFDeriv_tsum_le_of_geometric hGk hq0 hq1 hgeom hi x).trans ?_
    rw [mul_right_comm]
    gcongr
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ ↦ hB i)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) (inv_nonneg.2 hq1'.le)
  -- The `k`-th derivative is `α`-Hölder: the sup bounds of order `k` and the Lipschitz bounds
  -- coming from order `k + 1`.
  have ha : ∀ (j : ℕ) x, 2 ^ ((α : ℝ) * j) * ‖iteratedFDeriv ℝ k (G j) x‖ ≤
      (((B k).toNNReal * ‖u‖₊ : ℝ≥0) : ℝ) := fun j x ↦ by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (hB k), coe_nnNorm]
    exact rpow_mul_norm_iteratedFDeriv_smoothBlock_le φ le_rfl n₀ j u x
  have hb : ∀ (j : ℕ) x y, 2 ^ ((α : ℝ) * j) *
      dist (iteratedFDeriv ℝ k (G j) x) (iteratedFDeriv ℝ k (G j) y) ≤
        (((B (k + 1)).toNNReal * ‖u‖₊ : ℝ≥0) : ℝ) * 2 ^ j * dist x y := fun j x y ↦ by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (hB _), coe_nnNorm]
    exact rpow_mul_dist_iteratedFDeriv_smoothBlock_le φ n₀ j u x y
  have hH : HolderWith (C * ‖u‖₊) α (iteratedFDeriv ℝ k f₀) := by
    rw [hDf₀ k le_rfl]
    refine (hC₀ (fun j ↦ iteratedFDeriv ℝ k (G j)) _ _ ha hb).mono ?_
    rw [← add_mul, ← mul_assoc]
    gcongr
    exact le_self_add
  -- `f` is bounded, and represents `u`.
  have hbound : ∀ x, ‖f₀ x‖ ≤ D * ‖u‖ := fun x ↦ by
    simpa only [norm_iteratedFDeriv_zero] using hDf₀_le 0 (Nat.zero_le k) x
  have hsum : ∀ x, HasSum (fun j ↦ G j x) (f₀ x) := fun x ↦
    (Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left (B 0 * ‖u‖))
      fun j ↦ by
      simpa only [norm_iteratedFDeriv_zero] using hgeom 0 (Nat.zero_le k) j x).hasSum
  have htail : ∀ (N : ℕ) x, ‖∑ j ∈ Finset.range N, G j x - f₀ x‖ ≤
      B 0 * ‖u‖ * q ^ N / (1 - q) := fun N x ↦
    norm_sub_le_of_geometric_bound_of_hasSum hq1 (fun j ↦ by
      simpa only [norm_iteratedFDeriv_zero] using hgeom 0 (Nat.zero_le k) j x) (hsum x) N
  have hDC : D ≤ C :=
    calc D = (D.toNNReal : ℝ) := (Real.coe_toNNReal _ hD).symm
      _ ≤ C := by exact_mod_cast le_add_self
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup f₀ hf₀.continuous _ hbound, ?_, hf₀,
    fun i hi x ↦ (hDf₀_le i hi x).trans (by gcongr), hH⟩
  refine toLpTop_eq_toDistr_of_tendsto φ
    (fun j ↦ ae_eq_smoothBlock φ hn₀ (u.coe_block j).symm) ?_ (fun N x ↦ htail N x)
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (B 0 * ‖u‖)).div_const
    (1 - q)

/-- **Hölder–Zygmund distributions of order `0 < α < 1` are Hölder functions.** There is a
constant `C` such that every `u ∈ 𝒞^α = B^α_{∞,∞}` is the tempered distribution of a bounded
continuous function `f` with `‖f‖_∞ ≤ C ‖u‖` which is `α`-Hölder with constant `C ‖u‖`. -/
theorem exists_toLpTop_eq_and_norm_le_and_holderWith (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ u : BesovSpace F φ α ∞ ∞, ∃ f : E →ᵇ F,
      (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr ∧ ‖f‖ ≤ C * ‖u‖ ∧
        HolderWith (C * ‖u‖₊) α f := by
  obtain ⟨C, hC⟩ :=
    exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (F := F) φ 0 hα0 hα1
  rw [Nat.cast_zero, zero_add] at hC
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨f, hf, -, hbound, hH⟩ := hC u
  refine ⟨f, hf, (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ by
    simpa only [norm_iteratedFDeriv_zero] using hbound 0 le_rfl x, ?_⟩
  -- The `0`-th derivative is `f` up to the isometry `F ≃ (E [×0]→L[ℝ] F)`.
  refine fun x y ↦ ?_
  have h := hH x y
  rwa [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply,
    LinearIsometryEquiv.edist_map] at h

/-- A bounded continuous function representing `u` is the value at `u` of any map `R` choosing a
representative of every element. -/
private theorem repr_eq {s : ℝ} {R : BesovSpace F φ s ∞ ∞ → E →ᵇ F}
    (hR : ∀ u, (toLpTop volume ℂ (R u) : 𝓢'(E, F)) = u.toDistr) {u : BesovSpace F φ s ∞ ∞}
    {f : E →ᵇ F} (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) :
    R u = f :=
  toTemperedDistribution_toLpTop_injective (μ := volume) <| by
    dsimp only
    rw [hR, hf]

/-- A map choosing a bounded continuous representative of every element is additive. -/
private theorem repr_add {s : ℝ} {R : BesovSpace F φ s ∞ ∞ → E →ᵇ F}
    (hR : ∀ u, (toLpTop volume ℂ (R u) : 𝓢'(E, F)) = u.toDistr) (u v : BesovSpace F φ s ∞ ∞) :
    R (u + v) = R u + R v :=
  repr_eq φ hR <| by rw [map_add, Lp.toTemperedDistribution_add, hR, hR, toDistr_add]

/-- A map choosing a bounded continuous representative of every element is homogeneous. -/
private theorem repr_smul {s : ℝ} {R : BesovSpace F φ s ∞ ∞ → E →ᵇ F}
    (hR : ∀ u, (toLpTop volume ℂ (R u) : 𝓢'(E, F)) = u.toDistr) (c : ℝ)
    (u : BesovSpace F φ s ∞ ∞) :
    R (c • u) = c • R u :=
  repr_eq φ hR <| by
    rw [← Complex.coe_smul c (R u), map_smul, Lp.toTemperedDistribution_smul, hR,
      ← Complex.coe_smul c u, toDistr_smul]

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
        exact repr_add φ (fun u ↦ (holderRepr_spec φ hα0 hα1 u).1) u v
      map_smul' c u := HolderSpace.toBoundedContinuousFunction_injective <| by
        rw [RingHom.id_apply, HolderSpace.toBoundedContinuousFunction_smul,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction,
          HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
        exact repr_smul φ (fun u ↦ (holderRepr_spec φ hα0 hα1 u).1) c u }
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
  exact repr_eq φ (fun u ↦ (holderRepr_spec φ hα0 hα1 u).1) h


/-- The constant of `exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith`. -/
private def ckConst (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) : ℝ≥0 :=
  (exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (F := F) φ k hα0
    hα1).choose

/-- The bounded continuous `C^k` function representing `u`. -/
private def ckRepr (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ (k + α) ∞ ∞) :
    E →ᵇ F :=
  ((exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (F := F) φ k hα0
    hα1).choose_spec u).choose

private theorem ckRepr_spec (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    (toLpTop volume ℂ (ckRepr φ k hα0 hα1 u) : 𝓢'(E, F)) = u.toDistr ∧
      ContDiff ℝ k (ckRepr φ k hα0 hα1 u) ∧
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (ckRepr φ k hα0 hα1 u) x‖ ≤
        ckConst (F := F) φ k hα0 hα1 * ‖u‖) ∧
      HolderWith (ckConst (F := F) φ k hα0 hα1 * ‖u‖₊) α
        (iteratedFDeriv ℝ k (ckRepr φ k hα0 hα1 u)) :=
  ((exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (F := F) φ k hα0
    hα1).choose_spec u).choose_spec

/-- The bounded `C^{k,α}` map representing `u`. -/
private def ckHolderRepr (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ (k + α) ∞ ∞) :
    CkHolderSpace k α E F :=
  CkHolderSpace.ofContDiff (ckRepr φ k hα0 hα1 u) (ckRepr_spec φ k hα0 hα1 u).2.1
    (fun i hi ↦ ⟨_, (ckRepr_spec φ k hα0 hα1 u).2.2.1 i hi⟩)
    (ckRepr_spec φ k hα0 hα1 u).2.2.2.memHolder

private theorem coe_ckHolderRepr (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    ⇑(ckHolderRepr φ k hα0 hα1 u) = ckRepr φ k hα0 hα1 u :=
  CkHolderSpace.coe_ofContDiff _ _ _ _

variable (F) in
/-- **The inclusion `𝒞^{k+α} ⊆ C_b^{k,α}`** for `0 < α < 1`: an element of the Hölder–Zygmund
space `B^{k+α}_{∞,∞}`, as the bounded `C^k` map with bounded derivatives through order `k` and
`α`-Hölder `k`-th derivative representing it. -/
def toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ (k + α) ∞ ∞ →L[ℝ] CkHolderSpace k α E F :=
  LinearMap.mkContinuous
    { toFun := ckHolderRepr φ k hα0 hα1
      map_add' u v := CkHolderSpace.ext fun x ↦ by
        simp only [CkHolderSpace.coe_add, Pi.add_apply, coe_ckHolderRepr,
          repr_add φ (fun u ↦ (ckRepr_spec φ k hα0 hα1 u).1), FunLike.coe_add]
      map_smul' c u := CkHolderSpace.ext fun x ↦ by
        simp only [RingHom.id_apply, CkHolderSpace.coe_smul, Pi.smul_apply, coe_ckHolderRepr,
          repr_smul φ (fun u ↦ (ckRepr_spec φ k hα0 hα1 u).1), FunLike.coe_smul] }
    ((k + 2) * ckConst (F := F) φ k hα0 hα1) fun u ↦ by
      obtain ⟨-, -, hbd, hH⟩ := ckRepr_spec φ k hα0 hα1 u
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      refine (CkHolderSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderWith
        (M := ckConst (F := F) φ k hα0 hα1 * ‖u‖) (fun i hi x ↦ ?_)
        (by rw [coe_ckHolderRepr]; exact hH)).trans (le_of_eq ?_)
      · rw [coe_ckHolderRepr]
        exact hbd i hi x
      · push_cast
        ring

private theorem toCkHolderSpace_apply (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    toCkHolderSpace F φ k hα0 hα1 u = ckHolderRepr φ k hα0 hα1 u :=
  (rfl)

private theorem toBoundedContinuousFunction_toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    (toCkHolderSpace F φ k hα0 hα1 u).toBoundedContinuousFunction = ckRepr φ k hα0 hα1 u := by
  ext x
  rw [CkHolderSpace.coe_toBoundedContinuousFunction, toCkHolderSpace_apply, coe_ckHolderRepr]

/-- The `C^{k,α}` map `toCkHolderSpace F φ k hα0 hα1 u` represents `u`: its tempered distribution
is `u`. -/
@[simp]
theorem toLpTop_toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    (toLpTop volume ℂ (toCkHolderSpace F φ k hα0 hα1 u).toBoundedContinuousFunction :
      𝓢'(E, F)) = u.toDistr := by
  rw [toBoundedContinuousFunction_toCkHolderSpace]
  exact (ckRepr_spec φ k hα0 hα1 u).1

/-- `toCkHolderSpace F φ k hα0 hα1 u` is the only `C^{k,α}` map representing `u`. -/
theorem toCkHolderSpace_eq_iff (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ (k + α) ∞ ∞} {f : CkHolderSpace k α E F} :
    toCkHolderSpace F φ k hα0 hα1 u = f ↔
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u.toDistr := by
  refine ⟨fun h ↦ h ▸ toLpTop_toCkHolderSpace φ k hα0 hα1 u, fun h ↦ CkHolderSpace.ext fun x ↦ ?_⟩
  rw [toCkHolderSpace_apply, coe_ckHolderRepr, repr_eq φ (fun u ↦ (ckRepr_spec φ k hα0 hα1 u).1) h,
    CkHolderSpace.coe_toBoundedContinuousFunction]

/-! ### The converse inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}` -/

omit [CompleteSpace F] in
/-- The kernel of `Δ_{j+1}` annihilates the Taylor polynomial of `f` at `x`, so its convolution
with `f` at `x` only sees the Taylor remainder, of size `L ‖y‖ ^ (k + α) / k!`. -/
private theorem norm_fourierInv_convolution_le {k : ℕ} {α L : ℝ≥0} {f : E →ᵇ F}
    (hf : ContDiff ℝ k f) (hH : HolderWith L α (iteratedFDeriv ℝ k f)) (j : ℕ) (x : E) :
    ‖(𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) ⋆[lsmul ℂ ℂ] (f : E → F)) x‖ ≤
      L / k.factorial * ∫ y, ‖y‖ ^ ((k : ℝ) + α) *
        ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) y‖ := by
  set K : 𝓢(E, ℂ) := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz (j + 1))
  have hK : (K : E → ℂ) = 𝓕⁻ fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ) := by
    rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  rw [← hK]
  -- The Taylor polynomial `P y` of `f` at `x`, evaluated at `x - y`, is a sum of homogeneous
  -- polynomials `A i (y, …, y)`, each annihilated by `K`.
  set A : (i : ℕ) → E [×i]→L[ℝ] F := fun i ↦
    ((i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f x).compContinuousLinearMap
      fun _ ↦ -ContinuousLinearMap.id ℝ E
  set P : E → F := fun y ↦ ∑ i ∈ Finset.range (k + 1), A i (fun _ ↦ y)
  have hPint : Integrable (fun y ↦ K y • P y) := by
    simp_rw [P, Finset.smul_sum]
    exact integrable_finsetSum _ fun i _ ↦ K.integrable_smul_apply (A i)
  have hP : ∫ y, K y • P y = 0 := by
    simp_rw [P, Finset.smul_sum]
    rw [integral_finsetSum _ fun i _ ↦ K.integrable_smul_apply (A i)]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [hK]
      exact φ.integral_fourierInv_inhomogeneousLittlewoodPaley_succ_smul_apply_eq_zero j (A i)
  have hfint : Integrable (fun y ↦ K y • f (x - y)) :=
    (K.integrable.norm.mul_const ‖f‖).mono'
      (K.continuous.smul
        (f.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _))
  -- Taylor's theorem with the Hölder remainder bounds the integrand.
  set s : ℝ := k + α
  have hR (y : E) : ‖K y • (f (x - y) - P y)‖ ≤ L / k.factorial * (‖y‖ ^ s * ‖K y‖) := by
    have hT := norm_map_add_sub_sum_iteratedFDeriv_le_of_holderWith hf hH x (-y)
    rw [← sub_eq_add_neg, norm_neg] at hT
    have hPy : P y = ∑ i ∈ Finset.range (k + 1),
        (i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f x (fun _ ↦ -y) := by
      simp [P, A]
    rw [norm_smul, hPy]
    calc ‖K y‖ * ‖f (x - y) - ∑ i ∈ Finset.range (k + 1),
          (i.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ i f x (fun _ ↦ -y)‖
        ≤ ‖K y‖ * (L * ‖y‖ ^ s / k.factorial) := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = L / k.factorial * (‖y‖ ^ s * ‖K y‖) := by ring
  rw [convolution_def]
  simp only [lsmul_apply]
  rw [← sub_zero (∫ y, K y • f (x - y)), ← hP, ← integral_sub hfint hPint, ← integral_const_mul]
  refine norm_integral_le_of_norm_le
    ((K.integrable_norm_rpow_mul_norm (by positivity)).const_mul _) (.of_forall fun y ↦ ?_)
  rw [← smul_sub]
  exact hR y

/-- **Bounded `C^{k,α}` functions are Hölder–Zygmund distributions of order `k + α`.** There is a
constant `C` such that for every bounded continuous `f` which is `C^k` with `α`-Hölder `k`-th
derivative, with Hölder constant `L`, the tempered distribution of `f` lies in
`𝒞^{k+α} = B^{k+α}_{∞,∞}` with norm at most `C (‖f‖_∞ + L)`. -/
theorem exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (k : ℕ) (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F), ContDiff ℝ k f → ∀ {L : ℝ≥0},
      HolderWith L α (iteratedFDeriv ℝ k f) →
        ∃ u : BesovSpace F φ (k + α) ∞ ∞, u.toDistr = toLpTop volume ℂ f ∧
          ‖u‖ ≤ C * (‖f‖ + L) := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set s : ℝ := k + α
  set M₁ := ∫ y, ‖y‖ ^ s * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  set C := max C₀ (2 ^ s * M₁ / k.factorial)
  have hC : 0 ≤ C := (le_max_right _ _).trans' (by positivity)
  refine ⟨C, hC, fun f hf L hH ↦ ?_⟩
  choose g hg hgn using fun j ↦ hC₀ (p := ∞) j (toLpTop volume ℂ f)
  have hbound (j : ℕ) : 2 ^ (s * j) * ‖g j‖ ≤ C * (‖f‖ + L) := by
    rcases j with _ | j
    · rw [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
      exact (hgn 0).trans (mul_le_mul (le_max_left _ _)
        ((norm_toLpTop_le (𝕜 := ℂ) volume f).trans (le_add_of_nonneg_right L.coe_nonneg))
        (norm_nonneg _) hC)
    -- For `j ≥ 1` the block is the convolution with `𝓕⁻ ψ_{j+1}`, which only sees the
    -- Taylor remainder of `f`.
    have hconv : 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) ⋆[lsmul ℂ ℂ]
        (toLpTop volume ℂ f : E → F) =
        𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) ⋆[lsmul ℂ ℂ] (f : E → F) :=
      convolution_congr _ (EventuallyEq.refl _ _) (coeFn_toLpTop (𝕜 := ℂ) volume f)
    have hgj : ‖g (j + 1)‖ ≤ L / k.factorial * (((2 ^ j : ℝ) ^ s)⁻¹ * M₁) := by
      rw [← φ.integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ s j]
      refine Lp.norm_top_le_of_ae_bound (by positivity) ?_
      filter_upwards [ae_eq_convolution_of_littlewoodPaleyBlock_eq φ (j + 1) (hg (j + 1))]
        with x hx
      rw [hx, hconv]
      exact norm_fourierInv_convolution_le φ hf hH j x
    have h2 : (2 : ℝ) ^ (s * (j + 1 : ℕ)) * ((2 ^ j : ℝ) ^ s)⁻¹ = 2 ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← Real.rpow_neg zero_le_two,
        ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    calc 2 ^ (s * (j + 1 : ℕ)) * ‖g (j + 1)‖
        ≤ 2 ^ (s * (j + 1 : ℕ)) * (L / k.factorial * (((2 ^ j : ℝ) ^ s)⁻¹ * M₁)) := by gcongr
      _ = 2 ^ s * M₁ / k.factorial * L := by
          rw [← h2]
          ring
      _ ≤ C * (‖f‖ + L) := mul_le_mul (le_max_right _ _)
          (le_add_of_nonneg_left (norm_nonneg f)) L.coe_nonneg hC
  -- The constant sequence `C (‖f‖ + L)` is an `ℓ^∞` majorant of the weighted blocks.
  set c : ℝ := C * (‖f‖ + L)
  have hc : 0 ≤ c := by positivity
  let b : lp (fun _ : ℕ ↦ ℝ) ∞ := ⟨fun _ ↦ c, memℓp_infty ⟨c, by
    rintro _ ⟨k, rfl⟩
    exact (Real.norm_of_nonneg hc).le⟩⟩
  obtain ⟨u, hu, hub⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq g b hg hbound
  exact ⟨u, hu, hub.trans (lp.norm_le_of_forall_le hc fun _ ↦ (Real.norm_of_nonneg hc).le)⟩

/-- **Bounded Hölder functions are Hölder–Zygmund distributions of order `α`.** There is a
constant `C` such that for every bounded continuous `α`-Hölder `f`, with Hölder constant `L`, the
tempered distribution of `f` lies in `𝒞^α = B^α_{∞,∞}` with norm at most `C (‖f‖_∞ + L)`. -/
theorem exists_toDistr_eq_and_norm_le_of_holderWith (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F) {L : ℝ≥0}, HolderWith L α f →
      ∃ u : BesovSpace F φ α ∞ ∞, u.toDistr = toLpTop volume ℂ f ∧ ‖u‖ ≤ C * (‖f‖ + L) := by
  obtain ⟨C, hC, h⟩ := exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := F) φ 0 α
  refine ⟨C, hC, fun f L hH ↦ ?_⟩
  have h0 := h f (contDiff_zero.2 f.continuous) (L := L) fun x y ↦ by
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply,
      LinearIsometryEquiv.edist_map]
    exact hH x y
  rwa [Nat.cast_zero, zero_add] at h0

/-- The constant of `exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith`. -/
private def ofCkConst (k : ℕ) (α : ℝ≥0) : ℝ :=
  (exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := F) φ k α).choose

/-- The element of `𝒞^{k+α}` represented by a bounded `C^{k,α}` map, with the norm bound. -/
private theorem exists_toDistr_eq_ckHolderSpace (k : ℕ) {α : ℝ≥0} (f : CkHolderSpace k α E F) :
    ∃ u : BesovSpace F φ (k + α) ∞ ∞,
      u.toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction ∧
        ‖u‖ ≤ 2 * ofCkConst (F := F) φ k α * ‖f‖ := by
  obtain ⟨hC, h⟩ :=
    (exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := F) φ k α).choose_spec
  obtain ⟨u, hu, hun⟩ := h f.toBoundedContinuousFunction (by simpa using f.contDiff)
    (L := nnHolderNorm α (iteratedFDeriv ℝ k f))
    (by simpa using f.memHolder_iteratedFDeriv.holderWith)
  refine ⟨u, hu, hun.trans ?_⟩
  have hf : ‖f.toBoundedContinuousFunction‖ + (nnHolderNorm α (iteratedFDeriv ℝ k f) : ℝ) ≤
      2 * ‖f‖ := by
    linarith [f.norm_toBoundedContinuousFunction_le, f.nnHolderNorm_iteratedFDeriv_le]
  calc ofCkConst (F := F) φ k α * (‖f.toBoundedContinuousFunction‖ +
        (nnHolderNorm α (iteratedFDeriv ℝ k f) : ℝ))
      ≤ ofCkConst (F := F) φ k α * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hf hC
    _ = 2 * ofCkConst (F := F) φ k α * ‖f‖ := by ring

/-- The element of `𝒞^{k+α}` represented by a bounded `C^{k,α}` map. -/
private def ckBesovRepr (k : ℕ) {α : ℝ≥0} (f : CkHolderSpace k α E F) :
    BesovSpace F φ (k + α) ∞ ∞ :=
  (exists_toDistr_eq_ckHolderSpace φ k f).choose

private theorem toDistr_ckBesovRepr (k : ℕ) {α : ℝ≥0} (f : CkHolderSpace k α E F) :
    (ckBesovRepr φ k f).toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction :=
  (exists_toDistr_eq_ckHolderSpace φ k f).choose_spec.1

variable (F) in
/-- **The inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}`**: a bounded `C^k` map with bounded derivatives through
order `k` and `α`-Hölder `k`-th derivative, as an element of the Hölder–Zygmund space
`B^{k+α}_{∞,∞}`. -/
def ofCkHolderSpace (k : ℕ) (α : ℝ≥0) :
    CkHolderSpace k α E F →L[ℝ] BesovSpace F φ (k + α) ∞ ∞ :=
  LinearMap.mkContinuous
    { toFun := ckBesovRepr φ k
      map_add' f g := ext <| by
        simp only [toDistr_add, toDistr_ckBesovRepr, CkHolderSpace.toBoundedContinuousFunction_add,
          map_add, Lp.toTemperedDistribution_add]
      -- A real scalar acts as its complex coercion, for which every map in the chain is linear.
      map_smul' c f := ext <| by
        simp only [RingHom.id_apply, ← Complex.coe_smul, toDistr_smul, toDistr_ckBesovRepr,
          CkHolderSpace.toBoundedContinuousFunction_smul, map_smul,
          Lp.toTemperedDistribution_smul] }
    (2 * ofCkConst (F := F) φ k α) fun f ↦ (exists_toDistr_eq_ckHolderSpace φ k f).choose_spec.2

/-- The element `ofCkHolderSpace F φ k α f` of `𝒞^{k+α}` is the tempered distribution of `f`. -/
@[simp]
theorem toDistr_ofCkHolderSpace (k : ℕ) {α : ℝ≥0} (f : CkHolderSpace k α E F) :
    (ofCkHolderSpace F φ k α f).toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction :=
  toDistr_ckBesovRepr φ k f

/-- The constant of `exists_toDistr_eq_and_norm_le_of_holderWith`. -/
private def ofHolderConst (α : ℝ≥0) : ℝ :=
  (exists_toDistr_eq_and_norm_le_of_holderWith (F := F) φ α).choose

/-- The element of `𝒞^α` represented by a bounded `α`-Hölder function, with the norm bound. -/
private theorem exists_toDistr_eq_holderSpace {α : ℝ≥0} (f : HolderSpace α E F) :
    ∃ u : BesovSpace F φ α ∞ ∞, u.toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction ∧
      ‖u‖ ≤ 2 * ofHolderConst (F := F) φ α * ‖f‖ := by
  obtain ⟨hC, h⟩ := (exists_toDistr_eq_and_norm_le_of_holderWith (F := F) φ α).choose_spec
  obtain ⟨u, hu, hun⟩ := h f.toBoundedContinuousFunction (L := ‖f‖₊)
    (by simpa using f.holderWith_nnnorm)
  refine ⟨u, hu, hun.trans ?_⟩
  have hf : ‖f.toBoundedContinuousFunction‖ + (‖f‖₊ : ℝ) ≤ 2 * ‖f‖ := by
    rw [coe_nnNorm]
    linarith [f.norm_toBoundedContinuousFunction_le]
  calc ofHolderConst (F := F) φ α * (‖f.toBoundedContinuousFunction‖ + (‖f‖₊ : ℝ))
      ≤ ofHolderConst (F := F) φ α * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hf hC
    _ = 2 * ofHolderConst (F := F) φ α * ‖f‖ := by ring

/-- The element of `𝒞^α` represented by a bounded `α`-Hölder function. -/
private def holderBesovRepr {α : ℝ≥0} (f : HolderSpace α E F) : BesovSpace F φ α ∞ ∞ :=
  (exists_toDistr_eq_holderSpace φ f).choose

private theorem toDistr_holderBesovRepr {α : ℝ≥0} (f : HolderSpace α E F) :
    (holderBesovRepr φ f).toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction :=
  (exists_toDistr_eq_holderSpace φ f).choose_spec.1

variable (F) in
/-- **The inclusion `C^{0,α} ⊆ 𝒞^α`**: a bounded `α`-Hölder function, as an element of the
Hölder–Zygmund space `B^α_{∞,∞}`. -/
def ofHolderSpace (α : ℝ≥0) : HolderSpace α E F →L[ℝ] BesovSpace F φ α ∞ ∞ :=
  LinearMap.mkContinuous
    { toFun := holderBesovRepr φ
      map_add' f g := ext <| by
        simp only [toDistr_add, toDistr_holderBesovRepr,
          HolderSpace.toBoundedContinuousFunction_add, map_add, Lp.toTemperedDistribution_add]
      -- A real scalar acts as its complex coercion, for which every map in the chain is linear.
      map_smul' c f := ext <| by
        simp only [RingHom.id_apply, ← Complex.coe_smul, toDistr_smul, toDistr_holderBesovRepr,
          HolderSpace.toBoundedContinuousFunction_smul, map_smul,
          Lp.toTemperedDistribution_smul] }
    (2 * ofHolderConst (F := F) φ α) fun f ↦ (exists_toDistr_eq_holderSpace φ f).choose_spec.2

/-- The element `ofHolderSpace F φ α f` of `𝒞^α` is the tempered distribution of `f`. -/
@[simp]
theorem toDistr_ofHolderSpace {α : ℝ≥0} (f : HolderSpace α E F) :
    (ofHolderSpace F φ α f).toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction :=
  toDistr_holderBesovRepr φ f

/-- `ofHolderSpace` is a left inverse of `toHolderSpace`. -/
@[simp]
theorem ofHolderSpace_toHolderSpace {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ α ∞ ∞) :
    ofHolderSpace F φ α (toHolderSpace F φ hα0 hα1 u) = u :=
  ext <| by rw [toDistr_ofHolderSpace, toLpTop_toHolderSpace]

/-- `ofHolderSpace` is a right inverse of `toHolderSpace`. -/
@[simp]
theorem toHolderSpace_ofHolderSpace {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (f : HolderSpace α E F) :
    toHolderSpace F φ hα0 hα1 (ofHolderSpace F φ α f) = f :=
  (toHolderSpace_eq_iff φ hα0 hα1).2 (toDistr_ofHolderSpace φ f).symm

variable (F) in
/-- **`𝒞^α = C^{0,α}` with equivalent norms** for `0 < α < 1`: the Hölder–Zygmund space
`B^α_{∞,∞}` and the space of bounded `α`-Hölder functions are isomorphic Banach spaces, through
`toHolderSpace` and its inverse `ofHolderSpace`. -/
def holderSpaceEquiv {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ α ∞ ∞ ≃L[ℝ] HolderSpace α E F :=
  ContinuousLinearEquiv.equivOfInverse (toHolderSpace F φ hα0 hα1) (ofHolderSpace F φ α)
    (ofHolderSpace_toHolderSpace φ hα0 hα1) (toHolderSpace_ofHolderSpace φ hα0 hα1)

/-- `holderSpaceEquiv` acts as `toHolderSpace`. -/
@[simp]
theorem holderSpaceEquiv_apply {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ α ∞ ∞) :
    holderSpaceEquiv F φ hα0 hα1 u = toHolderSpace F φ hα0 hα1 u :=
  (rfl)

/-- The inverse of `holderSpaceEquiv` acts as `ofHolderSpace`. -/
@[simp]
theorem holderSpaceEquiv_symm_apply {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (f : HolderSpace α E F) :
    (holderSpaceEquiv F φ hα0 hα1).symm f = ofHolderSpace F φ α f :=
  (rfl)

/-- `ofCkHolderSpace` is a left inverse of `toCkHolderSpace`. -/
@[simp]
theorem ofCkHolderSpace_toCkHolderSpace (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    ofCkHolderSpace F φ k α (toCkHolderSpace F φ k hα0 hα1 u) = u :=
  ext <| by rw [toDistr_ofCkHolderSpace, toLpTop_toCkHolderSpace]

/-- `ofCkHolderSpace` is a right inverse of `toCkHolderSpace`. -/
@[simp]
theorem toCkHolderSpace_ofCkHolderSpace (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    toCkHolderSpace F φ k hα0 hα1 (ofCkHolderSpace F φ k α f) = f :=
  (toCkHolderSpace_eq_iff φ k hα0 hα1).2 (toDistr_ofCkHolderSpace φ k f).symm

variable (F) in
/-- **`𝒞^{k+α} = C_b^{k,α}` with equivalent norms** for `0 < α < 1`: the Hölder–Zygmund space
`B^{k+α}_{∞,∞}` and the space of bounded `C^k` maps with bounded derivatives through order `k` and
`α`-Hölder `k`-th derivative are isomorphic Banach spaces, through `toCkHolderSpace` and its
inverse `ofCkHolderSpace`. -/
def ckHolderSpaceEquiv (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ (k + α) ∞ ∞ ≃L[ℝ] CkHolderSpace k α E F :=
  ContinuousLinearEquiv.equivOfInverse (toCkHolderSpace F φ k hα0 hα1) (ofCkHolderSpace F φ k α)
    (ofCkHolderSpace_toCkHolderSpace φ k hα0 hα1) (toCkHolderSpace_ofCkHolderSpace φ k hα0 hα1)

/-- `ckHolderSpaceEquiv` acts as `toCkHolderSpace`. -/
@[simp]
theorem ckHolderSpaceEquiv_apply (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    ckHolderSpaceEquiv F φ k hα0 hα1 u = toCkHolderSpace F φ k hα0 hα1 u :=
  (rfl)

/-- The inverse of `ckHolderSpaceEquiv` acts as `ofCkHolderSpace`. -/
@[simp]
theorem ckHolderSpaceEquiv_symm_apply (k : ℕ) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    (ckHolderSpaceEquiv F φ k hα0 hα1).symm f = ofCkHolderSpace F φ k α f :=
  (rfl)

end BesovSpace

end TauCeti
