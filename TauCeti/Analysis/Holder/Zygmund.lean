/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Holder.Little
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.Convolution.Holder
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LineDeriv
import TauCeti.Analysis.Holder.JetBounds
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder–Zygmund spaces of non-integer order are the bounded Hölder spaces

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

Conversely, for every `α ≥ 0` a bounded `C^k` function `f` whose derivatives through order `k` are
bounded by `M` and whose `k`-th derivative is `α`-Hölder with constant `H` lies in `𝒞^{k+α}`, with
norm at most `C (M + H)`. For `0 < α < 1` the two inclusions are inverse to each other, so
`𝒞^{k+α}` and `C_b^{k,α}` are isomorphic Banach spaces (`TauCeti.BesovSpace.ckHolderSpaceEquiv`):
the Hölder–Zygmund scale is the scale of the classical Hölder spaces at non-integer order.

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

For the converse, the kernel `κ = 𝓕⁻ ψ_{j+1}` of a block `Δ_{j+1}` has integral `ψ_{j+1}(0) = 0`
(`ContDiffBump.integral_fourierInv_inhomogeneousLittlewoodPaley_succ`), and it is even, since the
bump function is. Averaging `Δ_{j+1} f(x) = ∫ κ(t) f(x - t) dt` with its reflection
`∫ κ(t) f(x + t) dt` gives

`2 Δ_{j+1} f(x) = ∫ κ(t) (f(x + t) + f(x - t) - 2 f(x)) dt`,

so a bounded function whose second differences satisfy `‖f(x + h) + f(x - h) - 2 f(x)‖ ≤ H ‖h‖^s`
has `‖Δ_{j+1} f‖_∞ ≤ H ∫ ‖t‖^s ‖κ(t)‖ dt`, which is `O(H 2^{-js})` since `κ` is an `L¹`-normalised
dilate at scale `2^j`. Hence `f ∈ 𝒞^s` for every `s ≥ 0`. For `s = 1` this is Zygmund's
condition: the Zygmund class lies in `𝒞^1`. The second differences of an `α`-Hölder function are
at most `2 H ‖h‖^α`, which gives `C^{0,α} ⊆ 𝒞^α`, the case `k = 0`. For `k ≥ 1`, the first
derivatives `∂_{bᵢ} f` along an orthonormal basis are bounded `C^{k-1,α}` functions, hence lie in
`𝒞^{k-1+α}` by induction, and an `L^∞` function whose first derivatives lie in `𝒞^{k-1+α}` lies in
`𝒞^{k+α}` (`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_lineDerivOp_eq`).

For `0 < α < 1` the isomorphism takes the little Hölder functions exactly to the elements whose
weighted blocks vanish at high frequency. A bounded continuous function
representing `u ∈ 𝒞^α` is little `α`-Hölder, with `α`-Hölder difference quotients tending to zero
at small scales, exactly when the weighted blocks vanish at high frequency, `2^{jα} ‖Δⱼ u‖_∞ → 0`.
If they do, `u` is the limit in `𝒞^α` of its dyadic partial sums, which are represented by
Lipschitz functions; conversely a little Hölder function is the limit in `C^{0,α}` of smooth
Lipschitz functions, whose weighted blocks of order `α < 1` vanish at high frequency. The little
Hölder–Zygmund space `c^α`, the closure of the Schwartz functions in `𝒞^α`, lies inside this
block-decay subspace (strictly so, as nonzero constants show), so every element of `c^α` is little
Hölder. The cusp `x ↦ ‖x‖ ^ α`, truncated at height `1`, is not: its weighted blocks are
bounded but do not tend to zero, so it is an explicit element of `𝒞^α` outside `c^α`.

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
* `TauCeti.exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_of_norm_add_add_sub_two_nsmul_le`:
  the blocks of a bounded function whose second differences are at most `H ‖h‖^s` satisfy
  `2^{(j+1)s} ‖Δ_{j+1} f‖_∞ ≤ C H`.
* `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_norm_add_add_sub_two_nsmul_le`: such a
  function lies in `𝒞^s`, with a norm bound; for `s = 1` the Zygmund class lies in `𝒞^1`.
* `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_holderWith` and
  `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith`: the converse
  inclusions `C^{0,α} ⊆ 𝒞^α` and `C_b^{k,α} ⊆ 𝒞^{k+α}`, for every `α ≥ 0`, with norm bounds.
* `TauCeti.BesovSpace.ofCkHolderSpace`: the inclusion `C_b^{k,α} → 𝒞^{k+α}` as a continuous
  linear map, characterised by `TauCeti.BesovSpace.toDistr_ofCkHolderSpace`.
* `TauCeti.BesovSpace.ofHolderSpace` and `TauCeti.BesovSpace.holderSpaceEquiv`: the inclusion
  `C^{0,α} → 𝒞^α` as a continuous linear map and, for `0 < α < 1`, the isomorphism
  `𝒞^α ≃ C^{0,α}`.
* `TauCeti.BesovSpace.ckHolderSpaceEquiv`: for `0 < α < 1`, the isomorphism
  `𝒞^{k+α} ≃ C_b^{k,α}` given by `toCkHolderSpace` and `ofCkHolderSpace`, which are mutually
  inverse (`TauCeti.BesovSpace.toCkHolderSpace_ofCkHolderSpace` and
  `TauCeti.BesovSpace.ofCkHolderSpace_toCkHolderSpace`).
* `TauCeti.BesovSpace.memLittleHolder_iff_tendsto_rpow_mul_norm_block`: for `0 < α < 1`, a
  representative of `u ∈ 𝒞^α` is little `α`-Hölder exactly when `2^{jα} ‖Δⱼ u‖_∞ → 0`; in
  particular representatives of elements of `c^α` are little Hölder
  (`TauCeti.BesovSpace.memLittleHolder_of_mem_littleBesov`).
* `TauCeti.BesovSpace.not_tendsto_rpow_mul_norm_block_of_eqOn_norm_rpow` and
  `TauCeti.BesovSpace.notMem_littleBesov_of_eqOn_norm_rpow`: for `0 < α < 1`, an element of `𝒞^α`
  represented by a function of norm `‖x‖ ^ α` near `0` has weighted blocks `2^{jα} ‖Δⱼ u‖_∞`
  that do not tend to zero, and lies outside `c^α`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Section 2.5.7.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution ContinuousLinearMap Module Filter
open scoped ENNReal NNReal SchwartzMap Convolution Topology LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

section Kernel

variable (φ : ContDiffBump (0 : E))

/-- The kernel `𝓕⁻ (φ (2^{-N} ·))` is the `L¹`-normalised dilate `2^{Nn} K₀ (2^N ·)`. -/
private theorem fourierInv_lowPass_apply (N : ℕ) (y : E) :
    𝓕⁻ (⇑(φ.lowPassSchwartz (pow_ne_zero N two_ne_zero))) y =
      (((2 : ℝ) ^ N) ^ finrank ℝ E) •
        𝓕⁻ (⇑(φ.lowPassSchwartz (pow_ne_zero 0 two_ne_zero))) (((2 : ℝ) ^ N) • y) := by
  rw [φ.coe_lowPassSchwartz_eq_comp, fourierInv_comp_smul, inv_inv, inv_pow, abs_inv, inv_inv,
    abs_of_pos (by positivity)]
  simp only [pow_zero]

/-- The Schwartz kernel `𝓕⁻ (φ (2^{-N} ·))` of the low-pass multiplier at scale `2^N`. -/
private def kernel (N : ℕ) : 𝓢(E, ℂ) :=
  𝓕⁻ (φ.lowPassSchwartz (pow_ne_zero N two_ne_zero))

private theorem coe_kernel (N : ℕ) :
    ⇑(kernel φ N) = 𝓕⁻ (⇑(φ.lowPassSchwartz (pow_ne_zero N two_ne_zero))) :=
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
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) *
        ⇑(φ.lowPassSchwartz (pow_ne_zero (j + n₀) two_ne_zero)) =
      fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
  ext ξ
  rw [Pi.mul_apply, ContDiffBump.coe_lowPassSchwartz]
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
  have hrep : fourierMultiplierCLM F (φ.lowPassSchwartz (pow_ne_zero (j + n₀) two_ne_zero))
      (g : 𝓢'(E, F)) = g := by
    rw [← hg, littlewoodPaleyBlock_apply, fourierMultiplierCLM_fourierMultiplierCLM_apply
      (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley j)
      (φ.lowPassSchwartz (pow_ne_zero (j + n₀) two_ne_zero)).hasTemperateGrowth,
      inhomogeneousLittlewoodPaley_mul_lowPass φ hn₀]
  have hconv : 𝓕⁻ (⇑(φ.lowPassSchwartz (pow_ne_zero (j + n₀) two_ne_zero))) ⋆[lsmul ℂ ℂ]
      (g : E → F) = smoothBlock φ n₀ j g := by
    ext x
    simp only [smoothBlock, coe_kernel, convolution_def, lsmul_apply]
  exact hconv ▸ ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq hrep

end Kernel

section SecondDifference

open BoundedContinuousFunction

variable (φ : ContDiffBump (0 : E))

/-- **The blocks of a function with bounded second differences.** Let `s ≥ 0`. There is `C`,
depending only on `φ` and `s`, with the following property. Let `f` be a bounded continuous
function whose second differences satisfy `‖f (x + h) + f (x - h) - 2 f x‖ ≤ H ‖h‖^s`. Then for
every `j` the `L^∞` function `Δ_{j+1} f` satisfies `2^{(j+1)s} ‖Δ_{j+1} f‖_∞ ≤ C H`. For `s = 1`
the hypothesis is Zygmund's condition. -/
theorem exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_of_norm_add_add_sub_two_nsmul_le
    (s : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F) {H : ℝ≥0},
      (∀ x h, ‖f (x + h) + f (x - h) - 2 • f x‖ ≤ H * ‖h‖ ^ (s : ℝ)) →
      ∀ (j : ℕ) (g : Lp F ∞ (volume : Measure E)),
      littlewoodPaleyBlock F φ (j + 1) (toLpTop volume ℂ f : 𝓢'(E, F)) = g →
      2 ^ ((s : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖g‖ ≤ C * H := by
  obtain ⟨C, hC, hm⟩ :=
    φ.exists_integrable_and_integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le
      s.coe_nonneg
  refine ⟨C, hC, fun f H hf j g hg ↦ ?_⟩
  -- The block `Δ_{j+1} f` is the convolution `κ ⋆ f` with the kernel `κ = 𝓕⁻ ψ_{j+1}`, which is
  -- even and has vanishing integral; hence
  -- `2 (κ ⋆ f)(x) = ∫ κ(t) (f(x + t) + f(x - t) - 2 f(x)) dt` is at most
  -- `H ∫ ‖t‖^s ‖κ t‖ dt`, the `s`-th moment of `κ` times `H`.
  set κ : E → ℂ := 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ))
  have hκi : Integrable κ := by
    simpa only [φ.coe_fourierInv_inhomogeneousLittlewoodPaleySchwartz] using
      (𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz (j + 1))).integrable
  obtain ⟨hmi, hmb⟩ := hm (j + 1)
  have hconv : (g : E → F) =ᵐ[volume] κ ⋆[lsmul ℂ ℂ] (f : E → F) := by
    refine (ae_eq_convolution_of_littlewoodPaleyBlock_eq φ (j + 1) hg).trans ?_
    rw [convolution_congr (lsmul ℂ ℂ) (Filter.EventuallyEq.refl _ κ) (coeFn_toLpTop volume f)]
  have hpt (x : E) : ‖(κ ⋆[lsmul ℂ ℂ] (f : E → F)) x‖ ≤ H * ∫ t, ‖t‖ ^ (s : ℝ) * ‖κ t‖ := by
    simp only [convolution_def, lsmul_apply]
    exact norm_integral_kernel_smul_sub_le_of_norm_add_add_sub_two_nsmul_le hκi
      (φ.fourierInv_inhomogeneousLittlewoodPaley_neg (j + 1) ·)
      (φ.integral_fourierInv_inhomogeneousLittlewoodPaley_succ j) hf hmi
      (integrable_kernel_smul_sub hκi f.continuous (f.norm_coe_le_norm ·) x)
  have hnorm : ‖g‖ ≤ H * (((2 : ℝ) ^ ((s : ℝ) * ((j + 1 : ℕ) : ℝ)))⁻¹ * C) := by
    refine Lp.norm_top_le_of_ae_bound (by positivity) ?_
    filter_upwards [hconv] with x hx
    rw [hx]
    exact (hpt x).trans (by gcongr)
  calc 2 ^ ((s : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖g‖
      ≤ 2 ^ ((s : ℝ) * ((j + 1 : ℕ) : ℝ)) *
          (H * (((2 : ℝ) ^ ((s : ℝ) * ((j + 1 : ℕ) : ℝ)))⁻¹ * C)) := by gcongr
    _ = C * H := by field_simp

end SecondDifference

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
  obtain ⟨n₀, hn₀⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  replace hn₀ := hn₀.le
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

/-- **Functions with bounded second differences are Hölder–Zygmund distributions.** Let
`s ≥ 0`. There is `C`, depending only on `φ` and `s`, such that every bounded continuous function
`f` whose second differences satisfy `‖f (x + h) + f (x - h) - 2 f x‖ ≤ H ‖h‖^s` is an element of
`𝒞^s = B^s_{∞,∞}` of norm at most `C (‖f‖ + H)`. For `s = 1` the hypothesis is Zygmund's
condition, which a Lipschitz function satisfies but which does not imply the Lipschitz
condition. -/
theorem exists_toDistr_eq_and_norm_le_of_norm_add_add_sub_two_nsmul_le (s : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F) {H : ℝ≥0},
      (∀ x h, ‖f (x + h) + f (x - h) - 2 • f x‖ ≤ H * ‖h‖ ^ (s : ℝ)) →
      ∃ w : BesovSpace F φ s ∞ ∞, w.toDistr = toLpTop volume ℂ f ∧ ‖w‖ ≤ C * (‖f‖ + H) := by
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨Cm, hCm, hblock⟩ :=
    exists_rpow_mul_norm_littlewoodPaleyBlock_succ_le_of_norm_add_add_sub_two_nsmul_le
      (F := F) φ s
  refine ⟨max CΔ 0 + Cm, by positivity, fun f H hf ↦ ?_⟩
  -- The blocks `Δⱼ f` are `L^∞` functions `gⱼ`, and the weighted blocks are bounded by
  -- `c = max CΔ 0 ‖f‖ + Cm H`: the low-frequency block by `‖f‖`, the others by `H`.
  choose g hg hgn using fun j ↦ hΔ j (toLpTop volume ℂ f)
  obtain ⟨w, hw, hwn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_of_forall_le
    (s := s) g (c := max CΔ 0 * ‖f‖ + Cm * H) hg fun j ↦ by
      rcases j with _ | j
      · rw [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
        refine ((hgn 0).trans ?_).trans (le_add_of_nonneg_right (by positivity))
        rw [norm_toLpTop]
        gcongr
        exact le_max_left _ _
      · exact (hblock f hf j (g (j + 1)) (hg (j + 1))).trans
          (le_add_of_nonneg_left (by positivity))
  refine ⟨w, hw, hwn.trans ?_⟩
  have := le_max_right CΔ 0
  nlinarith [norm_nonneg f, H.coe_nonneg]

/-- **Hölder functions are Hölder–Zygmund distributions.** Let `α ≥ 0`. There is `C`, depending
only on `φ` and `α`, such that every bounded continuous `α`-Hölder function `f` with constant `H`
is an element of `𝒞^α = B^α_{∞,∞}` of norm at most `C (‖f‖ + H)`. -/
theorem exists_toDistr_eq_and_norm_le_of_holderWith (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F) {H : ℝ≥0}, HolderWith H α f →
      ∃ w : BesovSpace F φ α ∞ ∞, w.toDistr = toLpTop volume ℂ f ∧ ‖w‖ ≤ C * (‖f‖ + H) := by
  obtain ⟨C, hC, h⟩ := exists_toDistr_eq_and_norm_le_of_norm_add_add_sub_two_nsmul_le (F := F) φ α
  refine ⟨2 * C, by positivity, fun f H hf ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := h f (H := 2 * H) fun x h ↦ by
    simpa using hf.norm_add_add_sub_two_nsmul_le x h
  refine ⟨w, hw, hwn.trans ?_⟩
  push_cast
  nlinarith [norm_nonneg f, H.coe_nonneg]

/-- **The inductive step from order `k` to order `k + 1`.** If bounded `C^{k,α}` functions lie in
`𝒞^{k+α}` with norm bounds, then bounded `C^{k+1,α}` functions lie in `𝒞^{k+1+α}`: their first
derivatives lie in `𝒞^{k+α}`, by `exists_toDistr_eq_and_norm_le_of_lineDerivOp_eq`. -/
private theorem exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith_succ {k : ℕ} {α : ℝ≥0}
    (hk : ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F), ContDiff ℝ k f → ∀ {M : ℝ} {H : ℝ≥0},
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) → HolderWith H α (iteratedFDeriv ℝ k f) →
      ∃ w : BesovSpace F φ (k + α) ∞ ∞, w.toDistr = toLpTop volume ℂ f ∧ ‖w‖ ≤ C * (M + H)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F), ContDiff ℝ (k + 1 : ℕ) f → ∀ {M : ℝ} {H : ℝ≥0},
      (∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) →
      HolderWith H α (iteratedFDeriv ℝ (k + 1) f) →
      ∃ w : BesovSpace F φ ((k + 1 : ℕ) + α) ∞ ∞,
        w.toDistr = toLpTop volume ℂ f ∧ ‖w‖ ≤ C * (M + H) := by
  obtain ⟨Ck, hCk, hk⟩ := hk
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨CA, hCA, hA⟩ := exists_toDistr_eq_and_norm_le_of_lineDerivOp_eq (F := F) φ b
  refine ⟨CA * (1 + finrank ℝ E * Ck), by positivity, fun f hf M H hM hH ↦ ?_⟩
  have hb (i : Fin (finrank ℝ E)) : ‖b i‖ = 1 := b.orthonormal.1 i
  -- The directional derivatives `∂_{bᵢ} f` are `C^k`, with derivatives through order `k`
  -- bounded by `M` and `α`-Hölder `k`-th derivative with constant `H`.
  have hDbd (i : Fin (finrank ℝ E)) :
      ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y (b i)) x‖ ≤ M := by
    simpa [hb] using hf.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_rfl) hM (b i)
  have hDc (i : Fin (finrank ℝ E)) : ContDiff ℝ k fun y ↦ fderiv ℝ f y (b i) :=
    (hf.fderiv_right (m := k) (by push_cast; exact le_rfl)).clm_apply contDiff_const
  have hDH (i : Fin (finrank ℝ E)) :
      HolderWith H α (iteratedFDeriv ℝ k fun y ↦ fderiv ℝ f y (b i)) := by
    simpa [hb] using
      (ContDiff.holderWith_iteratedFDeriv_fderiv_apply (by exact_mod_cast hf) hH (b i))
  let g (i : Fin (finrank ℝ E)) : E →ᵇ F :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun y ↦ fderiv ℝ f y (b i))
      (hDc i).continuous M fun x ↦ by
        simpa only [norm_iteratedFDeriv_zero] using hDbd i 0 k.zero_le x
  choose v hv hvn using fun i ↦ hk (g i) (hDc i) (hDbd i) (hDH i)
  -- The classical derivatives `∂_{bᵢ} f` are the distributional ones.
  have hder (i : Fin (finrank ℝ E)) :
      ∂_{b i} ((toLpTop volume ℂ f : Lp F ∞ volume) : 𝓢'(E, F)) = (v i).toDistr := by
    rw [hv i]
    exact lineDerivOp_toTemperedDistribution_eq_of_contDiff
      (hf.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 k.succ_ne_zero))
      (coeFn_toLpTop volume f) (coeFn_toLpTop volume (g i))
  obtain ⟨w, hw, hwn⟩ := hA (toLpTop volume ℂ f) v hder
  have hs : ((k + 1 : ℕ) : ℝ) + α = (k + α : ℝ) + 1 := by push_cast; ring
  rw [hs]
  refine ⟨w, hw, hwn.trans ?_⟩
  obtain ⟨hM0, hfM⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hM
  have hfM : ‖f‖ ≤ M := (BoundedContinuousFunction.norm_le hM0).2 hfM
  calc CA * (‖toLpTop volume ℂ f‖ + ∑ i, ‖v i‖)
      ≤ CA * (M + ∑ _i : Fin (finrank ℝ E), Ck * (M + H)) := by
        rw [norm_toLpTop]
        gcongr with i
        exact hvn i
    _ ≤ CA * (1 + finrank ℝ E * Ck) * (M + H) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
        gcongr
        nlinarith [H.coe_nonneg, mul_nonneg hCk (add_nonneg hM0 H.coe_nonneg)]

/-- **Bounded `C^{k,α}` functions are Hölder–Zygmund distributions of order `k + α`.** Let
`k : ℕ` and `α ≥ 0`. There is `C`, depending only on `φ`, `k` and `α`, with the following
property. Let `f` be a bounded continuous `C^k` function whose derivatives through order `k` are
bounded by `M` and whose `k`-th derivative is `α`-Hölder with constant `H`. Then
`f ∈ 𝒞^{k+α} = B^{k+α}_{∞,∞}`, with norm at most `C (M + H)`. -/
theorem exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (k : ℕ) (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E →ᵇ F), ContDiff ℝ k f → ∀ {M : ℝ} {H : ℝ≥0},
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ M) → HolderWith H α (iteratedFDeriv ℝ k f) →
      ∃ w : BesovSpace F φ (k + α) ∞ ∞, w.toDistr = toLpTop volume ℂ f ∧ ‖w‖ ≤ C * (M + H) := by
  induction k with
  | zero =>
    -- The order-zero case is `exists_toDistr_eq_and_norm_le_of_holderWith`.
    obtain ⟨C, hC, h⟩ := exists_toDistr_eq_and_norm_le_of_holderWith (F := F) φ α
    refine ⟨C, hC, fun f _ M H hM hH ↦ ?_⟩
    have hf : HolderWith H α f :=
      holderOnWith_univ.1 (holderOnWith_iteratedFDeriv_zero_iff.1 (holderOnWith_univ.2 hH))
    rw [Nat.cast_zero, zero_add]
    obtain ⟨w, hw, hwn⟩ := h f hf
    have hM' := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hM
    exact ⟨w, hw, hwn.trans (by gcongr; exact (BoundedContinuousFunction.norm_le hM'.1).2 hM'.2)⟩
  | succ k ih => exact exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith_succ φ ih

/-- The norm of a bounded `C^{k,α}` map bounds its norm in `𝒞^{k+α} = B^{k+α}_{∞,∞}`. -/
private theorem exists_toDistr_eq_and_norm_le_of_ckHolderSpace (k : ℕ) (α : ℝ≥0) :
    ∃ C : ℝ, ∀ f : CkHolderSpace k α E F, ∃ w : BesovSpace F φ (k + α) ∞ ∞,
      w.toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction ∧ ‖w‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := F) φ k α
  refine ⟨2 * C, fun f ↦ ?_⟩
  have hcoe := f.coe_toBoundedContinuousFunction
  obtain ⟨w, hw, hwn⟩ := hC f.toBoundedContinuousFunction (by rw [hcoe]; exact f.contDiff)
    (M := ‖f‖) (by rw [hcoe]; exact fun i hi x ↦ f.norm_iteratedFDeriv_apply_le hi x)
    (by rw [hcoe]; exact f.memHolder_iteratedFDeriv.holderWith)
  refine ⟨w, hw, hwn.trans ?_⟩
  have := f.nnHolderNorm_iteratedFDeriv_le
  nlinarith

/-- A bounded `C^{k,α}` map, as a tempered distribution, lies in `𝒞^{k+α} = B^{k+α}_{∞,∞}`. -/
private theorem memBesov_toLpTop (k : ℕ) (f : CkHolderSpace k α E F) :
    (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)).MemBesov φ (k + α) ∞ ∞ := by
  obtain ⟨w, hw, -⟩ := (exists_toDistr_eq_and_norm_le_of_ckHolderSpace (F := F) φ k α).choose_spec f
  exact hw ▸ w.memBesov_toDistr

variable (F) in
/-- **The inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}`**: a bounded `C^k` map with bounded derivatives through
order `k` and `α`-Hölder `k`-th derivative, as an element of the Hölder–Zygmund space
`B^{k+α}_{∞,∞}`. For `0 < α < 1` it inverts `TauCeti.BesovSpace.toCkHolderSpace`
(`TauCeti.BesovSpace.ckHolderSpaceEquiv`). -/
def ofCkHolderSpace (k : ℕ) (α : ℝ≥0) : CkHolderSpace k α E F →L[ℝ] BesovSpace F φ (k + α) ∞ ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun f := (memBesov_toLpTop φ k f).toBesovSpace
      map_add' f g := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toDistr_add,
          CkHolderSpace.toBoundedContinuousFunction_add,
          map_add, Lp.toTemperedDistribution_add]
      map_smul' c f := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, RingHom.id_apply, toDistr_smul,
          CkHolderSpace.toBoundedContinuousFunction_smul, map_smul,
          Lp.toTemperedDistribution_smul, ← Complex.coe_smul] } <| by
    obtain ⟨C, hC⟩ := exists_toDistr_eq_and_norm_le_of_ckHolderSpace (F := F) φ k α
    refine ⟨C, fun f ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ := hC f
    have hwf : (memBesov_toLpTop φ k f).toBesovSpace = w := ext <| by
      rw [MemBesov.toDistr_toBesovSpace, hw]
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, hwf] using hwn

@[simp]
theorem toDistr_ofCkHolderSpace (k : ℕ) (f : CkHolderSpace k α E F) :
    (ofCkHolderSpace F φ k α f).toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction :=
  MemBesov.toDistr_toBesovSpace _

/-- `TauCeti.BesovSpace.toCkHolderSpace` is a left inverse of
`TauCeti.BesovSpace.ofCkHolderSpace`. -/
@[simp]
theorem toCkHolderSpace_ofCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    toCkHolderSpace F φ k hα0 hα1 (ofCkHolderSpace F φ k α f) = f :=
  (toCkHolderSpace_eq_iff φ k hα0 hα1).2 (toDistr_ofCkHolderSpace φ k f).symm

/-- `TauCeti.BesovSpace.ofCkHolderSpace` is a left inverse of
`TauCeti.BesovSpace.toCkHolderSpace`. -/
@[simp]
theorem ofCkHolderSpace_toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    ofCkHolderSpace F φ k α (toCkHolderSpace F φ k hα0 hα1 u) = u :=
  ext <| by rw [toDistr_ofCkHolderSpace, toLpTop_toCkHolderSpace]

variable (F) in
/-- **The Hölder–Zygmund space of non-integer order is the bounded Hölder space.** For `k : ℕ`
and `0 < α < 1`, the Hölder–Zygmund space `𝒞^{k+α} = B^{k+α}_{∞,∞}` and the space `C_b^{k,α}` of
bounded `C^k` maps with bounded derivatives through order `k` and `α`-Hölder `k`-th derivative are
isomorphic Banach spaces: a tempered distribution lies in `𝒞^{k+α}` exactly when it is (the
distribution of) such a map. The isomorphism is `TauCeti.BesovSpace.toCkHolderSpace`, with inverse
`TauCeti.BesovSpace.ofCkHolderSpace`. -/
def ckHolderSpaceEquiv (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ (k + α) ∞ ∞ ≃L[ℝ] CkHolderSpace k α E F :=
  ContinuousLinearEquiv.ofContinuousLinearMap (toCkHolderSpace F φ k hα0 hα1)
    (ofCkHolderSpace F φ k α)
    (ContinuousLinearMap.ext (toCkHolderSpace_ofCkHolderSpace φ k hα0 hα1))
    (ContinuousLinearMap.ext (ofCkHolderSpace_toCkHolderSpace φ k hα0 hα1))

@[simp]
theorem coe_ckHolderSpaceEquiv (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) :
    ⇑(ckHolderSpaceEquiv F φ k hα0 hα1) = toCkHolderSpace F φ k hα0 hα1 :=
  (rfl)

@[simp]
theorem coe_ckHolderSpaceEquiv_symm (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) :
    ⇑(ckHolderSpaceEquiv F φ k hα0 hα1).symm = ofCkHolderSpace F φ k α :=
  (rfl)

/-! ### The case `k = 0`: `𝒞^α = C^{0,α}` -/

/-- The constant of `exists_toDistr_eq_and_norm_le_of_holderWith`. -/
private def ofHolderConst (α : ℝ≥0) : ℝ :=
  (exists_toDistr_eq_and_norm_le_of_holderWith (F := F) φ α).choose

/-- The element of `𝒞^α` represented by a bounded `α`-Hölder function, with the norm bound. -/
private theorem exists_toDistr_eq_holderSpace {α : ℝ≥0} (f : HolderSpace α E F) :
    ∃ u : BesovSpace F φ α ∞ ∞, u.toDistr = toLpTop volume ℂ f.toBoundedContinuousFunction ∧
      ‖u‖ ≤ 2 * ofHolderConst (F := F) φ α * ‖f‖ := by
  obtain ⟨hC, h⟩ := (exists_toDistr_eq_and_norm_le_of_holderWith (F := F) φ α).choose_spec
  obtain ⟨u, hu, hun⟩ := h f.toBoundedContinuousFunction (H := ‖f‖₊)
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
  ContinuousLinearEquiv.ofContinuousLinearMap (toHolderSpace F φ hα0 hα1) (ofHolderSpace F φ α)
    (ContinuousLinearMap.ext (toHolderSpace_ofHolderSpace φ hα0 hα1))
    (ContinuousLinearMap.ext (ofHolderSpace_toHolderSpace φ hα0 hα1))

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

/-! ### The little Hölder–Zygmund space and the little Hölder space -/

/-- An element of `𝒞^α` with the same tempered distribution as an element of `𝒞^{1+α}` is
represented by a Lipschitz function, which is little `α`-Hölder for `α < 1`: the representative is
`C¹` with bounded derivative. -/
private theorem toHolderSpace_mem_littleHolder_of_toDistr_eq (hα0 : 0 < α) (hα1 : α < 1)
    {v : BesovSpace F φ α ∞ ∞} {w : BesovSpace F φ (((1 : ℕ) : ℝ) + α) ∞ ∞}
    (hvw : v.toDistr = w.toDistr) :
    toHolderSpace F φ hα0 hα1 v ∈ HolderSpace.littleHolder α E F := by
  set g := toCkHolderSpace F φ 1 hα0 hα1 w
  have hvg : (toHolderSpace F φ hα0 hα1 v).toBoundedContinuousFunction =
      g.toBoundedContinuousFunction :=
    repr_eq φ (toLpTop_toHolderSpace φ hα0 hα1) (by rw [toLpTop_toCkHolderSpace, hvw])
  rw [HolderSpace.mem_littleHolder_iff, ← HolderSpace.coe_toBoundedContinuousFunction, hvg,
    CkHolderSpace.coe_toBoundedContinuousFunction]
  exact g.lipschitzWith.memLittleHolder hα1

/-- If the weighted blocks of `u ∈ 𝒞^α` vanish at high frequency, then its Hölder representative
is little Hölder: it is a limit in `C^{0,α}` of the representatives of the dyadic partial sums
`S_N u`, which come from `𝒞^{1+α}`, and the little Hölder space is closed. -/
private theorem toHolderSpace_mem_littleHolder_of_tendsto (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞}
    (hu : Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0)) :
    toHolderSpace F φ hα0 hα1 u ∈ HolderSpace.littleHolder α E F := by
  have hlt : (α : ℝ) < ((1 : ℕ) : ℝ) + α := by
    rw [Nat.cast_one]
    exact lt_one_add _
  refine HolderSpace.isClosed_littleHolder.mem_of_tendsto
    (((toHolderSpace F φ hα0 hα1).continuous.tendsto u).comp
      (tendsto_partialSumCLM_top_of_tendsto hu)) (Eventually.of_forall fun N ↦ ?_)
  obtain ⟨w, hw⟩ := partialSumCLM_mem_range_inclusionOfLT hlt ∞ N u
  rw [Function.comp_apply, ← hw]
  exact toHolderSpace_mem_littleHolder_of_toDistr_eq φ hα0 hα1 (toDistr_inclusionOfLT hlt w)

/-- If the Hölder representative of `u ∈ 𝒞^α` is little Hölder, then the weighted blocks of `u`
vanish at high frequency: the representative is a limit in `C^{0,α}` of smooth Lipschitz functions
`g`, which lie in `𝒞¹`, so their weighted blocks of order `α < 1` vanish at high frequency, and
block decay is a closed condition in `𝒞^α`. -/
private theorem tendsto_of_toHolderSpace_mem_littleHolder (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} (hu : toHolderSpace F φ hα0 hα1 u ∈ HolderSpace.littleHolder α E F) :
    Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0) := by
  rw [← SetLike.mem_coe, HolderSpace.littleHolder_eq_closure hα1] at hu
  rw [← ofHolderSpace_toHolderSpace φ hα0 hα1 u]
  refine isClosed_setOf_tendsto_rpow_mul_norm_block.closure_subset
    (map_mem_closure (ofHolderSpace F φ α).continuous hu fun g ⟨_, K, hK⟩ ↦ ?_)
  -- The Lipschitz function `g` is an element `w` of `𝒞¹`, so its weighted blocks of order
  -- `α < 1` vanish at high frequency.
  obtain ⟨_, -, hC⟩ := exists_toDistr_eq_and_norm_le_of_holderWith (F := F) φ 1
  obtain ⟨w, hw, -⟩ := hC g.toBoundedContinuousFunction (H := K) <| by
    rw [HolderSpace.coe_toBoundedContinuousFunction]
    exact hK.holderWith
  have hlt : (α : ℝ) < ((1 : ℝ≥0) : ℝ) := by exact_mod_cast hα1
  have hblock (j : ℕ) : (ofHolderSpace F φ α g).block j = w.block j :=
    block_eq_of_toDistr_eq ((toDistr_ofHolderSpace φ g).trans hw.symm) j
  simpa only [Set.mem_ofPred_eq, block_inclusionOfLT, hblock] using
    tendsto_rpow_mul_norm_block ENNReal.one_ne_top (inclusionOfLT F φ ∞ ∞ 1 hlt w)

/-- **Little Hölder continuity is block decay.** Let `0 < α < 1` and let `f` be
a bounded continuous function representing `u ∈ 𝒞^α = B^α_{∞,∞}`. Then `f` is little
`α`-Hölder, its `α`-Hölder difference quotients tending to zero at small scales, exactly when the
weighted blocks of `u` vanish at high frequency, `2^{jα} ‖Δⱼ u‖_∞ → 0`. -/
theorem memLittleHolder_iff_tendsto_rpow_mul_norm_block (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} {f : E →ᵇ F}
    (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) :
    MemLittleHolder α f ↔ Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0) := by
  have huf : (toHolderSpace F φ hα0 hα1 u).toBoundedContinuousFunction = f :=
    repr_eq φ (toLpTop_toHolderSpace φ hα0 hα1) hf
  rw [← huf, HolderSpace.coe_toBoundedContinuousFunction, ← HolderSpace.mem_littleHolder_iff]
  exact ⟨tendsto_of_toHolderSpace_mem_littleHolder φ hα0 hα1,
    toHolderSpace_mem_littleHolder_of_tendsto φ hα0 hα1⟩

/-- **Elements of the little Hölder–Zygmund space `c^α` are little Hölder.** For `0 < α < 1`, a
bounded continuous function representing an element of `c^α`, the closure of the Schwartz
functions in `𝒞^α`, is little `α`-Hölder. -/
theorem memLittleHolder_of_mem_littleBesov (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} (hu : u ∈ littleBesov F φ α ∞) {f : E →ᵇ F}
    (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) : MemLittleHolder α f :=
  (memLittleHolder_iff_tendsto_rpow_mul_norm_block φ hα0 hα1 hf).2
    (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu)

/-- **The cusp has weighted blocks that do not vanish at high frequency.** Let `0 < α < 1` and let
`u ∈ 𝒞^α` be represented by a bounded continuous function `f` with `‖f x‖ = ‖x‖ ^ α` near `0`,
such as the cusp truncated at height `1`. The weighted blocks `2^{jα} ‖Δⱼ u‖_∞` are bounded by
`‖u‖`, but they do not tend to zero. -/
theorem not_tendsto_rpow_mul_norm_block_of_eqOn_norm_rpow [Nontrivial E] (hα0 : 0 < α)
    (hα1 : α < 1) {u : BesovSpace F φ α ∞ ∞} {f : E →ᵇ F}
    (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr) {r : ℝ} (hr : 0 < r)
    (hfr : Set.EqOn (fun x ↦ ‖f x‖) (fun x ↦ ‖x‖ ^ (α : ℝ)) (Metric.ball 0 r)) :
    ¬ Tendsto (fun j : ℕ ↦ 2 ^ ((α : ℝ) * j) * ‖u.block j‖) atTop (𝓝 0) := fun h ↦
  not_memLittleHolder_of_eqOn_norm_rpow hα0 hr hfr (lipschitzWith_one_norm.comp_memLittleHolder
    ((memLittleHolder_iff_tendsto_rpow_mul_norm_block φ hα0 hα1 hf).2 h))

/-- **The cusp is not in the little Hölder–Zygmund space.** For `0 < α < 1`, an element of `𝒞^α`
represented by a bounded continuous function `f` with `‖f x‖ = ‖x‖ ^ α` near `0` does not lie in
`c^α`, the closure of the Schwartz functions in `𝒞^α`. -/
theorem notMem_littleBesov_of_eqOn_norm_rpow [Nontrivial E] (hα0 : 0 < α) (hα1 : α < 1)
    {u : BesovSpace F φ α ∞ ∞} {f : E →ᵇ F} (hf : (toLpTop volume ℂ f : 𝓢'(E, F)) = u.toDistr)
    {r : ℝ} (hr : 0 < r)
    (hfr : Set.EqOn (fun x ↦ ‖f x‖) (fun x ↦ ‖x‖ ^ (α : ℝ)) (Metric.ball 0 r)) :
    u ∉ littleBesov F φ α ∞ := fun hu ↦
  not_tendsto_rpow_mul_norm_block_of_eqOn_norm_rpow φ hα0 hα1 hf hr hfr
    (tendsto_rpow_mul_norm_block_of_mem_littleBesov hu)

end BesovSpace

end TauCeti
