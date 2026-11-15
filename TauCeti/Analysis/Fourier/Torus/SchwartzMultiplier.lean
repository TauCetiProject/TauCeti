/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
public import TauCeti.Analysis.Fourier.Torus.Multiplier
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.PoissonSummation

/-!
# Fourier multipliers on the torus with Schwartz symbols

Let `σ` be a Schwartz function on `ℝᵈ = EuclideanSpace ℝ d` and let `T_m` be the Fourier multiplier
on `L²(𝕋ᵈ)`, `𝕋ᵈ = UnitAddTorus d`, whose symbol `m` is the restriction of `σ` to the lattice
`ℤᵈ`: `(T_m f)^(n) = σ(n) f̂(n)`. Then `T_m` is bounded in every `Lᵖ` norm, `1 ≤ p ≤ ∞`, by the
`L¹` norm of the kernel `𝓕⁻ σ` on `ℝᵈ`:

`‖T_m f‖_p ≤ ‖𝓕⁻ σ‖_{L¹(ℝᵈ)} ‖f‖_p`

(`TauCeti.UnitAddTorus.eLpNorm_fourierMultiplier_le`). This is the periodic form of the bound
`‖𝓕⁻ (σ 𝓕 f)‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p` on `ℝᵈ`, with the same constant, and the simplest case of the
transference of multipliers from `ℝᵈ` to `𝕋ᵈ`. The bound is invariant under dilations of the
symbol, since `𝓕⁻ (σ (λ⁻¹ ·)) = λᵈ (𝓕⁻ σ) (λ ·)` has the same `L¹` norm as `𝓕⁻ σ`; this is what
makes the periodic Littlewood–Paley blocks bounded on `Lᵖ` uniformly in their index.

## The argument

The **periodic kernel** `K = ∑ₙ σ(n) eₙ` is a continuous function on the torus, since `σ` is
summable over `ℤᵈ`. For `f ∈ L²(𝕋ᵈ)` the Fourier series of `T_m f` converges absolutely, hence
uniformly, and integrating it term by term identifies `T_m f` with the convolution `K ⋆ f` on the
torus. Young's inequality on the torus (`MeasureTheory.eLpNorm_convolution_le`) bounds
`‖K ⋆ f‖_p` by `‖K‖₁ ‖f‖_p`.

It remains to bound `‖K‖₁`. By Poisson summation the lift of `K` to `ℝᵈ` is the periodization
`x ↦ ∑_{ℓ ∈ ℤᵈ} (𝓕⁻ σ)(x + ℓ)` of the kernel `𝓕⁻ σ`, whose integral over the torus is at most
`‖𝓕⁻ σ‖_{L¹(ℝᵈ)}`, since the integer translates of the unit cube tile `ℝᵈ`
(`SchwartzMap.lintegral_eNorm_tsum_fourier_mul_mFourier_le`).

## Main declarations

* `TauCeti.UnitAddTorus.eLpNorm_fourierMultiplier_le`: the `Lᵖ` bound for a Fourier multiplier
  whose symbol is a Schwartz function sampled on `ℤᵈ`.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter VII,
  Sections 2 and 3 (Poisson summation and the transference of multipliers to the torus).
* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 4.3 (multipliers on the torus).
-/

public section

noncomputable section

open Complex MeasureTheory Set Submodule
open scoped Convolution ENNReal FourierTransform lp RealInnerProductSpace SchwartzMap

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- Mathlib's Fourier basis `mFourierBasis` lives on `L²` for the product of the Haar probability
-- measures on the circle factors, given by this instance; use it here so that the multipliers act
-- on that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

-- The two facts about this measure that Mathlib records with file-local instances: it is a Haar
-- measure and a probability measure. They make the volume on the torus translation and negation
-- invariant, as convolution on the torus needs.
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### The periodic kernel -/

/-- A Schwartz function is absolutely summable over the integer points. -/
private theorem summable_norm_apply_latticePoint (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    Summable fun n : d → ℤ ↦ ‖σ (latticePoint n)‖ := by
  simpa only [← latticePoint_eq_sum] using
    σ.summable_norm_apply_sum_intCast_smul (EuclideanSpace.basisFun d ℝ)

private theorem summable_smul_mFourier (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    Summable fun n : d → ℤ ↦ σ (latticePoint n) • mFourier n :=
  .of_norm <| (summable_norm_apply_latticePoint σ).congr fun n ↦ by
    rw [norm_smul, mFourier_norm, mul_one]

/-- The periodic kernel `K = ∑ₙ σ(n) eₙ` of the multiplier with symbol `σ`. -/
private def periodicKernel (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) : C(UnitAddTorus d, ℂ) :=
  ∑' n : d → ℤ, σ (latticePoint n) • mFourier n

private theorem periodicKernel_apply (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) (z : UnitAddTorus d) :
    periodicKernel σ z = ∑' n : d → ℤ, σ (latticePoint n) * mFourier n z := by
  rw [periodicKernel, ← ContinuousMap.tsum_apply (summable_smul_mFourier σ)]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]

/-- **The `L¹` norm of the periodic kernel** is at most the `L¹` norm of `𝓕⁻ σ` on `ℝᵈ`: the
kernel is the periodization of `𝓕⁻ σ`. -/
private theorem eLpNorm_periodicKernel_le (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) :
    eLpNorm (periodicKernel σ) 1 volume ≤
      ENNReal.ofReal (∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖) := by
  have h := (𝓕⁻ σ).lintegral_eNorm_tsum_fourier_mul_mFourier_le (EuclideanSpace.basisFun d ℝ)
  simp only [← latticePoint_eq_sum, ← SchwartzMap.fourier_coe,
    FourierTransform.fourier_fourierInv_eq] at h
  rw [eLpNorm_one_eq_lintegral_eNorm (periodicKernel σ).continuous.aestronglyMeasurable,
    ← SchwartzMap.fourierInv_coe, ofReal_integral_norm_eq_lintegral_eNorm (𝓕⁻ σ).integrable]
  simpa only [periodicKernel_apply] using h

/-! ### The multiplier is a convolution -/

/-- The integral of `eₙ(t) f(x - t)` over the torus is `eₙ(x) f̂(n)`. -/
private theorem integral_mFourier_mul_sub (f : UnitAddTorus d → ℂ) (n : d → ℤ)
    (x : UnitAddTorus d) :
    ∫ t, mFourier n t * f (x - t) = mFourier n x * mFourierCoeff f n := by
  have he (s : UnitAddTorus d) : mFourier n (x - s) = mFourier n x * mFourier (-n) s := by
    have h1 : mFourier n s * mFourier (-n) s = 1 := by
      rw [← mFourier_add, add_neg_cancel, mFourier_zero, ContinuousMap.one_apply]
    calc mFourier n (x - s) = mFourier n (x - s) * (mFourier n s * mFourier (-n) s) := by
          rw [h1, mul_one]
      _ = mFourier n (x - s + s) * mFourier (-n) s := by rw [mFourier_apply_add]; ring
      _ = _ := by rw [sub_add_cancel]
  rw [mFourierCoeff, ← integral_const_mul,
    ← integral_sub_left_eq_self (fun t ↦ mFourier n t * f (x - t)) volume x]
  simp only [sub_sub_cancel, he, smul_eq_mul, mul_assoc]

variable (σ : 𝓢(EuclideanSpace ℝ d, ℂ)) {m : ℓ^∞(d → ℤ, ℂ)}

/-- The convolution of the periodic kernel with an `L²` function `f` is the absolutely convergent
Fourier series `∑ₙ σ(n) f̂(n) eₙ`. -/
private theorem periodicKernel_convolution_apply (f : L²(UnitAddTorus d)) (x : UnitAddTorus d) :
    (periodicKernel σ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f) x =
      ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n * mFourier n x := by
  have hf : Integrable (fun t ↦ f (x - t)) := ((Lp.memLp f).integrable one_le_two).comp_sub_left x
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply', periodicKernel_apply, ← tsum_mul_right]
  rw [← integral_tsum_of_summable_integral_norm]
  · refine tsum_congr fun n ↦ ?_
    simp_rw [mul_assoc, integral_const_mul, integral_mFourier_mul_sub]
    ring
  · exact fun n ↦ hf.bdd_mul (f := fun t ↦ σ (latticePoint n) * mFourier n t)
      (c := ‖σ (latticePoint n)‖)
      ((continuous_const.mul (mFourier n).continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t ↦ by simp)
  · refine ((summable_norm_apply_latticePoint σ).mul_right (∫ t, ‖f (x - t)‖)).congr fun n ↦ ?_
    simp only [norm_mul, norm_mFourier_apply, mul_one]
    rw [integral_const_mul]

/-- A Fourier multiplier whose symbol is a Schwartz function sampled on `ℤᵈ` is convolution with
the periodic kernel. -/
private theorem fourierMultiplier_ae_eq_convolution (hm : ∀ n, m n = σ (latticePoint n))
    (f : L²(UnitAddTorus d)) :
    fourierMultiplier m f =ᵐ[volume]
      periodicKernel σ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f := by
  set c : (d → ℤ) → ℂ := fun n ↦ m n * mFourierCoeff f n
  -- By Parseval's identity, the Fourier coefficients of `f` are bounded by `‖f‖`.
  have hf (n : d → ℤ) : ‖mFourierCoeff f n‖ ≤ ‖f‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (le_hasSum (hasSum_norm_sq_mFourierCoeff f) n fun _ _ ↦ sq_nonneg _)
  have hc : Summable fun n ↦ c n • mFourier n := .of_norm <|
    ((summable_norm_apply_latticePoint σ).mul_right ‖f‖).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun n ↦ by
        rw [norm_smul, mFourier_norm, mul_one, norm_mul, hm]
        exact mul_le_mul_of_nonneg_left (hf n) (norm_nonneg _)
  -- The Fourier series of `T_m f` converges in `L²` and, absolutely, in `C(𝕋ᵈ)`.
  have hsum := (ContinuousMap.toLp (E := ℂ) 2 volume ℂ).hasSum hc.hasSum
  simp only [map_smul] at hsum
  have hL2 := (hasSum_fourierMultiplier m f).unique hsum
  rw [hL2]
  refine (ContinuousMap.coeFn_toLp volume _).trans (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [periodicKernel_convolution_apply, ← ContinuousMap.tsum_apply hc]
  simp [c, hm]

/-! ### The `Lᵖ` bound -/

/-- **Fourier multipliers with Schwartz symbols are bounded on `Lᵖ(𝕋ᵈ)`.** If the symbol `m` of a
Fourier multiplier `T_m` on `L²(𝕋ᵈ)` is the restriction to `ℤᵈ` of a Schwartz function `σ` on
`ℝᵈ`, then for `1 ≤ p ≤ ∞` and every `f ∈ L²(𝕋ᵈ)`,

`‖T_m f‖_p ≤ ‖𝓕⁻ σ‖_{L¹(ℝᵈ)} ‖f‖_p`.

This is the constant that Young's inequality gives for the multiplier with symbol `σ` on every
`Lᵖ(ℝᵈ)`, and it does not change under dilations `σ ↦ σ (λ⁻¹ ·)`. -/
theorem eLpNorm_fourierMultiplier_le (hm : ∀ n, m n = σ (latticePoint n)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (f : L²(UnitAddTorus d)) :
    eLpNorm (fourierMultiplier m f) p volume ≤
      ENNReal.ofReal (∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖) * eLpNorm f p volume := by
  rw [eLpNorm_congr_ae (fourierMultiplier_ae_eq_convolution σ hm f)]
  refine (eLpNorm_convolution_le _ (periodicKernel σ).continuous.aestronglyMeasurable
    (Lp.aestronglyMeasurable f) hp).trans ?_
  have hL : ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ ≤ 1 := by
    rw [eNorm_eq_nnNorm, ENNReal.coe_le_one_iff, ← NNReal.coe_le_one, coe_nnNorm]
    exact ContinuousLinearMap.opNorm_mul_le ℂ ℂ
  calc ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ * eLpNorm (periodicKernel σ) 1 volume * eLpNorm f p volume
      ≤ 1 * ENNReal.ofReal (∫ x, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) x‖) * eLpNorm f p volume := by
        gcongr
        exact eLpNorm_periodicKernel_le σ
    _ = _ := by rw [one_mul]

end TauCeti.UnitAddTorus
