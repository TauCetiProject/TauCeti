/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.Fourier.LpSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication

/-!
# Schwartz functions in the Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space. Every Schwartz function `u` lies in
Mathlib's Bessel-potential space `H^{s,p}(E, F)` (`SchwartzMap.memSobolev`), with `Lᵖ` part the
Schwartz function `J^s u = 𝓕⁻ (⟨ξ⟩ ^ s 𝓕 u)`, where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. This file
packages this inclusion as a continuous linear map and proves that its range is dense for
`p < ∞`, since `J^s` is a bijection of Schwartz space and Schwartz functions are dense in `Lᵖ`.
Operators that are first defined and estimated on Schwartz functions, such as
pseudodifferential operators, therefore extend uniquely to bounded operators on `H^{s,p}`.

For `p = 2` and values in a complex Hilbert space `F`, the norm is computed on the Fourier side by
Plancherel's theorem: the `H^s` norm of `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`, and more generally
an element of `H^s` whose weighted Fourier transform `⟨ξ⟩ ^ s 𝓕 u` is represented by `G ∈ L²`
has norm `‖G‖`. The weighted Fourier transform of a Schwartz function lies in every `L^q` for any
normed complex `F`.

## Main declarations

* `SchwartzMap.toBesselPotentialSpaceCLM`: the inclusion `𝓢(E, F) →L[ℂ] H^{s,p}(E, F)`.
* `SchwartzMap.denseRange_toBesselPotentialSpaceCLM`: its range is dense for `p < ∞`.
* `SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero`,
  `BesselPotentialSpace.toDistr_toLpₗᵢ_zero_symm_apply`: the identification `H^{0,p} = Lᵖ`.
* `BesselPotentialSpace.continuousLinearMap_ext`: continuous linear maps out of `H^{s,p}`,
  `p < ∞`, are determined by their values on Schwartz functions.
* `BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`: for Hilbert-space values, the `H^s`
  norm is the `L²` norm of the weighted Fourier transform.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM`: for Hilbert-space values, the `H^s` norm of a
  Schwartz function `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`.
* `SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier`: `⟨ξ⟩ ^ s 𝓕 u` lies in every `L^q`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`: the `H¹` norm of a Schwartz function in terms
  of its first derivatives, `‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_compSubConstCLM`: translation preserves the `H^s`
  norm of a Schwartz function.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace SchwartzMap

/-- The inclusion of Schwartz functions into the Bessel-potential space `H^{s,p}`, as a continuous
linear map. It sends `u` to the element of `H^{s,p}` whose underlying tempered distribution is `u`
(`SchwartzMap.toDistr_toBesselPotentialSpaceCLM`); its `Lᵖ` part is the Schwartz function
`J^s u`, the Fourier multiplier with symbol `⟨ξ⟩ ^ s` applied to `u`. -/
def toBesselPotentialSpaceCLM (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓢(E, F) →L[ℂ] H^{s, p}(E, F) :=
  ((BesselPotentialSpace.toLpₗᵢ E F s p).symm.toContinuousLinearEquiv :
      Lp F p (volume : Measure E) →L[ℂ] H^{s, p}(E, F)) ∘L
    toLpCLM ℂ F p volume ∘L
      fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp]
theorem toLp_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM s p u).toLp =
      (fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u).toLp p := by
  rw [← BesselPotentialSpace.toLpₗᵢ_apply, toBesselPotentialSpaceCLM]
  simp

/-- The `Lᵖ` part of a Schwartz function `u` in `H^{s,p}` is almost everywhere the Schwartz function
`J^s u`. -/
theorem coeFn_toLp_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM s p u).toLp =ᵐ[volume]
      fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u := by
  rw [toLp_toBesselPotentialSpaceCLM]
  exact coeFn_toLp _ p volume

@[simp]
theorem toDistr_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM s p u).toDistr = (u : 𝓢'(E, F)) := by
  simp only [toBesselPotentialSpaceCLM, ContinuousLinearMap.comp_apply, toLpCLM_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    BesselPotentialSpace.toLpₗᵢ_symm_apply, Lp.toTemperedDistribution_toLp_eq,
    ← besselPotential_toTemperedDistributionCLM_eq, besselPotential_besselPotential_apply,
    add_neg_cancel, besselPotential_zero, ContinuousLinearMap.id_apply]

/-- In `H^{0,p} = Lᵖ` the `Lᵖ` part of a Schwartz function `u` is `u` itself. -/
theorem toLp_toBesselPotentialSpaceCLM_zero (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM 0 p u).toLp = u.toLp p := by
  simp [fourierMultiplierCLM_const]

/-- **Schwartz functions are dense in `H^{s,p}`** for `p < ∞`. -/
theorem denseRange_toBesselPotentialSpaceCLM (s : ℝ) (hp : p ≠ ∞) :
    DenseRange (toBesselPotentialSpaceCLM (E := E) (F := F) s p) := by
  have hsurj : Function.Surjective
      (fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))) :=
    fun ψ ↦ ⟨_, fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg s ψ⟩
  exact (BesselPotentialSpace.toLpₗᵢ E F s p).symm.surjective.denseRange.comp
    ((denseRange_toLpCLM (F := F) hp).comp hsurj.denseRange (toLpCLM ℝ F p volume).continuous)
    (BesselPotentialSpace.toLpₗᵢ E F s p).symm.continuous

omit [CompleteSpace F] in
/-- The weighted Fourier transform `⟨ξ⟩ ^ s 𝓕 u` of a Schwartz function is a Schwartz function,
so it lies in every `L^q`. When `F` is a complex Hilbert space, its `L²` norm is the `H^s` norm of
`u` (`SchwartzMap.norm_toBesselPotentialSpaceCLM`). -/
theorem memLp_one_add_norm_sq_rpow_smul_fourier (s : ℝ) (u : 𝓢(E, F)) (q : ℝ≥0∞) :
    MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) q volume := by
  have hw : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  exact ((smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u)).memLp q
    volume).ae_eq (.of_forall fun ξ ↦ smulLeftCLM_apply_apply hw _ ξ)

/-- The `H^s` norm of a Schwartz function `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`. -/
theorem norm_toBesselPotentialSpaceCLM {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (s : ℝ) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM s 2 u‖ =
      (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume).toReal := by
  rw [← BesselPotentialSpace.norm_toLp_eq, toLp_toBesselPotentialSpaceCLM,
    norm_toLp_fourierMultiplierCLM_eq (by fun_prop)]

open scoped LineDeriv Real RealInnerProductSpace in
/-- **The `H¹` norm of a Schwartz function** in terms of its first derivatives: for an orthonormal
basis `b` of `E`,

`‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.

The factor `(2π)⁻²` comes from the Fourier transform of `∂_v u` being `2πi ⟪ξ, v⟫ 𝓕 u`. -/
theorem norm_toBesselPotentialSpaceCLM_one_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 =
      (∫ x, ‖u x‖ ^ 2) + (2 * π)⁻¹ ^ 2 * ∑ i, ∫ x, ‖∂_{b i} u x‖ ^ 2 := by
  have hint (g : 𝓢(E, F)) : Integrable (fun ξ ↦ ‖𝓕 g ξ‖ ^ 2) :=
    ((𝓕 g).memLp 2).integrable_norm_pow two_ne_zero
  have hw := memLp_one_add_norm_sq_rpow_smul_fourier (F := F) 1 u 2
  have hL : ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 =
      ∫ ξ, ‖(((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • 𝓕 u ξ‖ ^ 2 := by
    rw [norm_toBesselPotentialSpaceCLM, hw.eLpNorm_eq_integral_rpow_norm two_ne_zero
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat]
    simp_rw [Real.rpow_two]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity)]
    norm_num
  rw [hL, ← integral_norm_sq_fourier u]
  simp_rw [← integral_norm_sq_fourier (∂_{b _} u)]
  rw [← integral_finsetSum _ fun i _ ↦ hint _, ← integral_const_mul,
    ← integral_add (hint u) ((integrable_finsetSum _ fun i _ ↦ hint _).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  have hsum : ∑ i, ⟪ξ, b i⟫ ^ 2 = ‖ξ‖ ^ 2 := b.sum_sq_inner_left ξ
  have hweight : |(1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)| ^ 2 = 1 + ‖ξ‖ ^ 2 := by
    rw [sq_abs, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [fourier_lineDerivOp_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    hweight, norm_mul, Complex.norm_I, Complex.norm_ofNat, Real.abs_pi, mul_one, sq_abs]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
  field_simp

open scoped LineDeriv Real in
/-- The `H¹` norm of a Schwartz function bounds the `L²` norm of each of its first derivatives
along an orthonormal basis `b`: `(2π)⁻² ∫ ‖∂_{bᵢ} u‖² ≤ ‖u‖²_{H¹}`. -/
theorem inv_two_pi_sq_mul_integral_norm_lineDerivOp_sq_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) (i : ι) :
    (2 * π)⁻¹ ^ 2 * ∫ x, ‖∂_{b i} u x‖ ^ 2 ≤ ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 := by
  rw [norm_toBesselPotentialSpaceCLM_one_sq b]
  have hi : ∫ x, ‖∂_{b i} u x‖ ^ 2 ≤ ∑ j, ∫ x, ‖∂_{b j} u x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ ∫ x, ‖∂_{b j} u x‖ ^ 2)
      (fun j _ ↦ integral_nonneg fun _ ↦ by positivity) (Finset.mem_univ i)
  have h0 : 0 ≤ ∫ x, ‖u x‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  nlinarith [mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹ ^ 2)]

/-- **Translation is an isometry of `H^s`** on Schwartz functions with Hilbert-space values. -/
@[simp]
theorem norm_toBesselPotentialSpaceCLM_compSubConstCLM {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢(E, F)) (a : E) :
    ‖toBesselPotentialSpaceCLM s 2 (u.compSubConstCLM ℂ a)‖ =
      ‖toBesselPotentialSpaceCLM s 2 u‖ := by
  rw [norm_toBesselPotentialSpaceCLM, norm_toBesselPotentialSpaceCLM]
  congr 1
  refine eLpNorm_congr_norm_ae
    (memLp_one_add_norm_sq_rpow_smul_fourier s _ 2).aestronglyMeasurable
    (memLp_one_add_norm_sq_rpow_smul_fourier s u 2).aestronglyMeasurable (.of_forall fun ξ ↦ ?_)
  simp [fourier_compSubConstCLM_apply, norm_smul]

end SchwartzMap

namespace BesselPotentialSpace

/-- Continuous linear maps out of `H^{s,p}`, `p < ∞`, into a Hausdorff space are determined by
their values on Schwartz functions. -/
theorem continuousLinearMap_ext {G : Type*} [AddCommMonoid G] [Module ℂ G] [TopologicalSpace G]
    [T2Space G] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {T T' : H^{s, p}(E, F) →L[ℂ] G}
    (h : ∀ u : 𝓢(E, F), T (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
      T' (SchwartzMap.toBesselPotentialSpaceCLM s p u)) :
    T = T' :=
  ContinuousLinearMap.ext fun f ↦ congrFun
    ((SchwartzMap.denseRange_toBesselPotentialSpaceCLM s hp).equalizer T.continuous T'.continuous
      (funext h)) f

/-- In `H^{0,p} = Lᵖ` the element with `Lᵖ` part `f` is the tempered distribution of `f`. -/
theorem toDistr_toLpₗᵢ_zero_symm_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp F p (volume : Measure E)) :
    ((toLpₗᵢ E F 0 p).symm f).toDistr = (f : 𝓢'(E, F)) := by
  rw [toLpₗᵢ_symm_apply, neg_zero, besselPotential_zero, ContinuousLinearMap.id_apply]

/-- The `H^s` norm is the `L²` norm of the weighted Fourier transform: if `⟨ξ⟩ ^ s 𝓕 u` is the
tempered distribution of `G ∈ L²`, then `‖u‖ = ‖G‖`. -/
theorem norm_eq_of_smulLeftCLM_fourier_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ} {u : H^{s}(E, F)}
    {G : Lp F 2 (volume : Measure E)}
    (h : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) = G) :
    ‖u‖ = ‖G‖ := by
  rw [← norm_fourier_toLp_eq]
  congr 1
  refine LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F)
    (μ := (volume : Measure E)) (p := 2)) ?_
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
  rw [← Lp.fourier_toTemperedDistribution_eq, ← u.bessel_toDistr_eq_toLp,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply, h]

end BesselPotentialSpace
