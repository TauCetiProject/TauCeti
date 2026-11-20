/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.Fourier.LpSpace
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.MeasureTheory.Function.Lp.Norm

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
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_zero`: on `H^{0,p}` the inclusion is isometric for
  the `Lᵖ` norm.
* `SchwartzMap.eLpNorm_le_of_toBesselPotentialSpaceCLM_eq`: the `Lᵖ` bound of an operator on
  `H^{0,p}` that sends one Schwartz function to another.
* `BesselPotentialSpace.continuousLinearMap_ext`: continuous linear maps out of `H^{s,p}`,
  `p < ∞`, are determined by their values on Schwartz functions, and
  `BesselPotentialSpace.continuousLinearMap_ext_real` for complex-linear maps out of
  `H^{s,p}(E, ℂ)` on real Schwartz functions.
* `BesselPotentialSpace.toTemperedDistribution_fourier_toLp`,
  `BesselPotentialSpace.fourier_toLp_eq_of_smulLeftCLM_fourier_eq`: for Hilbert-space values, the
  `L²` Fourier transform of the `L²` part of `u ∈ H^s` is the weighted Fourier transform
  `⟨ξ⟩ ^ s 𝓕 u`; `SchwartzMap.fourier_toLp_toBesselPotentialSpaceCLM` computes it for a Schwartz
  function.
* `BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`: for Hilbert-space values, the `H^s`
  norm is the `L²` norm of the weighted Fourier transform.
* `BesselPotentialSpace.fourier_toLp_ae_eq`: for `h ∈ H^{s,2}` whose tempered distribution has the
  Fourier transform `v ∈ L^q`, the `L²` Fourier transform of `J^s h` is `(1 + ‖ξ‖²)^{s/2} v`.
* `BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq`: Plancherel's identity
  `‖h‖²_{H^{1,2}} = ‖h‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢh‖²_{L²}` along an orthonormal basis.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM`: for Hilbert-space values, the `H^s` norm of a
  Schwartz function `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`.
* `SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier`: `⟨ξ⟩ ^ s 𝓕 u` lies in every `L^q`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_sq`: the square of the `H^s` norm of a Schwartz
  function is `∫ ⟨ξ⟩ ^ (2s) ‖𝓕 u ξ‖²`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_add_one_sq`: raising the order by one adds the
  derivatives, `‖u‖²_{H^{s+1}} = ‖u‖²_{H^s} + (2π)⁻² ∑ᵢ ‖∂_{bᵢ} u‖²_{H^s}`; in particular
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`)
  `‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_compSubConstCLM`: translation preserves the `H^s`
  norm of a Schwartz function.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_cutoffExponential_one_le`: the `H^s` norm of the
  wave packet `y ↦ exp(i ⟪y, ξ⟫) φ(y) v` is at most `2 ^ (|s| / 2) ⟨ξ / 2π⟩ ^ s ‖φ‖_{H^{|s|}} ‖v‖`,
  and
  `SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_cutoffExponential_smul_le`: hence the `H^s`
  norms of the wave packets of frequency `t ξ` are `O(t ^ s)` as `t → ∞`.
* `SchwartzMap.inv_two_pi_sq_mul_integral_norm_lineDerivOp_sq_le`: the `H¹` norm of a Schwartz
  function bounds the `L²` norm of each of its first derivatives.

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An order `s` above half the dimension of `E` is nonnegative, so that `H^{s,p}(E, F)` embeds
in `Lᵖ` (`BesselPotentialSpace.inclusionLp`). -/
theorem TauCeti.nonneg_of_finrank_lt_two_mul {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    0 ≤ s := by
  linarith [(Module.finrank ℝ E).cast_nonneg (α := ℝ)]

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

/-- The `H^{0,p}` norm of a Schwartz function is its `Lᵖ` norm. -/
theorem norm_toBesselPotentialSpaceCLM_zero (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM 0 p u‖ = (eLpNorm u p volume).toReal := by
  rw [← BesselPotentialSpace.norm_toLp_eq, toLp_toBesselPotentialSpaceCLM_zero, norm_toLp]

/-- If a bounded operator `A` on `H^{0,p} = Lᵖ` sends the Schwartz function `u` to the Schwartz
function `w`, then `‖w‖_{Lᵖ} ≤ ‖A‖ ‖u‖_{Lᵖ}`. -/
theorem eLpNorm_le_of_toBesselPotentialSpaceCLM_eq {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace G] {A : H^{0, p}(E, F) →L[ℂ] H^{0, p}(E, G)} {u : 𝓢(E, F)}
    {w : 𝓢(E, G)} (h : A (toBesselPotentialSpaceCLM 0 p u) = toBesselPotentialSpaceCLM 0 p w) :
    eLpNorm w p volume ≤ ENNReal.ofReal ‖A‖ * eLpNorm u p volume := by
  have hle := A.le_opNorm (toBesselPotentialSpaceCLM 0 p u)
  rw [h, norm_toBesselPotentialSpaceCLM_zero, norm_toBesselPotentialSpaceCLM_zero] at hle
  calc eLpNorm w p volume = ENNReal.ofReal (eLpNorm w p volume).toReal :=
        (ENNReal.ofReal_toReal (w.memLp p).eLpNorm_ne_top).symm
    _ ≤ ENNReal.ofReal (‖A‖ * (eLpNorm u p volume).toReal) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal ‖A‖ * eLpNorm u p volume := by
        rw [ENNReal.ofReal_mul (norm_nonneg A)]
        gcongr
        exact ENNReal.ofReal_toReal_le

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

/-- The `L²` Fourier transform of the `L²` part of a Schwartz function `u` in `H^s` is the weighted
Fourier transform `⟨ξ⟩ ^ s 𝓕 u`. -/
theorem fourier_toLp_toBesselPotentialSpaceCLM {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢(E, F)) :
    𝓕 (toBesselPotentialSpaceCLM s 2 u).toLp =
      (smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u)).toLp 2 := by
  rw [toLp_toBesselPotentialSpaceCLM, toLp_fourier_eq, fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]

/-- The `H^s` norm of a Schwartz function `u` is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`. -/
theorem norm_toBesselPotentialSpaceCLM {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (s : ℝ) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM s 2 u‖ =
      (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume).toReal := by
  rw [← BesselPotentialSpace.norm_toLp_eq, toLp_toBesselPotentialSpaceCLM,
    norm_toLp_fourierMultiplierCLM_eq (by fun_prop)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] in
/-- The pointwise integrand of the squared `H^r` norm:
`‖(1 + ‖ξ‖ ^ 2) ^ (r / 2) • v‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ r * ‖v‖ ^ 2`. -/
private theorem norm_one_add_norm_sq_rpow_smul_sq (r : ℝ) (ξ : E) (v : F) :
    ‖(((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • v‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ r * ‖v‖ ^ 2 := by
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos h1 _).le, mul_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul h1.le]
  norm_num

/-- The square of the `H^r` norm of a Schwartz function `u` with Hilbert-space values is
`∫ (1 + ‖ξ‖ ^ 2) ^ r ‖𝓕 u ξ‖ ^ 2`. -/
theorem norm_toBesselPotentialSpaceCLM_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (r : ℝ) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM r 2 u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ r * ‖𝓕 u ξ‖ ^ 2 := by
  have hw := memLp_one_add_norm_sq_rpow_smul_fourier (F := F) r u 2
  rw [norm_toBesselPotentialSpaceCLM, hw.eLpNorm_eq_integral_rpow_norm two_ne_zero
    ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat]
  simp_rw [Real.rpow_two]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity)]
  rw [Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, Real.rpow_one]
  exact integral_congr_ae (.of_forall fun ξ ↦ norm_one_add_norm_sq_rpow_smul_sq r ξ _)

omit [CompleteSpace F] in
/-- The integrand `(1 + ‖ξ‖ ^ 2) ^ r ‖𝓕 u ξ‖ ^ 2` of the squared `H^r` norm of a Schwartz function
is integrable. -/
theorem integrable_one_add_norm_sq_rpow_mul_norm_fourier_sq (r : ℝ) (u : 𝓢(E, F)) :
    Integrable fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ r * ‖𝓕 u ξ‖ ^ 2 := by
  refine ((memLp_one_add_norm_sq_rpow_smul_fourier (F := F) r u 2).integrable_norm_pow
    two_ne_zero).congr (.of_forall fun ξ ↦ norm_one_add_norm_sq_rpow_smul_sq r ξ _)

/-- The square of the `H⁰` norm of a Schwartz function with Hilbert-space values is the square of
its `L²` norm, `∫ ‖u‖²`. -/
theorem norm_toBesselPotentialSpaceCLM_zero_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM 0 2 u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  simp [norm_toBesselPotentialSpaceCLM_sq, integral_norm_sq_fourier]

open scoped LineDeriv Real RealInnerProductSpace in
/-- **One more order of Sobolev regularity is one more derivative.** For a Schwartz function `u`
with Hilbert-space values, every real `s` and an orthonormal basis `b` of `E`,

`‖u‖²_{H^{s+1}} = ‖u‖²_{H^s} + (2π)⁻² ∑ᵢ ‖∂_{bᵢ} u‖²_{H^s}`.

The factor `(2π)⁻²` comes from the Fourier transform of `∂_v u` being `2πi ⟪ξ, v⟫ 𝓕 u`. -/
theorem norm_toBesselPotentialSpaceCLM_add_one_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (s : ℝ) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM (s + 1) 2 u‖ ^ 2 =
      ‖toBesselPotentialSpaceCLM s 2 u‖ ^ 2 +
        (2 * π)⁻¹ ^ 2 * ∑ i, ‖toBesselPotentialSpaceCLM s 2 (∂_{b i} u)‖ ^ 2 := by
  simp only [norm_toBesselPotentialSpaceCLM_sq]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_one_add_norm_sq_rpow_mul_norm_fourier_sq _ _,
    ← integral_const_mul, ← integral_add (integrable_one_add_norm_sq_rpow_mul_norm_fourier_sq _ _)
      ((integrable_finsetSum _ fun i _ ↦
        integrable_one_add_norm_sq_rpow_mul_norm_fourier_sq _ _).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [fourier_lineDerivOp_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, Complex.norm_I, Complex.norm_ofNat, Real.abs_pi, mul_one, sq_abs]
  -- `(1 + ‖ξ‖²) ^ (s + 1) = (1 + ‖ξ‖²) ^ s (1 + ∑ᵢ ⟪ξ, bᵢ⟫²)`.
  have hsum : ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * (2 ^ 2 * π ^ 2 * ⟪ξ, b i⟫ ^ 2 * ‖𝓕 u ξ‖ ^ 2) =
      (1 + ‖ξ‖ ^ 2) ^ s * (2 ^ 2 * π ^ 2) * ‖𝓕 u ξ‖ ^ 2 * ∑ i, ⟪ξ, b i⟫ ^ 2 := by
    rw [Finset.mul_sum]
    congr 1 with i
    ring
  rw [Real.rpow_add_one h1.ne', hsum, b.sum_sq_inner_left ξ]
  field_simp

open scoped LineDeriv Real RealInnerProductSpace in
/-- **The `H¹` norm of a Schwartz function** in terms of its first derivatives: for an orthonormal
basis `b` of `E`,

`‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.

This is the case `s = 0` of `SchwartzMap.norm_toBesselPotentialSpaceCLM_add_one_sq`. -/
theorem norm_toBesselPotentialSpaceCLM_one_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 =
      (∫ x, ‖u x‖ ^ 2) + (2 * π)⁻¹ ^ 2 * ∑ i, ∫ x, ‖∂_{b i} u x‖ ^ 2 := by
  have h := norm_toBesselPotentialSpaceCLM_add_one_sq b 0 u
  rw [zero_add] at h
  simpa [norm_toBesselPotentialSpaceCLM_zero_sq] using h

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

open scoped Real in
/-- **The `H^s` norm of a wave packet.** Modulating a Schwartz function by the character
`exp(i ⟪y, ξ⟫)` translates its Fourier transform to `ξ / 2π`, so by Peetre's inequality the wave
packet `y ↦ exp(i ⟪y, ξ⟫) φ(y) v` has `H^s` norm at most
`2 ^ (|s| / 2) ⟨ξ / 2π⟩ ^ s ‖φ‖_{H^{|s|}} ‖v‖`, which is `O(‖ξ‖ ^ s)` for high frequencies. -/
theorem norm_toBesselPotentialSpaceCLM_cutoffExponential_one_le {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (φ : 𝓢(E, ℂ))
    (ξ : E) (v : F) :
    ‖toBesselPotentialSpaceCLM s 2 (φ.cutoffExponential 1 ξ v)‖ ≤
      2 ^ (|s| / 2) * (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) *
        ‖toBesselPotentialSpaceCLM |s| 2 φ‖ * ‖v‖ := by
  set c : E := (2 * π)⁻¹ • ξ
  set g : E → ℂ := fun η ↦ (((1 + ‖η‖ ^ 2) ^ (|s| / 2) : ℝ) : ℂ) • 𝓕 φ η
  set K : ℝ := 2 ^ (|s| / 2) * (1 + ‖c‖ ^ 2) ^ (s / 2) * ‖v‖
  have hg : MemLp g 2 volume := memLp_one_add_norm_sq_rpow_smul_fourier |s| φ 2
  -- Pointwise, Peetre's inequality with `ζ = c + (ζ - c)` bounds the weight at `ζ`.
  have hpt : ∀ ζ, ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 (φ.cutoffExponential 1 ξ v) ζ‖ ≤
      K * ‖g (ζ - c)‖ := by
    intro ζ
    have hP := TauCeti.one_add_norm_add_sq_rpow_le_mul s c (ζ - c)
    rw [add_sub_cancel] at hP
    rw [fourier_cutoffExponential φ one_ne_zero]
    simp only [g, K, one_pow, abs_one, inv_one, one_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ζ‖ ^ 2) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖ζ - c‖ ^ 2) _)]
    calc (1 + ‖ζ‖ ^ 2) ^ (s / 2) * (‖𝓕 φ (ζ - c)‖ * ‖v‖)
        ≤ 2 ^ (|s| / 2) * (1 + ‖c‖ ^ 2) ^ (s / 2) * (1 + ‖ζ - c‖ ^ 2) ^ (|s| / 2) *
            (‖𝓕 φ (ζ - c)‖ * ‖v‖) := by gcongr
      _ = _ := by ring
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (memLp_one_add_norm_sq_rpow_smul_fourier s (φ.cutoffExponential 1 ξ v) 2).aestronglyMeasurable
    (.of_forall hpt) 2
  -- Translation by `c` does not change the `L²` norm.
  have htr : eLpNorm (fun ζ ↦ g (ζ - c)) 2 volume = eLpNorm g 2 volume :=
    eLpNorm_comp_measurePreserving (f := fun ζ ↦ ζ - c) hg.aestronglyMeasurable
      (measurePreserving_sub_right volume c)
  rw [htr] at hle
  rw [norm_toBesselPotentialSpaceCLM, norm_toBesselPotentialSpaceCLM]
  calc _ ≤ (ENNReal.ofReal K * eLpNorm g 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top) hle
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        ring

open scoped Real in
/-- **High-frequency wave packets.** For a nonzero frequency `ξ`, the `H^s` norms of the wave
packets `y ↦ exp(i ⟪y, t ξ⟫) φ(y) v` grow at most like `t ^ s` as `t → ∞`: they are at most
`C t ^ s` for all `t ≥ 1`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_cutoffExponential_smul_le {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (s : ℝ) (φ : 𝓢(E, ℂ))
    {ξ : E} (hξ : ξ ≠ 0) (v : F) :
    ∃ C, ∀ t : ℝ, 1 ≤ t →
      ‖toBesselPotentialSpaceCLM s 2 (φ.cutoffExponential 1 (t • ξ) v)‖ ≤ C * t ^ s := by
  set c : E := (2 * π)⁻¹ • ξ
  have hc : 0 < ‖c‖ := norm_pos_iff.2 (smul_ne_zero (by positivity) hξ)
  set M := max ((‖c‖ ^ 2) ^ (s / 2)) ((1 + ‖c‖ ^ 2) ^ (s / 2))
  refine ⟨2 ^ (|s| / 2) * M * ‖toBesselPotentialSpaceCLM |s| 2 φ‖ * ‖v‖, fun t ht ↦ ?_⟩
  have hM : (1 + ‖t • c‖ ^ 2) ^ (s / 2) ≤ M * t ^ s :=
    TauCeti.one_add_norm_smul_sq_rpow_le_max_mul_rpow hc ht ⟨le_rfl, le_rfl⟩ s
  refine (norm_toBesselPotentialSpaceCLM_cutoffExponential_one_le s φ _ v).trans ?_
  rw [smul_comm (2 * π)⁻¹ t ξ]
  calc 2 ^ (|s| / 2) * (1 + ‖t • c‖ ^ 2) ^ (s / 2) * ‖toBesselPotentialSpaceCLM |s| 2 φ‖ * ‖v‖
      ≤ 2 ^ (|s| / 2) * (M * t ^ s) * ‖toBesselPotentialSpaceCLM |s| 2 φ‖ * ‖v‖ := by gcongr
    _ = _ := by ring

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

/-- Continuous complex-linear maps out of `H^{s,p}(E, ℂ)`, `p < ∞`, into a Hausdorff space are
determined by their values on real Schwartz functions, embedded by `Complex.ofRealCLM`. -/
theorem continuousLinearMap_ext_real {G : Type*} [AddCommMonoid G] [Module ℂ G]
    [TopologicalSpace G] [T2Space G] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {T T' : H^{s, p}(E, ℂ) →L[ℂ] G}
    (h : ∀ u : 𝓢(E, ℝ),
      T (SchwartzMap.toBesselPotentialSpaceCLM s p (u.postcompCLM Complex.ofRealCLM)) =
        T' (SchwartzMap.toBesselPotentialSpaceCLM s p (u.postcompCLM Complex.ofRealCLM))) :
    T = T' := by
  refine continuousLinearMap_ext hp fun φ ↦ ?_
  rw [← SchwartzMap.postcompCLM_re_add_I_smul_im φ]
  simp only [map_add, map_smul, h]

/-- In `H^{0,p} = Lᵖ` the element with `Lᵖ` part `f` is the tempered distribution of `f`. -/
theorem toDistr_toLpₗᵢ_zero_symm_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp F p (volume : Measure E)) :
    ((toLpₗᵢ E F 0 p).symm f).toDistr = (f : 𝓢'(E, F)) := by
  rw [toLpₗᵢ_symm_apply, neg_zero, besselPotential_zero, ContinuousLinearMap.id_apply]

section Fourier

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ}

/-- The `L²` Fourier transform of the `L²` part of `u ∈ H^s` is the weighted Fourier transform
`⟨ξ⟩ ^ s 𝓕 u` of the tempered distribution `u`. -/
theorem toTemperedDistribution_fourier_toLp (u : H^{s}(E, F)) :
    ((𝓕 u.toLp : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) := by
  rw [← Lp.fourier_toTemperedDistribution_eq, ← u.bessel_toDistr_eq_toLp,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply]

/-- **The Fourier transform of the Bessel potential.** If `h ∈ H^{s,2}` has a tempered distribution
whose Fourier transform is an `L^q` function `v`, for any `1 ≤ q ≤ ∞`, then the Fourier transform of
the `L²` function `J^s h` is `(1 + ‖ξ‖²)^{s/2} v(ξ)` almost everywhere. -/
theorem fourier_toLp_ae_eq (h : H^{s}(E, F)) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {v : Lp F q (volume : Measure E)} (hv : 𝓕 h.toDistr = v) :
    𝓕 h.toLp =ᵐ[volume] fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • v ξ := by
  rw [← Lp.toTemperedDistribution_eq_smulLeftCLM_iff (by fun_prop),
    toTemperedDistribution_fourier_toLp, hv]

/-- If the weighted Fourier transform `⟨ξ⟩ ^ s 𝓕 u` of `u ∈ H^s` is the tempered distribution of
`G ∈ L²`, then `G` is the `L²` Fourier transform of the `L²` part of `u`. -/
theorem fourier_toLp_eq_of_smulLeftCLM_fourier_eq {u : H^{s}(E, F)}
    {G : Lp F 2 (volume : Measure E)}
    (h : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) = G) :
    𝓕 u.toLp = G :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F)
    (μ := (volume : Measure E)) (p := 2)) (by
      simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
      rw [toTemperedDistribution_fourier_toLp, h])

/-- The `H^s` norm is the `L²` norm of the weighted Fourier transform: if `⟨ξ⟩ ^ s 𝓕 u` is the
tempered distribution of `G ∈ L²`, then `‖u‖ = ‖G‖`. -/
theorem norm_eq_of_smulLeftCLM_fourier_eq {u : H^{s}(E, F)} {G : Lp F 2 (volume : Measure E)}
    (h : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) = G) :
    ‖u‖ = ‖G‖ := by
  rw [← norm_fourier_toLp_eq, fourier_toLp_eq_of_smulLeftCLM_fourier_eq h]

open scoped LineDeriv Real in
/-- **Plancherel's identity for `H^{1,2}`.** Let `b` be an orthonormal basis of `E` and let
`h ∈ H^{1,2}(E, F)` be the `L²` function `g`, with derivatives `∂_{bᵢ} h` the `L²` functions `dᵢ`.
Then `‖h‖² = ‖g‖² + (2π)⁻² ∑ᵢ ‖dᵢ‖²`. The factor `(2π)⁻²` comes from Mathlib's normalisation of the
Fourier transform, under which `∂_{bᵢ}` has symbol `2πi⟪ξ, bᵢ⟫` and `J¹` has symbol
`(1 + ‖ξ‖²)^{1/2}`. -/
theorem norm_sq_eq_norm_sq_add_mul_sum_norm_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (h : H^{1}(E, F)) {g : Lp F 2 (volume : Measure E)} (hg : h.toDistr = g)
    {d : ι → Lp F 2 (volume : Measure E)} (hd : ∀ i, ∂_{b i} h.toDistr = d i) :
    ‖h‖ ^ 2 = ‖g‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ∑ i, ‖d i‖ ^ 2 := by
  have hv : 𝓕 h.toDistr = 𝓕 g := by rw [hg, Lp.fourier_toTemperedDistribution_eq]
  have hint (f : Lp F 2 (volume : Measure E)) : Integrable (fun ξ ↦ ‖f ξ‖ ^ 2) :=
    (Lp.memLp f).integrable_norm_pow two_ne_zero
  -- On the Fourier side, `‖𝓕 (J¹ h)‖² = (1 + ‖ξ‖²) ‖𝓕 g‖²` and `‖𝓕 dᵢ‖² = 4π² ⟪ξ, bᵢ⟫² ‖𝓕 g‖²`.
  have hpt : (fun ξ ↦ ‖𝓕 h.toLp ξ‖ ^ 2) =ᵐ[volume]
      fun ξ ↦ ‖𝓕 g ξ‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ∑ i, ‖𝓕 (d i) ξ‖ ^ 2 := by
    filter_upwards [fourier_toLp_ae_eq h hv,
      ae_all_iff.2 fun i ↦ Lp.fourier_ae_eq_of_lineDerivOp_eq hv (hd i)] with ξ hξ hξd
    have hsum : ∑ i, ‖𝓕 (d i) ξ‖ ^ 2 = (2 * π) ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 g ξ‖ ^ 2 := by
      simp only [hξd, norm_smul, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, mul_pow, sq_abs,
        ← Finset.sum_mul, ← Finset.mul_sum, b.sum_sq_inner_left]
    rw [hξ, hsum, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [← norm_fourier_toLp_eq h, ← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae hpt,
    integral_add (hint _) ((integrable_finsetSum _ fun i _ ↦ hint _).const_mul _),
    integral_const_mul, integral_finsetSum _ fun i _ ↦ hint _]
  simp only [Lp.integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq]

end Fourier

end BesselPotentialSpace
