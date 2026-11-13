/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp

/-!
# Sobolev embeddings of `H^s(ℝⁿ)` into `C₀(ℝⁿ)` and `C^k(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space of dimension `n`. A function in the
`L²` Sobolev space of order `s > n / 2` on `E` agrees almost everywhere with a continuous function
vanishing at infinity, and

`|u(x)| ≤ C ‖u‖_{H^s}` for almost every `x`,

with `C` the `L²` norm of `(1 + ‖ξ‖ ^ 2) ^ (-s / 2)`. If `s > k + n / 2`, this continuous
representative is `C^k`, its derivatives of order `j ≤ k` vanish at infinity, and

`‖D^j u(x)‖ ≤ C ‖u‖_{H^s}` for all `x` and `j ≤ k`.

A tempered distribution lying in `H^s` for every real `s` is therefore a smooth function. These
whole-space statements hold for every real order and with values in a complex Hilbert space; for
integer orders on an open set, without bounds, see `TauCeti.Wkp.exists_contDiffOn_ae_eq`. For the
weak-derivative space `W^{k,2}(ℝⁿ)` with `2k > n` the continuous representative depends linearly
and boundedly on the function, so that

`sup_x |u(x)| ≤ C ‖u‖_{W^{k,2}}`.

## The Fourier argument

For a tempered distribution `u` in the Bessel-potential space `H^s`, `2s > n`, Mathlib's
`TemperedDistribution.MemSobolev.fourier_memL1` shows that its Fourier transform is an `L¹`
function `v`: Cauchy–Schwarz pairs `(1 + |ξ|²)^{s/2} 𝓕u ∈ L²` with `(1 + |ξ|²)^{-s/2} ∈ L²`. Fourier
inversion on `𝓢'` gives `u = 𝓕⁻ v`, and for `v ∈ L¹` the distribution `𝓕⁻ v` is the function
`x ↦ ∫ e^{2πi⟪ξ, x⟫} v(ξ) dξ` (`MeasureTheory.Lp.fourierInv_toTemperedDistribution_apply`). This
function is continuous by dominated convergence and vanishes at infinity by the Riemann–Lebesgue
lemma, and it represents `u` almost everywhere because both have the same pairings with Schwartz
functions (`MeasureTheory.Lp.ae_eq_of_toTemperedDistribution_apply_eq`). Quantitatively,
`|𝓕⁻ v (x)| ≤ ‖v‖₁`, and by Plancherel the `H^s` norm of `u` is the `L²` norm of
`(1 + |ξ|²)^{s/2} v`, so Cauchy–Schwarz gives `‖v‖₁ ≤ ‖(1 + |ξ|²)^{-s/2}‖₂ ‖u‖_{H^s}`
(`TemperedDistribution.MemSobolev.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace`,
`TauCeti.memLp_rpow_neg_one_add_norm_sq`).

For derivatives the same argument applies to the moments of `v`: Cauchy–Schwarz pairs
`(1 + |ξ|²)^{s/2} v ∈ L²` with `(1 + |ξ|²)^{-(s-j)/2} ∈ L²`, so `‖ξ‖ ^ j ‖v ξ‖` is integrable when
`2 (s - j) > n`. Mathlib's `Real.contDiff_fourier` and `Real.iteratedFDeriv_fourier` then make
`𝓕⁻ v` a `C^k` function whose `j`-th derivative is the Fourier transform of an integrable function,
bounded by `(2π) ^ j ∫ ‖ξ‖ ^ j ‖v ξ‖` and vanishing at infinity by the Riemann–Lebesgue lemma.

On the whole space the weak-derivative space `W^{k,2}` is the Bessel-potential space `H^{k,2}`
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), so every `u ∈ W^{k,2}(ℝⁿ)` has a
representative in `C₀(ℝⁿ)`. Two continuous functions that agree almost everywhere are equal, so
the representative is unique and depends linearly on `u`. Its graph is closed, since convergence
in `W^{k,2}` gives almost-everywhere convergence along a subsequence and convergence in `C₀` is
uniform, so the closed graph theorem makes the map `u ↦ u` bounded from `W^{k,2}(ℝⁿ)` to `C₀(ℝⁿ)`.

The statements are for Lebesgue measure `volume`, the measure of Mathlib's Bessel-potential
spaces.

## Main declarations

* `TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`: an `L²` function in
  `H^s`, `2s > n`, agrees almost everywhere with a continuous function vanishing at infinity.
* `MemSobolev.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace` (in
  `TemperedDistribution`): the `H^s` norm of a distribution whose Fourier transform is an `L¹`
  function `v` is the `L²` norm of `(1 + ‖ξ‖ ^ 2) ^ (s / 2) v`.
* `TemperedDistribution.MemSobolev.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace`: the bound
  `‖v‖₁ ≤ ‖(1 + ‖ξ‖ ^ 2) ^ (-s / 2)‖₂ ‖f‖_{H^s}` for that `v`.
* `TemperedDistribution.exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace`: the bound
  `|u(x)| ≤ C ‖u‖_{H^s}`, `2s > n`, almost everywhere.
* `TemperedDistribution.ae_tendsto_of_tendsto_toBesselPotentialSpace`: convergence in `H^s`,
  `2s > n`, implies convergence almost everywhere.
* `TemperedDistribution.tendsto_cocompact_of_mem_realSobolevFunctions`: a continuous real
  function in `H^s`, `2s > n`, tends to zero at infinity.
* `TemperedDistribution.MemSobolev.exists_contDiff_ae_eq`: an `L²` function in `H^s`,
  `2s > n + 2k`, agrees almost everywhere with a `C^k` function.
* `TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions`: the version for real
  functions; `TemperedDistribution.exists_contDiff_ae_eq_of_forall_mem_realSobolevFunctions` gives
  a smooth representative of a real function lying in every `H^k`.
* `TemperedDistribution.contDiff_of_mem_realSobolevFunctions`,
  `TemperedDistribution.exists_norm_iteratedFDeriv_le_of_mem_realSobolevFunctions`: a continuous
  real function in `H^s`, `2s > n + 2k`, is `C^k` with bounded derivatives of order at most `k`.
* `TemperedDistribution.MemSobolev.integrable_norm_pow_mul_norm`,
  `TemperedDistribution.MemSobolev.integral_norm_pow_mul_norm_le`: the moments
  `∫ ‖ξ‖ ^ j ‖v ξ‖ ≤ ‖(1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)‖₂ ‖f‖_{H^s}` of `v = 𝓕 f`, `2 (s - j) > n`.
* `TemperedDistribution.MemSobolev.contDiff_of_ae_eq`: a continuous representative of an `L²`
  function in `H^s`, `s > k + n / 2`, is `C^k`.
* `TemperedDistribution.MemSobolev.tendsto_iteratedFDeriv_cocompact_of_ae_eq`: its derivatives
  of order `j`, `s > j + n / 2`, vanish at infinity.
* `TemperedDistribution.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace`: the bound
  `‖D^j u(x)‖ ≤ C ‖u‖_{H^s}` for `j ≤ k`, `s > k + n / 2`.
* `TemperedDistribution.contDiff_of_forall_memSobolev_of_ae_eq`,
  `TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev`: functions and tempered
  distributions lying in every `H^s` are smooth.
* `TauCeti.Wkp.toZeroAtInfty`: the Sobolev embedding `W^{k,2}(ℝⁿ) →L[ℝ] C₀(ℝⁿ)` for `2k > n`.
* `TauCeti.Wkp.value_ae_eq_toZeroAtInfty`, `TauCeti.Wkp.toZeroAtInfty_eq_iff`: the embedding sends
  a Sobolev function to its unique continuous representative.
* `TauCeti.Wkp.toZeroAtInfty_injective`: the continuous representative determines the Sobolev
  function.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., §9.3 (the Sobolev embeddings `H_s ⊆ C₀` for
  `s > n / 2` and `H_s ⊆ C^k` for `s > k + n / 2`, proved by showing that the Fourier transform,
  weighted by `|ξ|^j` for `j ≤ k`, is integrable).
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology TopologicalSpace
open scoped FourierTransform SchwartzMap ZeroAtInfty ENNReal Real

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TemperedDistribution

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Sobolev embedding into `C₀`.** An `L²` function on `E` lying in the Bessel-potential space
`H^s` with `s > dim E / 2` agrees almost everywhere with a continuous function vanishing at
infinity. -/
theorem MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F))) :
    ∃ g : C₀(E, F), u =ᵐ[volume] g := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 hs
  have hint : Integrable (fun x => (v : E → F) (-x)) :=
    (L1.integrable_coeFn v).comp_neg
  -- The inverse Fourier transform of `v` is the Fourier transform of `x ↦ v (-x)`.
  have hneg : 𝓕⁻ (v : E → F) = 𝓕 (fun x => (v : E → F) (-x)) :=
    Real.fourierInv_eq_fourier_comp_neg _
  let g : C₀(E, F) :=
    { toFun := 𝓕⁻ (v : E → F)
      continuous_toFun := hneg ▸ VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar
        (by simpa only [innerₗ_apply_apply] using continuous_inner) hint
      zero_at_infty' := hneg ▸ tendsto_integral_exp_inner_smul_cocompact _ }
  -- Fourier inversion on `𝓢'` identifies `u` with `𝓕⁻ v`.
  refine ⟨g, ?_⟩
  rw [ZeroAtInftyContinuousMap.coe_mk]
  exact Lp.ae_eq_fourierInv_of_fourier_eq hv

/-- **The `H^s` norm on the Fourier side.** If the Fourier transform of `f ∈ H^s` is an `L¹`
function `v`, then `‖f‖_{H^s}` is the `L²` norm of `(1 + ‖ξ‖ ^ 2) ^ (s / 2) v`. -/
theorem MemSobolev.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace {s : ℝ}
    {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    eLpNorm (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v ξ) 2 volume =
      ‖hf.toBesselPotentialSpace‖ₑ := by
  set U := hf.toBesselPotentialSpace.toLp
  have hU : besselPotential E F s f = U := by
    simpa using hf.toBesselPotentialSpace.bessel_toDistr_eq_toLp
  have hwg : (fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hwc : Continuous fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (s / 2) :=
    (by fun_prop : Continuous fun ξ : E => 1 + ‖ξ‖ ^ 2).rpow_const fun ξ =>
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  -- The `L²` function `𝓕 U` represents the weight times `v`.
  have hae : ((𝓕 U : Lp F 2 (volume : Measure E)) : E → F) =ᵐ[volume]
      fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v ξ := by
    refine Lp.ae_eq_of_toTemperedDistribution_apply_eq (𝓕 U) ?_ fun φ => ?_
    · refine locallyIntegrable_iff.2 fun K hK => ?_
      exact (L1.integrable_coeFn v).integrableOn.continuousOn_smul hwc.continuousOn hK
    · rw [← Lp.fourier_toTemperedDistribution_eq U, ← hU,
        fourier_besselPotential_eq_smulLeftCLM_fourier_apply, hv,
        Lp.smulLeftCLM_toTemperedDistribution_apply hwg]
      simp only [Complex.coe_smul]
  rw [eLpNorm_congr_ae hae.symm, ← Lp.eNorm_def, ← ofReal_norm, ← ofReal_norm,
    BesselPotentialSpace.norm_fourier_toLp_eq]

/-- If the Fourier transform of `f ∈ H^s` is an `L¹` function `v`, then
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) v` is square integrable. -/
theorem MemSobolev.memLp_one_add_norm_sq_rpow_smul {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v ξ) 2 :=
  memLp_iff.2
    (hf.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace hv ▸ eNorm_lt_top)

/-- **The `L¹` norm on the Fourier side.** If the Fourier transform of `f ∈ H^s` is an `L¹`
function `v`, then `‖v‖₁ ≤ ‖(1 + ‖ξ‖ ^ 2) ^ (-s / 2)‖₂ ‖f‖_{H^s}`, by Cauchy–Schwarz. The first
factor is finite when `2s > dim E` (`TauCeti.memLp_rpow_neg_one_add_norm_sq`). -/
theorem MemSobolev.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace {s : ℝ} {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    eLpNorm v 1 volume ≤ eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume *
      ‖hf.toBesselPotentialSpace‖ₑ := by
  have h :=
    TauCeti.eLpNorm_one_le_eLpNorm_rpow_neg_one_add_norm_sq_mul_eLpNorm_one_add_norm_sq_rpow_smul
      (volume : Measure E) s (v : E → F)
  rwa [hf.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace hv] at h

/-- **The quantitative Sobolev embedding `H^s ⊆ L^∞`, `s > n / 2`.** There is a constant `C`,
depending only on `s` and `E`, such that every `L²` function `u ∈ H^s` satisfies
`|u(x)| ≤ C ‖u‖_{H^s}` for almost every `x`. -/
theorem exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace {s : ℝ}
    (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F))),
      ∀ᵐ x ∂volume, ‖u x‖ ≤ C * ‖hu.toBesselPotentialSpace‖ := by
  set K := eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume
  have hK : K ≠ ∞ := (TauCeti.memLp_rpow_neg_one_add_norm_sq volume hs).ne
  refine ⟨K.toReal, ENNReal.toReal_nonneg, fun {u} hu => ?_⟩
  obtain ⟨v, hv⟩ := hu.fourier_memL1 hs
  have hi := L1.integrable_coeFn v
  -- `‖v‖₁ ≤ K ‖u‖_{H^s}` by Cauchy–Schwarz and the Fourier form of the `H^s` norm.
  have hL1 : ∫ ξ, ‖v ξ‖ ≤ K.toReal * ‖hu.toBesselPotentialSpace‖ := by
    have h : eLpNorm v 1 volume ≤ K * ‖hu.toBesselPotentialSpace‖ₑ :=
      hu.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace hv
    rw [eLpNorm_one_eq_lintegral_eNorm hi.aestronglyMeasurable,
      ← ofReal_norm, ← ENNReal.ofReal_toReal hK,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h
    rw [integral_norm_eq_lintegral_eNorm hi.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  filter_upwards [Lp.ae_eq_fourierInv_of_fourier_eq hv] with x hx
  rw [hx, Real.fourierInv_eq_fourier_comp_neg]
  refine (Real.norm_fourier_le_integral_norm _ x).trans ?_
  rw [integral_neg_eq_self (fun ξ => ‖(v : E → F) ξ‖)]
  exact hL1

/-- **Convergence in `H^s` implies convergence almost everywhere, `s > n / 2`.** If `L²`
functions `u n ∈ H^s` converge in `H^s` to an `L²` function `v ∈ H^s`, then `u n x → v x` for
almost every `x`. -/
theorem ae_tendsto_of_tendsto_toBesselPotentialSpace {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : ℕ → Lp F 2 (volume : Measure E)} {v : Lp F 2 (volume : Measure E)}
    (hu : ∀ n, MemSobolev s 2 (u n : 𝓢'(E, F))) (hv : MemSobolev s 2 (v : 𝓢'(E, F)))
    (h : Tendsto (fun n => (hu n).toBesselPotentialSpace) atTop (𝓝 hv.toBesselPotentialSpace)) :
    ∀ᵐ x ∂volume, Tendsto (fun n => u n x) atTop (𝓝 (v x)) := by
  obtain ⟨C, -, hC⟩ := exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (F := F) hs
  have hD (n : ℕ) : MemSobolev s 2 ((u n - v : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    rw [Lp.toTemperedDistribution_sub]
    exact (hu n).sub hv
  have hlim : Tendsto (fun n => C * ‖(hD n).toBesselPotentialSpace‖) atTop (𝓝 0) := by
    have h' := (tendsto_iff_norm_sub_tendsto_zero.1 h).const_mul C
    rw [mul_zero] at h'
    refine h'.congr fun n => ?_
    simp only [Lp.toTemperedDistribution_sub, (hu n).toBesselPotentialSpace_sub hv]
  filter_upwards [ae_all_iff.2 fun n => hC (hD n), ae_all_iff.2 fun n => Lp.coeFn_sub (u n) v]
    with x hx hsub
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
  simpa only [hsub n, Pi.sub_apply] using hx n

/-- **Continuous Sobolev functions vanish at infinity.** A continuous real function in `H^s`,
`s > dim E / 2`, tends to zero at infinity: it agrees almost everywhere, hence everywhere, with
the continuous representative given by `MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`. -/
theorem tendsto_cocompact_of_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) (hcont : Continuous f) :
    Tendsto f (cocompact E) (𝓝 0) := by
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨g, hg⟩ := hS.exists_zeroAtInftyContinuousMap_ae_eq hs
  have hae : (fun x ↦ (f x : ℂ)) =ᵐ[volume] g := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu, hg] with x h₁ h₂ h₃
    rw [← h₃, h₁, h₂, Complex.ofRealCLM_apply]
  have hc : Continuous fun x ↦ (f x : ℂ) := Complex.continuous_ofReal.comp hcont
  have heq := (hc.ae_eq_iff_eq volume g.continuous).1 hae
  have hg0 : Tendsto (fun x ↦ (f x : ℂ)) (cocompact E) (𝓝 0) := heq ▸ g.zero_at_infty'
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp hg0

/-! ### Derivatives: the embedding `H^s ⊆ C^k` for `s > k + n / 2` -/

/-- Both moment statements at once: `‖ξ‖ ^ j ‖v ξ‖` is dominated by the integrable function
`(1 + ‖ξ‖ ^ 2) ^ (j / 2) ‖v ξ‖`, whose integral Cauchy–Schwarz bounds. -/
private theorem MemSobolev.integrable_norm_pow_mul_norm_and_integral_le {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    Integrable (fun ξ : E => ‖ξ‖ ^ j * ‖v ξ‖) ∧
      ∫ ξ, ‖ξ‖ ^ j * ‖v ξ‖ ≤
        (eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)) 2 volume).toReal *
          ‖hf.toBesselPotentialSpace‖ := by
  set K := eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)) 2 volume
  have hK : K ≠ ∞ := (TauCeti.memLp_rpow_neg_one_add_norm_sq volume hs).ne
  -- The weighted function `w = (1 + ‖ξ‖ ^ 2) ^ (j / 2) v` dominates `‖ξ‖ ^ j ‖v ξ‖`.
  set w : E → F := fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) • v ξ
  have hwc : Continuous fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) :=
    (by fun_prop : Continuous fun ξ : E => 1 + ‖ξ‖ ^ 2).rpow_const fun ξ =>
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  have hvm : AEStronglyMeasurable (v : E → F) := (L1.integrable_coeFn v).aestronglyMeasurable
  have hwm : AEStronglyMeasurable w := hwc.aestronglyMeasurable.smul hvm
  have hw : eLpNorm w 1 volume ≤ K * ‖hf.toBesselPotentialSpace‖ₑ := by
    have h :=
      TauCeti.eLpNorm_one_le_eLpNorm_rpow_neg_one_add_norm_sq_mul_eLpNorm_one_add_norm_sq_rpow_smul
        (volume : Measure E) (s - j) w
    have heq : (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ ((s - j) / 2) • w ξ) =
        fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2) • v ξ := by
      funext ξ
      simp only [w, smul_smul, ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2)]
      congr 2
      ring
    rwa [heq, hf.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace hv] at h
  have hlt : eLpNorm w 1 volume < ∞ :=
    hw.trans_lt (ENNReal.mul_lt_top hK.lt_top eNorm_lt_top)
  have hwi : Integrable w := memLp_one_iff_integrable.1 hlt
  have hle (ξ : E) : ‖ξ‖ ^ j * ‖v ξ‖ ≤ ‖w ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    calc ‖ξ‖ ^ j = (‖ξ‖ ^ (2 : ℝ)) ^ ((j : ℝ) / 2) := by
          rw [← Real.rpow_mul (norm_nonneg ξ), show (2 : ℝ) * ((j : ℝ) / 2) = j by ring,
            Real.rpow_natCast]
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ ((j : ℝ) / 2) := by
          rw [Real.rpow_two]
          gcongr
          linarith
  have hint : Integrable (fun ξ : E => ‖ξ‖ ^ j * ‖v ξ‖) :=
    hwi.norm.mono' ((continuous_norm.pow j).aestronglyMeasurable.mul hvm.norm)
      (.of_forall fun ξ => (Real.norm_of_nonneg (by positivity)).trans_le (hle ξ))
  refine ⟨hint, ?_⟩
  calc ∫ ξ, ‖ξ‖ ^ j * ‖v ξ‖ ≤ ∫ ξ, ‖w ξ‖ := integral_mono hint hwi.norm hle
    _ ≤ K.toReal * ‖hf.toBesselPotentialSpace‖ := by
      rw [integral_norm_eq_lintegral_eNorm hwm]
      rw [eLpNorm_one_eq_lintegral_eNorm hwm, ← ofReal_norm, ← ENNReal.ofReal_toReal hK,
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hw
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hw

/-- **Moments of the Fourier transform of a Sobolev function.** If the Fourier transform of
`f ∈ H^s` is an `L¹` function `v` and `2 (s - j) > dim E`, then `‖ξ‖ ^ j ‖v ξ‖` is integrable. -/
theorem MemSobolev.integrable_norm_pow_mul_norm {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    Integrable (fun ξ : E => ‖ξ‖ ^ j * ‖v ξ‖) :=
  (hf.integrable_norm_pow_mul_norm_and_integral_le hs hv).1

/-- **The moment bound.** If the Fourier transform of `f ∈ H^s` is an `L¹` function `v` and
`2 (s - j) > dim E`, then `∫ ‖ξ‖ ^ j ‖v ξ‖ ≤ ‖(1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)‖₂ ‖f‖_{H^s}`, by
Cauchy–Schwarz. For `j = 0` this is
`TemperedDistribution.MemSobolev.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace`. -/
theorem MemSobolev.integral_norm_pow_mul_norm_le {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    ∫ ξ, ‖ξ‖ ^ j * ‖v ξ‖ ≤
      (eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)) 2 volume).toReal *
        ‖hf.toBesselPotentialSpace‖ :=
  (hf.integrable_norm_pow_mul_norm_and_integral_le hs hv).2

/-- The moments of `ξ ↦ v (-ξ)`, the function whose Fourier transform is `𝓕⁻ v`, are those of
`v`. -/
private theorem MemSobolev.integrable_norm_pow_mul_norm_neg {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    Integrable (fun ξ : E => ‖ξ‖ ^ j * ‖(v : E → F) (-ξ)‖) := by
  simpa only [norm_neg] using (hf.integrable_norm_pow_mul_norm hs hv).comp_neg

/-- If the Fourier transform of `f ∈ H^s` is an `L¹` function `v`, then `𝓕⁻ v` is `C^k` when
`2 (s - k) > dim E`. -/
private theorem MemSobolev.contDiff_fourierInv {s : ℝ} {k : ℕ}
    (hs : finrank ℝ E < 2 * (s - k)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    ContDiff ℝ k (𝓕⁻ (v : E → F)) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  refine Real.contDiff_fourier (N := k) fun j hj => hf.integrable_norm_pow_mul_norm_neg ?_ hv
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  linarith

open VectorFourier in
/-- The `j`-th derivative of `𝓕⁻ v` is the Fourier transform of
`ξ ↦ (-2πi ⟪ξ, ·⟫) ^ j v (-ξ)`. -/
private theorem MemSobolev.iteratedFDeriv_fourierInv {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) :
    iteratedFDeriv ℝ j (𝓕⁻ (v : E → F)) =
      𝓕 (fun ξ => fourierPowSMulRight (innerSL ℝ) (fun ξ => (v : E → F) (-ξ)) ξ j) := by
  have hvm : AEStronglyMeasurable (fun ξ => (v : E → F) (-ξ)) :=
    (L1.integrable_coeFn v).comp_neg.aestronglyMeasurable
  have hint (i : ℕ) (hi : (i : ℕ∞) ≤ j) :
      Integrable (fun ξ : E => ‖ξ‖ ^ i * ‖(v : E → F) (-ξ)‖) := by
    refine hf.integrable_norm_pow_mul_norm_neg ?_ hv
    have hi' : (i : ℝ) ≤ j := by exact_mod_cast hi
    linarith
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact Real.iteratedFDeriv_fourier (N := j) hint hvm le_rfl

/-- The bound `‖D^j (𝓕⁻ v) x‖ ≤ (2π) ^ j ‖(1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)‖₂ ‖f‖_{H^s}`. -/
private theorem MemSobolev.norm_iteratedFDeriv_fourierInv_le {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    {v : Lp F 1 (volume : Measure E)} (hv : 𝓕 f = v) (x : E) :
    ‖iteratedFDeriv ℝ j (𝓕⁻ (v : E → F)) x‖ ≤
      (2 * π) ^ j * (eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)) 2 volume).toReal *
        ‖hf.toBesselPotentialSpace‖ := by
  rw [hf.iteratedFDeriv_fourierInv hs hv]
  refine (Real.norm_fourier_le_integral_norm _ x).trans ?_
  calc ∫ ξ, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun ξ => (v : E → F) (-ξ)) ξ j‖
      ≤ ∫ ξ, (2 * π) ^ j * (‖ξ‖ ^ j * ‖(v : E → F) (-ξ)‖) := by
        refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _)
          ((hf.integrable_norm_pow_mul_norm_neg hs hv).const_mul _) (.of_forall fun ξ => ?_)
        refine (VectorFourier.norm_fourierPowSMulRight_le _ _ ξ j).trans ?_
        have hL : 2 * π * ‖innerSL ℝ (E := E)‖ ≤ 2 * π := by
          simpa using mul_le_mul_of_nonneg_left (norm_innerSL_le (E := E) ℝ)
            (by positivity : (0 : ℝ) ≤ 2 * π)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hL j) (by positivity)
    _ = (2 * π) ^ j * ∫ ξ, ‖ξ‖ ^ j * ‖(v : E → F) ξ‖ := by
        rw [integral_const_mul]
        congr 1
        simpa only [norm_neg] using integral_neg_eq_self (fun ξ : E => ‖ξ‖ ^ j * ‖(v : E → F) ξ‖)
          volume
    _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        exact hf.integral_norm_pow_mul_norm_le hs hv

/-- **Sobolev embedding into `C^k`.** A continuous representative `g` of an `L²` function in the
Bessel-potential space `H^s` with `s > k + dim E / 2` is `k` times continuously differentiable.
Such a representative exists by `MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`. -/
theorem MemSobolev.contDiff_of_ae_eq {s : ℝ} {k : ℕ} (hs : finrank ℝ E < 2 * (s - k))
    {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F))) {g : E → F}
    (hg : Continuous g) (hug : u =ᵐ[volume] g) : ContDiff ℝ k g := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  rw [Lp.eq_fourierInv_of_ae_eq hv hg hug]
  exact hu.contDiff_fourierInv hs hv

/-- **Sobolev embedding into `C^k`.** An `L²` function on `E` lying in the Bessel-potential space
`H^s` with `s > dim E / 2 + k` agrees almost everywhere with a `C^k` function. -/
theorem MemSobolev.exists_contDiff_ae_eq {s : ℝ} {k : ℕ} (hs : finrank ℝ E + 2 * k < 2 * s)
    {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F))) :
    ∃ g : E → F, ContDiff ℝ k g ∧ u =ᵐ[volume] g := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by linarith [k.cast_nonneg (α := ℝ)])
  exact ⟨𝓕⁻ (v : E → F), hu.contDiff_fourierInv (by linarith) hv,
    Lp.ae_eq_fourierInv_of_fourier_eq hv⟩

/-- **Real Sobolev functions are `C^k` almost everywhere.** A real function in `H^s`,
`s > dim E / 2 + k`, agrees almost everywhere with a `C^k` function. -/
theorem exists_contDiff_ae_eq_of_mem_realSobolevFunctions {s : ℝ} {k : ℕ}
    (hs : finrank ℝ E + 2 * k < 2 * s) {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) :
    ∃ g : E → ℝ, ContDiff ℝ k g ∧ f =ᵐ[volume] g := by
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨g, hg, hug⟩ := hS.exists_contDiff_ae_eq hs
  refine ⟨fun x ↦ (g x).re, Complex.reCLM.contDiff.comp hg, ?_⟩
  filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu, hug] with x h₁ h₂ h₃
  rw [← h₃, h₁, h₂, Complex.ofRealCLM_apply, Complex.ofReal_re]

open scoped ContDiff in
/-- **Functions in every Sobolev space are smooth almost everywhere.** A real function lying in
`H^k` for every `k` agrees almost everywhere with a smooth function. The `C^n` representatives
given by `exists_contDiff_ae_eq_of_mem_realSobolevFunctions` for the various `n` agree almost
everywhere, hence everywhere, since they are continuous. -/
theorem exists_contDiff_ae_eq_of_forall_mem_realSobolevFunctions {f : E → ℝ}
    (hf : ∀ k : ℕ, f ∈ realSobolevFunctions E k 2) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ f =ᵐ[volume] g := by
  have hs (n : ℕ) : (finrank ℝ E : ℝ) + 2 * n < 2 * ((finrank ℝ E + n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [(finrank ℝ E).cast_nonneg (α := ℝ)]
  choose g hg hfg using fun n : ℕ ↦
    exists_contDiff_ae_eq_of_mem_realSobolevFunctions (hs n) (hf (finrank ℝ E + n + 1))
  refine ⟨g 0, contDiff_infty.2 fun n ↦ ?_, hfg 0⟩
  rw [← ((hg n).continuous.ae_eq_iff_eq volume (hg 0).continuous).1 ((hfg n).symm.trans (hfg 0))]
  exact hg n

/-- **Continuous Sobolev functions are `C^k`.** A continuous real function in `H^s`,
`s > dim E / 2 + k`, is of class `C^k`: it agrees almost everywhere, hence everywhere, with the
`C^k` representative given by `exists_contDiff_ae_eq_of_mem_realSobolevFunctions`. -/
theorem contDiff_of_mem_realSobolevFunctions {s : ℝ} {k : ℕ} (hs : finrank ℝ E + 2 * k < 2 * s)
    {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2) (hcont : Continuous f) :
    ContDiff ℝ k f := by
  obtain ⟨g, hg, hfg⟩ := exists_contDiff_ae_eq_of_mem_realSobolevFunctions hs hf
  rwa [(hcont.ae_eq_iff_eq volume hg.continuous).1 hfg]

/-- **Derivatives of Sobolev functions vanish at infinity.** For a continuous representative `g`
of an `L²` function in `H^s` and `s > j + dim E / 2`, the `j`-th derivative of `g` tends to zero
at infinity. -/
theorem MemSobolev.tendsto_iteratedFDeriv_cocompact_of_ae_eq {s : ℝ} {j : ℕ}
    (hs : finrank ℝ E < 2 * (s - j)) {u : Lp F 2 (volume : Measure E)}
    (hu : MemSobolev s 2 (u : 𝓢'(E, F))) {g : E → F} (hg : Continuous g)
    (hug : u =ᵐ[volume] g) :
    Tendsto (iteratedFDeriv ℝ j g) (cocompact E) (𝓝 0) := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  rw [Lp.eq_fourierInv_of_ae_eq hv hg hug, hu.iteratedFDeriv_fourierInv hs hv]
  exact (tendsto_integral_exp_inner_smul_cocompact _).congr fun w => (Real.fourier_eq _ w).symm

/-- **The quantitative Sobolev embedding `H^s ⊆ C^k`, `s > k + n / 2`.** There is a constant `C`,
depending only on `s`, `k` and `E`, such that every continuous representative `g` of an `L²`
function `u ∈ H^s` satisfies `‖D^j g(x)‖ ≤ C ‖u‖_{H^s}` for all `j ≤ k` and all `x`. -/
theorem exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace {s : ℝ} {k : ℕ}
    (hs : finrank ℝ E < 2 * (s - k)) :
    ∃ C, 0 ≤ C ∧ ∀ {u : Lp F 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, F)))
      {g : E → F}, Continuous g → u =ᵐ[volume] g →
        ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ C * ‖hu.toBesselPotentialSpace‖ := by
  set c : ℕ → ℝ := fun j =>
    (2 * π) ^ j * (eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-(s - j) / 2)) 2 volume).toReal
  have hc (j : ℕ) : 0 ≤ c j := by positivity
  refine ⟨∑ j ∈ Finset.range (k + 1), c j, Finset.sum_nonneg fun j _ => hc j,
    fun {u} hu {g} hg hug j hj x => ?_⟩
  have hsj : (finrank ℝ E : ℝ) < 2 * (s - j) := by
    have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  rw [Lp.eq_fourierInv_of_ae_eq hv hg hug]
  refine (hu.norm_iteratedFDeriv_fourierInv_le hsj hv x).trans ?_
  gcongr
  exact Finset.single_le_sum (fun i _ => hc i) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

/-- **Continuous Sobolev functions have bounded derivatives.** The derivatives of order at most
`k` of a continuous real function `f` in `H^s`, `s > dim E / 2 + k`, are bounded: those of its
complexification are, by `exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace`. -/
theorem exists_norm_iteratedFDeriv_le_of_mem_realSobolevFunctions {s : ℝ} {k : ℕ}
    (hs : finrank ℝ E + 2 * k < 2 * s) {f : E → ℝ} (hf : f ∈ realSobolevFunctions E s 2)
    (hcont : Continuous f) {n : ℕ} (hn : n ≤ k) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨u, hu, hS⟩ := mem_realSobolevFunctions.1 hf
  have hs' : (finrank ℝ E : ℝ) < 2 * (s - k) := by linarith
  set g : E → ℂ := fun x ↦ (f x : ℂ)
  have hgc : Continuous g := Complex.continuous_ofReal.comp hcont
  have hug : Complex.ofRealCLM.compLp u =ᵐ[volume] g := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u, hu] with x h₁ h₂
    rw [h₁, h₂, Complex.ofRealCLM_apply]
  have hg : ContDiff ℝ k g := hS.contDiff_of_ae_eq hs' hgc hug
  obtain ⟨C, -, hC⟩ :=
    exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace (F := ℂ) hs'
  have hfg : f = fun x ↦ Complex.reCLM (g x) := funext fun x ↦ by simp [g]
  refine ⟨‖Complex.reCLM‖ * (C * ‖hS.toBesselPotentialSpace‖), fun x ↦ ?_⟩
  rw [hfg]
  exact (Complex.reCLM.norm_iteratedFDeriv_comp_left hg.contDiffAt
    (by exact_mod_cast hn)).trans (by gcongr; exact hC hS hgc hug n hn x)

open scoped ContDiff in
/-- **Sobolev functions of every order are smooth.** A continuous representative of an `L²`
function lying in `H^s` for every real `s` is smooth. -/
theorem contDiff_of_forall_memSobolev_of_ae_eq {u : Lp F 2 (volume : Measure E)}
    (hu : ∀ s, MemSobolev s 2 (u : 𝓢'(E, F))) {g : E → F} (hg : Continuous g)
    (hug : u =ᵐ[volume] g) : ContDiff ℝ ∞ g :=
  contDiff_infty.2 fun k => (hu (k + finrank ℝ E / 2 + 1)).contDiff_of_ae_eq (by linarith) hg hug

open scoped ContDiff in
/-- **Tempered distributions in every `H^s` are smooth functions.** A tempered distribution lying
in the Bessel-potential space `H^s` for every real `s` is given by a smooth function `g`: it pairs
with every Schwartz function `φ` as `∫ φ • g`. -/
theorem exists_contDiff_eq_integral_of_forall_memSobolev {f : 𝓢'(E, F)}
    (hf : ∀ s, MemSobolev s 2 f) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ φ : 𝓢(E, ℂ), f φ = ∫ x, φ x • g x := by
  obtain ⟨u, rfl⟩ := memSobolev_zero_iff.1 (hf 0)
  obtain ⟨g, hg⟩ := (hf (finrank ℝ E / 2 + 1)).exists_zeroAtInftyContinuousMap_ae_eq (by linarith)
  refine ⟨g, contDiff_of_forall_memSobolev_of_ae_eq hf g.continuous hg, fun φ => ?_⟩
  rw [Lp.toTemperedDistribution_apply]
  exact integral_congr_ae (hg.mono fun x hx => by simp only [hx])

end TemperedDistribution

namespace TauCeti

/-- For `s > 1`, the order `s` is above half the real dimension of the plane, so `H^s(ℂ)` embeds
into the continuous functions vanishing at infinity and is an algebra. -/
theorem finrank_real_complex_lt_two_mul {s : ℝ} (hs : 1 < s) : (finrank ℝ ℂ : ℝ) < 2 * s := by
  rw [Complex.finrank_real_complex]
  push_cast
  linarith

namespace Wkp

variable {k : ℕ}

/-- If `2k > dim E`, every function in the weak-derivative Sobolev space `W^{k,2}` on the whole
space agrees almost everywhere with a continuous function vanishing at infinity. The bundled form
is `TauCeti.Wkp.toZeroAtInfty`. -/
private theorem exists_zeroAtInftyContinuousMap_ae_eq (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) ⊤ 2 k) : ∃ g : C₀(E, ℝ), value k u =ᵐ[volume] g := by
  have hvolume : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume := by simp
  set w : Lp ℝ 2 (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume (value k u)
  have hw : ∀ x, w x = value k u x := coeFn_castLpₗᵢ hvolume _
  have hS := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k w).mpr
    ⟨u, .of_forall fun x => (hw x).symm⟩
  obtain ⟨g, hg⟩ := hS.exists_zeroAtInftyContinuousMap_ae_eq (by exact_mod_cast hk)
  -- The complex representative is real almost everywhere, so its real part represents `u`.
  refine ⟨⟨⟨fun x => (g x).re, Complex.continuous_re.comp g.continuous⟩, by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp g.zero_at_infty'⟩, ?_⟩
  filter_upwards [hg, Complex.ofRealCLM.coeFn_compLp w] with x hgx hx
  rw [← hw]
  simp [← hgx, hx]

/-- Two continuous representatives of the same Sobolev function coincide. -/
private theorem eq_of_value_ae_eq {u : Wkp (volume : Measure E) ⊤ 2 k} {g g' : C₀(E, ℝ)}
    (hg : value k u =ᵐ[volume] g) (hg' : value k u =ᵐ[volume] g') : g = g' :=
  ZeroAtInftyContinuousMap.ext <| congrFun <|
    (Continuous.ae_eq_iff_eq (volume : Measure E) g.continuous g'.continuous).mp
      (hg.symm.trans hg')

/-- The continuous representative of a Sobolev function, as a linear map. -/
private def toZeroAtInftyₗ (hk : finrank ℝ E < 2 * k) :
    Wkp (volume : Measure E) ⊤ 2 k →ₗ[ℝ] C₀(E, ℝ) where
  toFun u := (exists_zeroAtInftyContinuousMap_ae_eq hk u).choose
  map_add' u v := by
    refine eq_of_value_ae_eq (u := u + v)
      (exists_zeroAtInftyContinuousMap_ae_eq hk (u + v)).choose_spec ?_
    have hadd : ⇑(value k u + value k v) =ᵐ[volume] ⇑(value k u) + ⇑(value k v) := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_add (value k u) (value k v)
    filter_upwards [(exists_zeroAtInftyContinuousMap_ae_eq hk u).choose_spec,
      (exists_zeroAtInftyContinuousMap_ae_eq hk v).choose_spec, hadd] with x hu hv hadd
    rw [value_add, hadd, Pi.add_apply, hu, hv, _root_.add_apply]
  map_smul' c u := by
    refine eq_of_value_ae_eq (u := c • u)
      (exists_zeroAtInftyContinuousMap_ae_eq hk (c • u)).choose_spec ?_
    have hsmul : ⇑(c • value k u) =ᵐ[volume] c • ⇑(value k u) := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_smul c (value k u)
    filter_upwards [(exists_zeroAtInftyContinuousMap_ae_eq hk u).choose_spec, hsmul]
      with x hu hsmul
    rw [value_smul, hsmul, Pi.smul_apply, hu, RingHom.id_apply,
      _root_.smul_apply]

private theorem value_ae_eq_toZeroAtInftyₗ (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) ⊤ 2 k) : value k u =ᵐ[volume] toZeroAtInftyₗ hk u :=
  (exists_zeroAtInftyContinuousMap_ae_eq hk u).choose_spec

/-- The graph of the continuous representative is sequentially closed: along a sequence
converging in `W^{k,2}`, the values converge almost everywhere along a subsequence, while the
representatives converge uniformly. -/
private theorem toZeroAtInftyₗ_closedGraph (hk : finrank ℝ E < 2 * k)
    (u : ℕ → Wkp (volume : Measure E) ⊤ 2 k) (w : Wkp (volume : Measure E) ⊤ 2 k)
    (g : C₀(E, ℝ))
    (hu : Tendsto u atTop (𝓝 w)) (hg : Tendsto (toZeroAtInftyₗ hk ∘ u) atTop (𝓝 g)) :
    g = toZeroAtInftyₗ hk w := by
  refine eq_of_value_ae_eq (u := w) ?_ (value_ae_eq_toZeroAtInftyₗ hk w)
  have hval : Tendsto (fun n => value k (u n)) atTop (𝓝 (value k w)) := by
    simpa only [Function.comp_def, valueL_apply] using ((valueL k).continuous.tendsto w).comp hu
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      value k (u (ns i)) x = toZeroAtInftyₗ hk (u (ns i)) x :=
    ae_all_iff.mpr fun i => value_ae_eq_toZeroAtInftyₗ hk (u (ns i))
  replace hns : ∀ᵐ x ∂(volume : Measure E),
      Tendsto (fun i => value k (u (ns i)) x) atTop (𝓝 (value k w x)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hns
  filter_upwards [hns, hrep] with x hx hxrep
  -- Convergence in `C₀` is uniform, so it implies convergence at `x`.
  have heval : Tendsto (fun i => toZeroAtInftyₗ hk (u (ns i)) x) atTop (𝓝 (g x)) :=
    (((continuous_apply x).comp (BoundedContinuousFunction.continuous_coe.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous)).tendsto g).comp
        (hg.comp hmono.tendsto_atTop)
  exact tendsto_nhds_unique (hx.congr hxrep) heval

/-- **The Sobolev embedding `W^{k,2}(ℝⁿ) →L[ℝ] C₀(ℝⁿ)`** for `2k > dim E`: the bounded linear map
sending a function in the whole-space weak-derivative Sobolev space `W^{k,2}` to its unique
representative that is continuous and vanishes at infinity. Its boundedness is the estimate
`sup_x |u(x)| ≤ C ‖u‖_{W^{k,2}}`. -/
def toZeroAtInfty (hk : finrank ℝ E < 2 * k) : Wkp (volume : Measure E) ⊤ 2 k →L[ℝ] C₀(E, ℝ) :=
  .ofSeqClosedGraph (g := toZeroAtInftyₗ hk) (toZeroAtInftyₗ_closedGraph hk)

/-- The Sobolev embedding sends a Sobolev function to a representative of its value. -/
theorem value_ae_eq_toZeroAtInfty (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) ⊤ 2 k) :
    value k u =ᵐ[volume] toZeroAtInfty hk u :=
  value_ae_eq_toZeroAtInftyₗ hk u

/-- The Sobolev embedding of `u` is the only function in `C₀` representing the value of `u`. -/
theorem toZeroAtInfty_eq_iff (hk : finrank ℝ E < 2 * k) (u : Wkp (volume : Measure E) ⊤ 2 k)
    (g : C₀(E, ℝ)) :
    toZeroAtInfty hk u = g ↔ value k u =ᵐ[volume] g :=
  ⟨fun h => h ▸ value_ae_eq_toZeroAtInfty hk u,
    fun h => eq_of_value_ae_eq (value_ae_eq_toZeroAtInfty hk u) h⟩

/-- The Sobolev embedding is injective: the continuous representative determines the Sobolev
function. -/
theorem toZeroAtInfty_injective (hk : finrank ℝ E < 2 * k) :
    Function.Injective (toZeroAtInfty (E := E) hk) := by
  intro u v huv
  apply ext k
  apply Lp.ext
  have hae : value k u =ᵐ[volume] value k v := by
    filter_upwards [value_ae_eq_toZeroAtInfty hk u, value_ae_eq_toZeroAtInfty hk v]
      with x hu hv
    rw [hu, hv, huv]
  simpa only [Opens.coe_top, Measure.restrict_univ] using hae

end Wkp

end TauCeti
