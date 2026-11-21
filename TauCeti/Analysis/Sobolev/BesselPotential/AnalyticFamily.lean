/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.ImaginaryOrder
public import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Analysis.Complex.WeaklyHolomorphic
import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# The Bessel potentials of order with nonpositive real part as an analytic family on `Lᵖ`

Let `E` be a finite-dimensional real inner product space and `1 < p < ∞`. For a complex number
`w` with `re w ≤ 0`, the Bessel potential `J^w`, the Fourier multiplier with symbol
`⟨ξ⟩ ^ w = (1 + ‖ξ‖ ^ 2) ^ (w / 2)` (`TauCeti.japaneseBracketCpow`), is bounded on
`Lᵖ = H^{0,p}` with norm at most `C (1 + ‖w‖) ^ N` by the Mihlin–Hörmander theorem
(`TauCeti.exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le`). This file shows that
these operators form an analytic family: for every `u ∈ H^{0,p}`, the map `w ↦ J^w u` is continuous
on the closed half-plane `re w ≤ 0` and holomorphic on the open half-plane `re w < 0`. With the
polynomial bound this is what Stein's interpolation theorem needs to interpolate between
Bessel-potential spaces of different orders.

## The argument

For a Schwartz function `ψ` the functions `J^w ψ` are Schwartz functions.

* *Continuity.* By the logarithmic convexity of the `Lᵖ` norms,
  `‖J^w ψ - J^{w₀} ψ‖_p ≤ ‖J^w ψ - J^{w₀} ψ‖_r ^ (1 - θ) ‖J^w ψ - J^{w₀} ψ‖_∞ ^ θ` for some
  `1 < r < p` and `0 < θ ≤ 1`. The `Lʳ` norm is bounded near `w₀` by the Mihlin bound on `Lʳ`,
  and the sup norm is at most `∫ ‖(⟨ξ⟩ ^ w - ⟨ξ⟩ ^ {w₀}) 𝓕 ψ ξ‖ dξ`, which tends to `0` by
  dominated convergence.
* *Holomorphy.* The pairing of `J^w ψ` with a test function is the pairing of the element
  `J^w ψ` of `H^0 = L²`, which depends holomorphically on `w`
  (`SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM`). These pairings
  separate the points of `H^{0,p}`, so a continuous function whose pairings are holomorphic is
  holomorphic (`TauCeti.differentiableOn_of_continuousOn_of_forall_comp`).

A general `u ∈ H^{0,p}` is a limit of Schwartz functions `ψₙ`, and the bound
`‖J^w (u - ψₙ)‖ ≤ C (1 + ‖w‖) ^ N ‖u - ψₙ‖` makes `J^w ψₙ → J^w u` locally uniformly in `w`, so
continuity and holomorphy pass to the limit.

## Main declarations

* `BesselPotentialSpace.besselPotentialNonposCLM`: `J^w` as a bounded operator on `H^{0,p}` for
  `re w ≤ 0`, with `BesselPotentialSpace.toDistr_besselPotentialNonposCLM` and the bound
  `BesselPotentialSpace.exists_norm_besselPotentialNonposCLM_le`.
* `SchwartzMap.continuousOn_toBesselPotentialSpaceCLM_besselPotentialCLM`,
  `SchwartzMap.differentiableOn_toBesselPotentialSpaceCLM_besselPotentialCLM`: the same two
  statements for Schwartz functions, proved first.
* `BesselPotentialSpace.continuousOn_besselPotentialNonposCLM_apply`: `w ↦ J^w u` is continuous on
  `re w ≤ 0`.
* `BesselPotentialSpace.differentiableOn_besselPotentialNonposCLM_apply`: `w ↦ J^w u` is
  holomorphic on `re w < 0`.

## References

* E. M. Stein, *Interpolation of linear operators*, Trans. Amer. Math. Soc. 83 (1956), 482–492.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, §6.4.
-/

public section

noncomputable section

open MeasureTheory Module TemperedDistribution Set Filter Topology
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BesselPotentialSpace

/-- For `re w ≤ 0` the Bessel potential `J^w` maps `H^{0,p}` into itself, `1 < p < ∞`. -/
theorem memSobolev_zero_fourierMultiplierCLM_japaneseBracketCpow (hp : 1 < p) (hp_top : p ≠ ∞)
    {w : ℂ} (hw : w.re ≤ 0) (u : H^{0, p}(E, F)) :
    (fourierMultiplierCLM F (TauCeti.japaneseBracketCpow w) u.toDistr).MemSobolev 0 p :=
  (u.memSobolev_toDistr.fourierMultiplierCLM_japaneseBracketCpow hp hp_top w).of_le (by linarith)

open scoped Classical in
/-- **The Bessel potential of order with nonpositive real part on `Lᵖ`.** For `1 < p < ∞` and
`re w ≤ 0`, the Fourier multiplier `J^w` with symbol `⟨ξ⟩ ^ w` as a bounded operator on
`H^{0,p}(E, F) = Lᵖ(E, F)`. For `re w > 0` it does not preserve `H^{0,p}`, and the operator is
defined to be `0`. -/
def besselPotentialNonposCLM (hp : 1 < p) (hp_top : p ≠ ∞) (w : ℂ) :
    H^{0, p}(E, F) →L[ℂ] H^{0, p}(E, F) :=
  if hw : w.re ≤ 0 then
    mapCLM (fourierMultiplierCLM F (TauCeti.japaneseBracketCpow w))
      (memSobolev_zero_fourierMultiplierCLM_japaneseBracketCpow hp hp_top hw)
  else 0

variable {hp : 1 < p} {hp_top : p ≠ ∞}

/-- For `re w ≤ 0`, `besselPotentialNonposCLM hp hp_top w` acts on the underlying tempered
distributions as the Fourier multiplier with symbol `⟨ξ⟩ ^ w`. -/
theorem toDistr_besselPotentialNonposCLM {w : ℂ} (hw : w.re ≤ 0) (u : H^{0, p}(E, F)) :
    (besselPotentialNonposCLM hp hp_top w u).toDistr =
      fourierMultiplierCLM F (TauCeti.japaneseBracketCpow w) u.toDistr := by
  simp only [besselPotentialNonposCLM, hw, ↓reduceDIte]
  exact toDistr_mapCLM _ _ u

/-- On Schwartz functions, `besselPotentialNonposCLM hp hp_top w` is the Bessel potential
`SchwartzMap.besselPotentialCLM w` of complex order. -/
theorem besselPotentialNonposCLM_toBesselPotentialSpaceCLM {w : ℂ} (hw : w.re ≤ 0)
    (ψ : 𝓢(E, F)) :
    besselPotentialNonposCLM hp hp_top w (SchwartzMap.toBesselPotentialSpaceCLM 0 p ψ) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 p (SchwartzMap.besselPotentialCLM w ψ) := by
  ext1
  rw [toDistr_besselPotentialNonposCLM hw, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.besselPotentialCLM_def,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq
      (TauCeti.hasTemperateGrowth_japaneseBracketCpow w)]

variable (hp hp_top) in
/-- **The norm of `J^w` on `Lᵖ` grows polynomially in the order.** For `1 < p < ∞` there is a
constant `C` such that `‖J^w‖_{Lᵖ → Lᵖ} ≤ C (1 + ‖w‖) ^ N` for `re w ≤ 0`,
`N = ⌊dim E / 2⌋ + 1`. -/
theorem exists_norm_besselPotentialNonposCLM_le :
    ∃ C : ℝ≥0, ∀ w : ℂ, w.re ≤ 0 →
      ‖(besselPotentialNonposCLM hp hp_top w : H^{0, p}(E, F) →L[ℂ] H^{0, p}(E, F))‖ ≤
        C * (1 + ‖w‖) ^ (finrank ℝ E / 2 + 1) := by
  obtain ⟨C, hC⟩ :=
    TauCeti.exists_fourierMultiplierCLM_japaneseBracketCpow_eq_and_norm_le (E := E) (F := F) hp
      hp_top
  refine ⟨C, fun w hw ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_⟩
  obtain ⟨g, hg, hgu⟩ := hC w hw u.toLp
  -- The `Lᵖ` function of `J^w u` is the `Lᵖ` function `g` given by the Mihlin bound.
  have hv : (besselPotentialNonposCLM hp hp_top w u).toLp = g := by
    refine Lp.toTemperedDistribution_injective ?_
    beta_reduce
    rw [toTemperedDistribution_toLp_zero, toDistr_besselPotentialNonposCLM hw,
      ← toTemperedDistribution_toLp_zero, hg]
  rw [← norm_toLp_eq, hv, ← norm_toLp_eq u]
  exact hgu

/-! ### Schwartz functions -/

section Schwartz

variable (ψ : 𝓢(E, F))

omit [CompleteSpace F] in
/-- The sup norm of `J^w ψ - J^{w₀} ψ` is at most `∫ ‖(⟨ξ⟩ ^ w - ⟨ξ⟩ ^ {w₀}) 𝓕 ψ ξ‖ dξ`. -/
private theorem norm_besselPotentialCLM_sub_apply_le (w w₀ : ℂ) (x : E) :
    ‖(SchwartzMap.besselPotentialCLM w ψ - SchwartzMap.besselPotentialCLM w₀ ψ) x‖ ≤
      ∫ ξ, ‖(TauCeti.japaneseBracketCpow w ξ - TauCeti.japaneseBracketCpow w₀ ξ) • 𝓕 ψ ξ‖ := by
  have h : SchwartzMap.besselPotentialCLM w ψ - SchwartzMap.besselPotentialCLM w₀ ψ =
      𝓕⁻ (SchwartzMap.smulLeftCLM F (TauCeti.japaneseBracketCpow w) (𝓕 ψ) -
        SchwartzMap.smulLeftCLM F (TauCeti.japaneseBracketCpow w₀) (𝓕 ψ)) := by
    rw [SchwartzMap.besselPotentialCLM_def, SchwartzMap.besselPotentialCLM_def,
      SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierMultiplierCLM_apply,
      FourierTransform.fourierInv_sub]
  rw [h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  refine (Real.norm_fourier_le_integral_norm _ _).trans_eq
    (integral_congr_ae (.of_forall fun ξ ↦ ?_))
  simp [SchwartzMap.smulLeftCLM_apply_apply (TauCeti.hasTemperateGrowth_japaneseBracketCpow w),
    SchwartzMap.smulLeftCLM_apply_apply (TauCeti.hasTemperateGrowth_japaneseBracketCpow w₀),
    sub_smul]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖⟨ξ⟩ ^ z‖ ≤ 1` for `re z ≤ 0`. -/
private theorem norm_japaneseBracketCpow_le_one {z : ℂ} (hz : z.re ≤ 0) (ξ : E) :
    ‖TauCeti.japaneseBracketCpow z ξ‖ ≤ 1 := by
  rw [TauCeti.norm_japaneseBracketCpow]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg ξ]) (by linarith)

omit [CompleteSpace F] in
/-- `∫ ‖(⟨ξ⟩ ^ w - ⟨ξ⟩ ^ {w₀}) 𝓕 ψ ξ‖ dξ` tends to `0` as `w → w₀` with `re w ≤ 0`. -/
private theorem tendsto_integral_norm_japaneseBracketCpow_sub_smul {w₀ : ℂ} (hw₀ : w₀.re ≤ 0) :
    Tendsto (fun w ↦ ∫ ξ, ‖(TauCeti.japaneseBracketCpow w ξ -
      TauCeti.japaneseBracketCpow w₀ ξ) • 𝓕 ψ ξ‖) (𝓝[{w | w.re ≤ 0}] w₀) (𝓝 0) := by
  have hcont (ξ : E) : Continuous fun w : ℂ ↦ TauCeti.japaneseBracketCpow w ξ :=
    continuous_iff_continuousAt.2 fun z ↦ (TauCeti.hasDerivAt_japaneseBracketCpow z ξ).continuousAt
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[{w : ℂ | w.re ≤ 0}] w₀)
    (μ := volume) (F := fun (w : ℂ) (ξ : E) ↦ ‖(TauCeti.japaneseBracketCpow w ξ -
      TauCeti.japaneseBracketCpow w₀ ξ) • 𝓕 ψ ξ‖)
    (f := fun ξ ↦ ‖(TauCeti.japaneseBracketCpow w₀ ξ - TauCeti.japaneseBracketCpow w₀ ξ) •
      𝓕 ψ ξ‖) (fun ξ ↦ 2 * ‖𝓕 ψ ξ‖)
    (.of_forall fun w ↦ ?_) ?_ ((𝓕 ψ).integrable.norm.const_mul 2) (.of_forall fun ξ ↦ ?_)
  · simpa using h
  · exact ((((TauCeti.contDiff_japaneseBracketCpow (n := 0) w).continuous.sub
      (TauCeti.contDiff_japaneseBracketCpow (n := 0) w₀).continuous).smul
        (𝓕 ψ).continuous).norm).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with w hw
    refine .of_forall fun ξ ↦ ?_
    rw [norm_norm, norm_smul]
    gcongr
    linarith [norm_sub_le (TauCeti.japaneseBracketCpow w ξ) (TauCeti.japaneseBracketCpow w₀ ξ),
      norm_japaneseBracketCpow_le_one (hw : w.re ≤ 0) ξ,
      norm_japaneseBracketCpow_le_one hw₀ ξ]
  · exact ((((hcont ξ).sub continuous_const).smul continuous_const).norm.tendsto' w₀ _
      (by simp)).mono_left nhdsWithin_le_nhds

/-- The Mihlin bound for Schwartz functions: for `re w ≤ 0`,
`‖J^w ψ‖_p ≤ C (1 + ‖w‖) ^ N ‖ψ‖_p`. -/
private theorem exists_eLpNorm_besselPotentialCLM_le (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ w : ℂ, w.re ≤ 0 → ∀ ψ : 𝓢(E, F),
      (eLpNorm (SchwartzMap.besselPotentialCLM w ψ) p volume).toReal ≤
        C * (1 + ‖w‖) ^ (finrank ℝ E / 2 + 1) * (eLpNorm ψ p volume).toReal := by
  obtain ⟨C, hC⟩ := exists_norm_besselPotentialNonposCLM_le (E := E) (F := F) hp hp_top
  refine ⟨C, fun w hw ψ ↦ ?_⟩
  rw [← SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    ← SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    ← besselPotentialNonposCLM_toBesselPotentialSpaceCLM (hp := hp) (hp_top := hp_top) hw]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hC w hw)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
  [Fact (1 ≤ p)] in
/-- An exponent strictly between `r` and `∞` is an interpolated exponent:
`1 / p = (1 - θ) / r + θ / ∞` for some `0 < θ ≤ 1`. -/
private theorem exists_inv_eq_ofReal_mul_inv_add {r : ℝ≥0∞} (hr₁ : 1 < r) (hrp : r < p)
    (hp_top : p ≠ ∞) : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      p⁻¹ = ENNReal.ofReal (1 - θ) * r⁻¹ + ENNReal.ofReal θ * ∞⁻¹ := by
  have hr_top : r ≠ ∞ := (hrp.trans_le le_top).ne
  have hr₀ : r ≠ 0 := (zero_lt_one.trans hr₁).ne'
  have hrp' : r.toReal < p.toReal := (ENNReal.toReal_lt_toReal hr_top hp_top).2 hrp
  have hr0' : 0 < r.toReal := ENNReal.toReal_pos hr₀ hr_top
  refine ⟨1 - r.toReal / p.toReal, ?_, ?_, ?_⟩
  · rw [sub_pos, div_lt_one (hr0'.trans hrp')]
    exact hrp'
  · rw [sub_le_self_iff]
    positivity
  · rw [ENNReal.inv_top, mul_zero, add_zero, sub_sub_cancel,
      ENNReal.ofReal_div_of_pos (hr0'.trans hrp'), ENNReal.ofReal_toReal hr_top,
      ENNReal.ofReal_toReal hp_top, div_eq_mul_inv, mul_comm r, mul_assoc,
      ENNReal.mul_inv_cancel hr₀ hr_top, mul_one]

omit [CompleteSpace F] [Fact (1 ≤ p)] in
/-- The interpolation step: a Schwartz function `g` with `‖g‖_r ≤ M` and `‖g‖_∞ ≤ I` has
`‖g‖_p ≤ M ^ (1 - θ) I ^ θ` when `1 / p = (1 - θ) / r + θ / ∞`. -/
private theorem toReal_eLpNorm_le_rpow_mul_rpow (g : 𝓢(E, F)) {r : ℝ≥0∞} {θ : ℝ} (hθ₀ : 0 < θ)
    (hθ₁ : θ ≤ 1) (hpθ : p⁻¹ = ENNReal.ofReal (1 - θ) * r⁻¹ + ENNReal.ofReal θ * ∞⁻¹) {M I : ℝ}
    (hM : 0 ≤ M) (hI : 0 ≤ I) (hgr : (eLpNorm g r volume).toReal ≤ M) (hg : ∀ x, ‖g x‖ ≤ I) :
    (eLpNorm g p volume).toReal ≤ M ^ (1 - θ) * I ^ θ := by
  have hgtop : eLpNorm g ∞ volume ≤ ENNReal.ofReal I := by
    rw [eLpNorm_exponent_top g.continuous.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (.of_forall hg)
  have hlog := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (μ := volume) (f := ⇑g) ⟨hθ₀.le, hθ₁⟩ hpθ
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hlog.trans ?_)
  rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hM (by linarith),
    ← ENNReal.ofReal_rpow_of_nonneg hI hθ₀.le]
  gcongr
  exact (ENNReal.le_ofReal_iff_toReal_le (SchwartzMap.eLpNorm_lt_top g r volume).ne hM).2 hgr

omit [CompleteSpace F] [Fact (1 ≤ p)] in
/-- Near `w₀`, the `Lʳ` norms of `J^w ψ - J^{w₀} ψ` are bounded, by the Mihlin bound on `Lʳ`. -/
private theorem toReal_eLpNorm_besselPotentialCLM_sub_le {r : ℝ≥0∞} (hr : 1 ≤ r) {C : ℝ≥0}
    (hC : ∀ w : ℂ, w.re ≤ 0 → ∀ ψ : 𝓢(E, F),
      (eLpNorm (SchwartzMap.besselPotentialCLM w ψ) r volume).toReal ≤
        C * (1 + ‖w‖) ^ (finrank ℝ E / 2 + 1) * (eLpNorm ψ r volume).toReal)
    {w w₀ : ℂ} (hw : w.re ≤ 0) (hw₀ : w₀.re ≤ 0) (hw₁ : w ∈ Metric.closedBall w₀ 1) :
    (eLpNorm ⇑(SchwartzMap.besselPotentialCLM w ψ - SchwartzMap.besselPotentialCLM w₀ ψ) r
      volume).toReal ≤
      C * (2 + ‖w₀‖) ^ (finrank ℝ E / 2 + 1) * (eLpNorm ψ r volume).toReal +
        C * (1 + ‖w₀‖) ^ (finrank ℝ E / 2 + 1) * (eLpNorm ψ r volume).toReal := by
  have h₁ : ‖w‖ ≤ 1 + ‖w₀‖ := by
    have := norm_le_norm_add_norm_sub' w w₀
    rw [Metric.mem_closedBall, dist_eq_norm] at hw₁
    linarith
  have hsub := eLpNorm_sub_le (μ := volume) (p := r)
    (f := ⇑(SchwartzMap.besselPotentialCLM w ψ))
    (g := ⇑(SchwartzMap.besselPotentialCLM w₀ ψ)) hr
  have hcoe : (⇑(SchwartzMap.besselPotentialCLM w ψ - SchwartzMap.besselPotentialCLM w₀ ψ) :
      E → F) = ⇑(SchwartzMap.besselPotentialCLM w ψ) -
        ⇑(SchwartzMap.besselPotentialCLM w₀ ψ) := (rfl)
  rw [hcoe]
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2
    ⟨(SchwartzMap.eLpNorm_lt_top _ _ volume).ne, (SchwartzMap.eLpNorm_lt_top _ _ volume).ne⟩)
      hsub).trans ?_
  rw [ENNReal.toReal_add (SchwartzMap.eLpNorm_lt_top _ _ volume).ne
    (SchwartzMap.eLpNorm_lt_top _ _ volume).ne]
  refine add_le_add ((hC w hw ψ).trans ?_) (hC w₀ hw₀ ψ)
  have h₂ : 1 + ‖w‖ ≤ 2 + ‖w₀‖ := by linarith
  gcongr ?_ * _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h₂ _) C.coe_nonneg

/-- For a Schwartz function `ψ`, the map `w ↦ J^w ψ` into `H^{0,p}` is continuous on the closed
half-plane `re w ≤ 0`, `1 < p < ∞`. -/
theorem _root_.SchwartzMap.continuousOn_toBesselPotentialSpaceCLM_besselPotentialCLM (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ContinuousOn (fun w ↦ SchwartzMap.toBesselPotentialSpaceCLM 0 p
      (SchwartzMap.besselPotentialCLM w ψ)) {w | w.re ≤ 0} := by
  intro w₀ hw₀
  replace hw₀ : w₀.re ≤ 0 := hw₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [← map_sub, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero]
  -- Interpolate the `Lᵖ` norm between an `Lʳ` norm, `1 < r < p`, and the sup norm.
  obtain ⟨r, hr₁, hrp⟩ := exists_between hp
  have : Fact (1 ≤ r) := ⟨hr₁.le⟩
  have hr_top : r ≠ ∞ := (hrp.trans_le le_top).ne
  obtain ⟨θ, hθ₀, hθ₁, hpθ⟩ := exists_inv_eq_ofReal_mul_inv_add hr₁ hrp hp_top
  obtain ⟨C, hC⟩ := exists_eLpNorm_besselPotentialCLM_le (E := E) (F := F) hr₁ hr_top
  set N := finrank ℝ E / 2 + 1
  -- A bound on the `Lʳ` norms near `w₀`.
  set M : ℝ := C * (2 + ‖w₀‖) ^ N * (eLpNorm ψ r volume).toReal +
    C * (1 + ‖w₀‖) ^ N * (eLpNorm ψ r volume).toReal
  set I : ℂ → ℝ := fun w ↦ ∫ ξ, ‖(TauCeti.japaneseBracketCpow w ξ -
    TauCeti.japaneseBracketCpow w₀ ξ) • 𝓕 ψ ξ‖
  have hbound : ∀ᶠ w in 𝓝[{w | w.re ≤ 0}] w₀,
      (eLpNorm (⇑(SchwartzMap.besselPotentialCLM w ψ - SchwartzMap.besselPotentialCLM w₀ ψ))
        p volume).toReal ≤ M ^ (1 - θ) * I w ^ θ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds w₀
      zero_lt_one)] with w hw hw₁
    replace hw : w.re ≤ 0 := hw
    set g := SchwartzMap.besselPotentialCLM w ψ - SchwartzMap.besselPotentialCLM w₀ ψ
    have hgr : (eLpNorm g r volume).toReal ≤ M :=
      toReal_eLpNorm_besselPotentialCLM_sub_le ψ hr₁.le hC hw hw₀ hw₁
    exact toReal_eLpNorm_le_rpow_mul_rpow g hθ₀ hθ₁ hpθ (by positivity)
      (integral_nonneg fun _ ↦ norm_nonneg _) hgr (norm_besselPotentialCLM_sub_apply_le ψ w w₀)
  refine squeeze_zero' (.of_forall fun _ ↦ ENNReal.toReal_nonneg) hbound ?_
  have hlim := ((tendsto_integral_norm_japaneseBracketCpow_sub_smul ψ hw₀).rpow_const
    (Or.inr hθ₀.le)).const_mul (M ^ (1 - θ))
  simpa [Real.zero_rpow hθ₀.ne'] using hlim

/-- The pairing `u ↦ u φ` of the tempered distributions with a test function `φ`. -/
private def evalCLM (φ : 𝓢(E, ℂ)) : 𝓢'(E, F) →L[ℂ] F :=
  ⟨⟨⟨fun T ↦ T φ, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩, continuous_eval_const φ⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem evalCLM_apply (φ : 𝓢(E, ℂ)) (T : 𝓢'(E, F)) : evalCLM φ T = T φ := (rfl)

/-- For a Schwartz function `ψ`, the map `w ↦ J^w ψ` into `H^{0,p}` is holomorphic on the open
half-plane `re w < 0`, `1 < p < ∞`. -/
theorem _root_.SchwartzMap.differentiableOn_toBesselPotentialSpaceCLM_besselPotentialCLM
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    DifferentiableOn ℂ (fun w ↦ SchwartzMap.toBesselPotentialSpaceCLM 0 p
      (SchwartzMap.besselPotentialCLM w ψ)) {w | w.re < 0} := by
  refine TauCeti.differentiableOn_of_continuousOn_of_forall_comp
    (fun φ : 𝓢(E, ℂ) ↦ evalCLM φ ∘L toDistrCLM E F 0 p) (fun u hu ↦ ?_)
    ((SchwartzMap.continuousOn_toBesselPotentialSpaceCLM_besselPotentialCLM ψ hp hp_top).mono
      fun w (hw : w.re < 0) ↦ (hw.le : w.re ≤ 0)) (fun φ ↦ ?_)
    (isOpen_lt Complex.continuous_re continuous_const)
  · ext1
    ext φ
    simpa [evalCLM_apply, toDistrCLM_apply] using hu φ
  · -- The pairing only sees the tempered distribution `J^w ψ`, which is also an element of
    -- `H^0 = L²` depending holomorphically on `w`.
    have h : (fun w ↦ (evalCLM φ ∘L toDistrCLM E F 0 p) (SchwartzMap.toBesselPotentialSpaceCLM 0 p
        (SchwartzMap.besselPotentialCLM w ψ))) = fun w ↦ (evalCLM φ ∘L toDistrCLM E F 0 2)
          (SchwartzMap.toBesselPotentialSpaceCLM 0 2 (SchwartzMap.besselPotentialCLM w ψ)) := by
      funext w
      simp [toDistrCLM_apply, SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
    rw [h]
    exact fun w _ ↦ ((evalCLM φ ∘L toDistrCLM E F 0 2).hasFDerivAt.comp_hasDerivAt w
      (SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM 0 ψ w)
        ).differentiableAt.differentiableWithinAt

end Schwartz

/-! ### General elements of `Lᵖ` -/

/-- `J^w` applied to Schwartz approximations of `u` converges to `J^w u` locally uniformly on the
closed half-plane `re w ≤ 0`. -/
private theorem exists_tendstoLocallyUniformlyOn (u : H^{0, p}(E, F)) :
    ∃ ψ : ℕ → 𝓢(E, F), TendstoLocallyUniformlyOn
      (fun n w ↦ besselPotentialNonposCLM hp hp_top w (SchwartzMap.toBesselPotentialSpaceCLM 0 p
        (ψ n))) (fun w ↦ besselPotentialNonposCLM hp hp_top w u) atTop {w | w.re ≤ 0} := by
  obtain ⟨C, hC⟩ := exists_norm_besselPotentialNonposCLM_le (E := E) (F := F) hp hp_top
  choose ψ hψ using fun n : ℕ ↦ (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (E := E)
    (F := F) 0 hp_top).exists_dist_lt u (Nat.one_div_pos_of_nat (n := n))
  refine ⟨ψ, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε w₀ _ ↦ ?_⟩
  set N := finrank ℝ E / 2 + 1
  set B : ℝ := C * (2 + ‖w₀‖) ^ N + 1
  have hB : 0 < B := by positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (div_pos hε hB)
  refine ⟨{w | w.re ≤ 0} ∩ Metric.closedBall w₀ 1,
    inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds w₀ zero_lt_one), ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn w hw
  rw [dist_eq_norm, ← map_sub]
  have hw₁ : ‖w‖ ≤ 1 + ‖w₀‖ := by
    have := norm_le_norm_add_norm_sub' w w₀
    have h := hw.2
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    linarith
  have hun : ‖u - SchwartzMap.toBesselPotentialSpaceCLM 0 p (ψ n)‖ < ε / B := by
    rw [← dist_eq_norm]
    refine (hψ n).trans (lt_of_le_of_lt ?_ hn₀)
    gcongr
  calc ‖besselPotentialNonposCLM hp hp_top w (u - SchwartzMap.toBesselPotentialSpaceCLM 0 p (ψ n))‖
      ≤ C * (1 + ‖w‖) ^ N * ‖u - SchwartzMap.toBesselPotentialSpaceCLM 0 p (ψ n)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hC w hw.1)
    _ ≤ B * ‖u - SchwartzMap.toBesselPotentialSpaceCLM 0 p (ψ n)‖ := by
        gcongr
        have : (1 + ‖w‖) ^ N ≤ (2 + ‖w₀‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        nlinarith [C.coe_nonneg]
    _ < B * (ε / B) := by gcongr
    _ = ε := mul_div_cancel₀ ε hB.ne'

/-- **Continuity of the analytic family.** For `1 < p < ∞` and `u ∈ H^{0,p}`, the map
`w ↦ J^w u` is continuous on the closed half-plane `re w ≤ 0`. -/
theorem continuousOn_besselPotentialNonposCLM_apply (u : H^{0, p}(E, F)) :
    ContinuousOn (fun w ↦ besselPotentialNonposCLM hp hp_top w u) {w | w.re ≤ 0} := by
  obtain ⟨ψ, hψ⟩ := exists_tendstoLocallyUniformlyOn (hp := hp) (hp_top := hp_top) u
  refine hψ.continuousOn (.of_forall fun n ↦ ?_)
  exact (SchwartzMap.continuousOn_toBesselPotentialSpaceCLM_besselPotentialCLM (ψ n) hp
    hp_top).congr
    fun w hw ↦ besselPotentialNonposCLM_toBesselPotentialSpaceCLM hw (ψ n)

/-- **Holomorphy of the analytic family.** For `1 < p < ∞` and `u ∈ H^{0,p}`, the map
`w ↦ J^w u` is holomorphic on the open half-plane `re w < 0`. -/
theorem differentiableOn_besselPotentialNonposCLM_apply (u : H^{0, p}(E, F)) :
    DifferentiableOn ℂ (fun w ↦ besselPotentialNonposCLM hp hp_top w u) {w | w.re < 0} := by
  obtain ⟨ψ, hψ⟩ := exists_tendstoLocallyUniformlyOn (hp := hp) (hp_top := hp_top) u
  refine TendstoLocallyUniformlyOn.differentiableOn
    (TendstoLocallyUniformlyOn.mono hψ fun w (hw : w.re < 0) ↦ (hw.le : w.re ≤ 0))
    (.of_forall fun n ↦ ?_) (isOpen_lt Complex.continuous_re continuous_const)
  exact (SchwartzMap.differentiableOn_toBesselPotentialSpaceCLM_besselPotentialCLM (ψ n) hp
    hp_top).congr
    fun w (hw : w.re < 0) ↦ besselPotentialNonposCLM_toBesselPotentialSpaceCLM hw.le (ψ n)

end BesselPotentialSpace
