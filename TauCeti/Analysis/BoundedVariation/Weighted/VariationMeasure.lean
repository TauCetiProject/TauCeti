/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weighted variation is the weighted variation measure

Let `W : E → ℝ` be a weight of class `C¹` and `u` a function of locally bounded variation on an
open set `Ω`: locally integrable on `Ω`, with every compact subset of `Ω` having an open
neighbourhood of finite Euclidean variation. Then the weighted variation is the integral of the
density `e^{−W}` against the variation measure `|Du|`:

`V_μ(u; Ω) = ∫_Ω e^{−W} d|Du|`.

Applied to the open subsets of `Ω`, this says that `U ↦ V_μ(u; U)` is the restriction to open sets
of the Borel measure `e^{−W} |Du|` on `Ω`. This is the form in which the weighted perimeter is
computed from De Giorgi's structure theorem, and in which the weighted Gauss–Green and coarea
formulas are derived from their Euclidean counterparts.

The pairing of `u` with the weighted divergence of a test vector field `X` is
`-∫ e^{−W} ⟪X, σ_u⟫ d|Du|`, by the polar decomposition `Du = σ_u |Du|` applied to the `C¹` field
`e^{−W} X` (`TauCeti.integral_weightedDivergence_mul_eq_neg_integral_inner_polarDensity`); since
`‖σ_u‖ = 1`, it is at most `∫ e^{−W} d|Du|`. Conversely, on an open set `U` with compact closure in
`Ω` the weight is at most some `M`, and a test field `X` supported in `U` with
`∫ ⟪X, -σ_u⟫ d|Du| ≥ |Du|(U) − δ` has `∫_U e^{−W} (1 − ⟪X, -σ_u⟫) d|Du| ≤ M δ`, because the
integrand is nonnegative. Exhausting `Ω` by compact sets gives the reverse inequality.

## Main declarations

* `TauCeti.integral_weightedDivergence_mul_eq_neg_integral_inner_polarDensity`: the weighted
  pairing `∫ u div_μ X dμ` is `-∫ e^{−W} ⟪X, σ_u⟫ d|Du|`.
* `TauCeti.weightedVariation_eq_lintegral_variationMeasure`: `V_μ(u; Ω) = ∫_Ω e^{−W} d|Du|`.
* `TauCeti.weightedVariation_eq_setLIntegral_variationMeasure`: for an open `U ⊆ Ω`,
  `V_μ(u; U) = ∫_U e^{−W} d|Du|`, with `|Du|` the variation measure on `Ω`.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Section 3.
* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011), equations (2.3)–(2.5).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §1.4 (polar decomposition) and §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set
open scoped ENNReal Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E} {u : E → ℝ}

variable (hW : ContDiff ℝ 1 W) (hu : LocallyIntegrableOn u Ω)
  (hfin : ∀ K, IsCompact K → K ⊆ Ω →
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U u ≠ ∞)
include hW hu hfin

/-- **The weighted pairing against the polar decomposition.** For a `C¹` weight and `u`
locally integrable on `Ω` with locally finite variation, the pairing `∫ u div_μ X dμ` of `u` with
the weighted divergence of a test vector field `X` is `-∫ e^{−W} ⟪X, σ_u⟫ d|Du|`. -/
theorem integral_weightedDivergence_mul_eq_neg_integral_inner_polarDensity (X : 𝓓(Ω, E)) :
    ∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x =
      -∫ x, Real.exp (-W x) * ⟪X x, polarDensity volume Ω u x⟫ ∂variationMeasure volume Ω u := by
  have hY : ContDiff ℝ 1 fun y => Real.exp (-W y) • X y :=
    hW.neg.exp.smul (X.contDiff.of_le (by simp))
  have h := integral_trace_fderiv_mul_eq_neg_integral_inner_polarDensity hu hfin hY
    X.hasCompactSupport.smul_left ((tsupport_smul_subset_right _ _).trans X.tsupport_subset)
  simp only [trace_fderiv_exp_neg_smul (hW.differentiable one_ne_zero _)
    ((X.contDiff.differentiable (by simp)) _), real_inner_smul_left] at h
  simpa only [divergenceCLM_apply] using h

omit [FiniteDimensional ℝ E] hu hfin in
/-- `e^{−W}` is integrable on a set of finite measure in `Ω` on which it is bounded. -/
private theorem integrableOn_exp_neg {ν : Measure Ω} {U' : Set Ω} (hU' : MeasurableSet U')
    (hνU : ν U' ≠ ∞) {M : ℝ} (hgU : ∀ x ∈ U', Real.exp (-W x) ≤ M) :
    IntegrableOn (fun x : Ω => Real.exp (-W x)) U' ν :=
  Measure.integrableOn_of_bounded hνU
    (hW.continuous.neg.rexp.comp continuous_subtypeVal).aestronglyMeasurable (M := M)
    ((ae_restrict_iff' hU').2 (ae_of_all _ fun x hx => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hgU x hx))

/-- The defect estimate behind the lower bound. Let `X` be a test vector field of norm at most one
vanishing outside a set `U'` of finite `|Du|`-measure on which `e^{−W} ≤ M`. Then
`∫_{U'} e^{−W} d|Du|` exceeds the weighted pairing of `u` with `X` by at most `M` times the
defect `|Du|(U') - ∫ u div X`. -/
private theorem setIntegral_exp_neg_le (X : 𝓓(Ω, E)) (hX : ∀ x, ‖X x‖ ≤ 1) {U' : Set Ω}
    (hU' : MeasurableSet U') (hνU : variationMeasure volume Ω u U' ≠ ∞)
    (hXU : ∀ x ∉ U', X x = 0) {M : ℝ} (hgU : ∀ x ∈ U', Real.exp (-W x) ≤ M) :
    ∫ x in U', Real.exp (-W x) ∂variationMeasure volume Ω u ≤
      (∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x) +
        M * ((variationMeasure volume Ω u).real U' - ∫ x, divergenceCLM X x * u x) := by
  set ν := variationMeasure volume Ω u
  set σ := polarDensity volume Ω u
  set g : E → ℝ := fun x => Real.exp (-W x)
  have hg : Continuous g := hW.continuous.neg.rexp
  rw [integral_weightedDivergence_mul_eq_neg_integral_inner_polarDensity hW hu hfin,
    integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin]
  -- Integrability of the integrands against `|Du|` restricted to `U'`.
  have hiX : Integrable (fun x : Ω => ⟪X x, σ x⟫) ν :=
    integrable_inner_polarDensity X.continuous X.hasCompactSupport X.tsupport_subset
  have hiGX : Integrable (fun x : Ω => g x * ⟪X x, σ x⟫) ν := by
    simpa only [real_inner_smul_left] using integrable_inner_polarDensity (μ := volume) (u := u)
      (f := fun x => g x • X x) (hg.smul X.continuous) X.hasCompactSupport.smul_left
      ((tsupport_smul_subset_right _ _).trans X.tsupport_subset)
  have hig : IntegrableOn (fun x : Ω => g x) U' ν := integrableOn_exp_neg hW hU' hνU hgU
  have hi1 : IntegrableOn (fun _ : Ω => (1 : ℝ)) U' ν := integrableOn_const hνU
  -- Both pairings only see `U'`.
  have hzero (f : Ω → ℝ) (hf : ∀ x : Ω, X x = 0 → f x = 0) : ∫ x in U', f x ∂ν = ∫ x, f x ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf x (hXU x hx)
  have h1 := hzero (fun x => ⟪X x, σ x⟫) fun x hx => by simp [hx]
  have h2 := hzero (fun x => g x * ⟪X x, σ x⟫) fun x hx => by simp [hx]
  -- Since `‖σ_u‖ = 1`, the factor `1 + ⟪X, σ_u⟫` is nonnegative, so `g ≤ M` may be inserted.
  have hinner : ∀ᵐ x : Ω ∂ν, -1 ≤ ⟪X x, σ x⟫ := by
    filter_upwards [ae_norm_polarDensity_eq_one hu hfin] with x hx
    have := abs_real_inner_le_norm (X x) (σ x)
    rw [hx, mul_one] at this
    exact (abs_le.1 (this.trans (hX x))).1
  have hle : ∫ x in U', g x * (1 + ⟪X x, σ x⟫) ∂ν ≤ ∫ x in U', M * (1 + ⟪X x, σ x⟫) ∂ν := by
    refine setIntegral_mono_on_ae ((hig.add hiGX.integrableOn).congr
      (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring))
      ((hi1.add hiX.integrableOn).const_mul M) hU' ?_
    filter_upwards [hinner] with x hx hxU
    exact mul_le_mul_of_nonneg_right (hgU x hxU) (by linarith)
  have hL : ∫ x in U', g x * (1 + ⟪X x, σ x⟫) ∂ν =
      ∫ x in U', g x ∂ν + ∫ x, g x * ⟪X x, σ x⟫ ∂ν := by
    rw [← h2, ← integral_add hig hiGX.integrableOn]
    congr 1 with x
    ring
  have hR : ∫ x in U', M * (1 + ⟪X x, σ x⟫) ∂ν = M * (ν.real U' + ∫ x, ⟪X x, σ x⟫ ∂ν) := by
    rw [integral_const_mul, integral_add hi1 hiX.integrableOn, setIntegral_const, h1,
      smul_eq_mul, mul_one]
  rw [sub_neg_eq_add]
  linarith

/-- On a compact subset of `Ω`, the integral of `e^{−W}` against `|Du|` is at most the weighted
variation. -/
private theorem setLIntegral_le_weightedVariation {C : Set Ω} (hC : IsCompact C) :
    ∫⁻ x in C, ENNReal.ofReal (Real.exp (-W x)) ∂variationMeasure volume Ω u ≤
      weightedVariation W Ω u := by
  have := Ω.isOpen.locallyCompactSpace
  set ν := variationMeasure volume Ω u
  -- An open set `U` between `C` and a compact `L ⊆ Ω`, on which `e^{−W} ≤ M`.
  obtain ⟨L, hL, hCL, hLΩ⟩ := exists_compact_between (hC.image continuous_subtypeVal) Ω.isOpen
    (by rintro _ ⟨x, -, rfl⟩; exact x.property)
  let U : Opens E := ⟨interior L, isOpen_interior⟩
  have hUΩ : U ≤ Ω := interior_subset.trans hLΩ
  set U' : Set Ω := (↑) ⁻¹' (U : Set E)
  have hL' : IsCompact (((↑) : Ω → E) ⁻¹' L) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hL (by simpa using hLΩ)
  have hνU : ν U' ≠ ∞ :=
    ((measure_mono (preimage_mono interior_subset)).trans_lt hL'.measure_lt_top).ne
  obtain ⟨M, hM⟩ := hL.bddAbove_image hW.continuous.neg.rexp.continuousOn
  have hgU (x : Ω) (hx : x ∈ U') : Real.exp (-W x) ≤ max M 0 :=
    (hM ⟨(x : E), interior_subset hx, rfl⟩).trans (le_max_left _ _)
  have hU' : MeasurableSet U' := (U.isOpen.preimage continuous_subtypeVal).measurableSet
  refine (lintegral_mono_set (t := U') fun x hx => hCL (mem_image_of_mem _ hx)).trans
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg hW hU' hνU hgU)
    (ae_of_all _ fun x => (Real.exp_pos _).le)]
  -- A test field `X` on `Ω`, supported in `U`, whose pairing with `u` is `δ`-close to `|Du|(U)`.
  set δ := (ε : ℝ) / (max M 0 + 1)
  have hνt : ν.real U' = (totalVariationOn volume U u).toReal := by
    rw [measureReal_def, variationMeasure_preimage_coe hu hfin hUΩ]
  have htv : totalVariationOn volume U u ≠ ∞ := by
    rwa [← variationMeasure_preimage_coe hu hfin hUΩ]
  obtain ⟨Y, hY1, hYt⟩ :=
    exists_toReal_totalVariationOn_sub_lt_integral htv (show 0 < δ by positivity)
  let X : 𝓓(Ω, E) := monoCLM ℝ Y
  have hXY : (X : E → E) = Y := by simp [X, hUΩ]
  have hX1 (x : E) : ‖X x‖ ≤ 1 := by simpa [hXY] using hY1 x
  have hXU (x : Ω) (hx : x ∉ U') : X x = 0 := by
    rw [hXY]
    exact image_eq_zero_of_notMem_tsupport fun h => hx (Y.tsupport_subset h)
  have hYX : ∫ x, divergenceCLM Y x * u x = ∫ x, divergenceCLM X x * u x := by
    simp only [divergenceCLM_apply, hXY]
  have hkey := setIntegral_exp_neg_le hW hu hfin X hX1 hU' hνU hXU hgU
  have hεM : max M 0 * δ ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [le_max_right M 0, ε.coe_nonneg]
  have hdef : max M 0 * (ν.real U' - ∫ x, divergenceCLM X x * u x) ≤ max M 0 * δ :=
    mul_le_mul_of_nonneg_left (by linarith) (le_max_right M 0)
  calc ENNReal.ofReal (∫ x in U', Real.exp (-W x) ∂ν)
      ≤ ENNReal.ofReal
          ((∫ x, (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) * u x) +
            max M 0 * δ) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ weightedVariation W Ω u + ε := ENNReal.ofReal_add_le.trans <| add_le_add
          (ofReal_integral_le_weightedVariation X hX1)
          (by simpa using ENNReal.ofReal_le_ofReal hεM)

/-- **Weighted variation is the weighted variation measure.** For a `C¹` weight `W` and `u`
locally integrable on the open set `Ω` with locally finite Euclidean variation there, the
weighted variation `V_μ(u; Ω)` is the integral `∫_Ω e^{−W} d|Du|` of the density against the
variation measure. -/
theorem weightedVariation_eq_lintegral_variationMeasure :
    weightedVariation W Ω u =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-W x)) ∂variationMeasure volume Ω u := by
  have := Ω.isOpen.locallyCompactSpace
  refine le_antisymm (weightedVariation_le_iff.2 fun X hX => ?_) ?_
  · -- Each pairing is `-∫ e^{−W} ⟪X, σ_u⟫ d|Du|`, and `|⟪X, σ_u⟫| ≤ 1` almost everywhere.
    rw [integral_weightedDivergence_mul_eq_neg_integral_inner_polarDensity hW hu hfin]
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    rw [← Real.eNorm_eq_ofReal_abs, eNorm_neg]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [ae_norm_polarDensity_eq_one hu hfin] with x hx
    rw [Real.eNorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (Real.exp_pos _).le ?_)
    exact (abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one]; exact hX x)
  · -- Exhaust `Ω` by compact sets.
    rw [← setLIntegral_univ, ← iUnion_compactCovering,
      setLIntegral_iUnion_of_directed _ (directed_of_isDirected_le fun _ _ h =>
        compactCovering_subset Ω h)]
    exact iSup_le fun n =>
      setLIntegral_le_weightedVariation hW hu hfin (isCompact_compactCovering _ n)

/-- **The weighted variation measure on open subsets.** For a `C¹` weight `W`, `u` locally
integrable on `Ω` with locally finite variation there and an open set `U ⊆ Ω`, the weighted
variation `V_μ(u; U)` is `∫_U e^{−W} d|Du|`, with `|Du|` the variation measure on `Ω`. Thus
`U ↦ V_μ(u; U)` is the restriction to open sets of the measure `e^{−W} |Du|` on `Ω`. -/
theorem weightedVariation_eq_setLIntegral_variationMeasure {U : Opens E} (hU : U ≤ Ω) :
    weightedVariation W U u = ∫⁻ x in (↑) ⁻¹' (U : Set E),
      ENNReal.ofReal (Real.exp (-W x)) ∂variationMeasure volume Ω u := by
  rw [weightedVariation_eq_lintegral_variationMeasure hW (hu.mono_set hU)
      (fun K hK hKU => hfin K hK (hKU.trans hU)),
    ← map_inclusion_variationMeasure hu hfin hU,
    lintegral_map (f := fun x : Ω => ENNReal.ofReal (Real.exp (-W x)))
      (hW.continuous.comp continuous_subtypeVal).neg.rexp.measurable.ennreal_ofReal
      (continuous_inclusion _).measurable]
  -- The two sides differ only in writing the subtype of `U` as `↥U` (an open set) and as `↑↑U`
  -- (its underlying set), and in composing with the inclusion, whose coercion is the identity.
  rfl

end TauCeti
