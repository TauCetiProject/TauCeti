/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.LebesgueDecomposition
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Regular
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.PerimeterUpperBound

/-!
# Quantitative perimeter excess and interval-section rigidity for Steiner symmetrization

Let `E` be a finite-dimensional real inner product space, `e` a unit vector with orthogonal
hyperplane `H = (ℝ ∙ e)ᗮ`, and `s ⊆ E` a null-measurable set of finite volume. Write
`v(y) = |{t : ℝ | y + t • e ∈ s}|` for the section-length function on `H`, `D = {y | 0 < v(y)}`
for the essential projection, and `∇ᵃv` for the absolutely continuous derivative density
`acDerivativeDensity volume ⊤ v (volume.comap Subtype.val)` of `v` on `H`.

This file proves the Chlebík–Cianchi–Fusco / Cagnetti–Colombo–De Philippis–Maggi quantitative
excess refinement of Steiner's perimeter inequality
(`TauCeti.perimeter_steinerSymmetrization_add_setLIntegral_le` and
`TauCeti.perimeter_steinerSymmetrization_add_lintegral_noninterval_le`):

`P(S_e s) + ∫_{y ∈ A} 4 / √(4 + ‖∇ᵃv(y)‖²) dy ≤ P(s)`,

where `S_e s = steinerSymmetrization e he s` and `A ⊆ H` is the family of transverse points whose
line sections do not agree almost everywhere with any interval. No boundedness or regularity of `s`
is assumed, and `P(s)` may be infinite.

Consequently, **equality in Steiner's perimeter inequality forces interval sections**
(`TauCeti.ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq`): if `P(s) < ∞` and
`P(S_e s) = P(s)`, then for almost every `y ∈ (ℝ ∙ e)ᗮ` the section `{t | y + t • e ∈ s}` agrees
almost everywhere with an interval. Interval sections are necessary but not sufficient for equality
in a single direction: a sheared slab has interval sections along `e`, yet symmetrization removes
the tilt of its midpoints and strictly decreases perimeter.

## Proof outline

In the localized joint slicing inequality
(`TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`), we
choose a measurable transverse vector field `Φ₀` of norm at most `1` equal to `-σ_v` on a
singular carrier of `|Dˢv|`, to `-∇ᵃv / √(4 + ‖∇ᵃv‖²)` on `D`, and to `-∇ᵃv / ‖∇ᵃv‖` off `D`.
Approximating `Φ₀` by smooth compactly supported test fields of norm at most `1` in `L¹` against
the finite measure `volume.restrict D + ‖∇ᵃv‖ volume + |Dˢv|`
(`MeasureTheory.MemLp.exists_testFunction_eLpNorm_sub_le_and_norm_le`) yields
`∫_D √(4 + ‖∇ᵃv‖²) + ∫_{Dᶜ} ‖∇ᵃv‖ + |Dˢv|(H) + ∫_A 4 / √(4 + ‖∇ᵃv‖²) ≤ P(s)`,
whose first three terms dominate `P(S_e s)` by the smooth-slab upper bound
(`TauCeti.perimeter_steinerSymmetrization_le_lintegral_add_singularPart`).

## Main declarations

* `TauCeti.perimeter_steinerSymmetrization_add_setLIntegral_le`: quantitative perimeter excess
  bound for any null-measurable family `A` of noninterval sections.
* `TauCeti.perimeter_steinerSymmetrization_add_lintegral_noninterval_le`: the same bound over the
  full set of noninterval sections.
* `TauCeti.ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq`: equality in
  Steiner's perimeter inequality forces almost every parallel line section to agree a.e. with an
  interval.

## References

* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TestFunction
open scoped Distributions ENNReal RealInnerProductSpace Topology

namespace TauCeti

section Rigidity

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- Calibration identity `√(1 - ‖-(√(4 + ‖a‖²))⁻¹ • a‖²) = 2 / √(4 + ‖a‖²)`. -/
private theorem sqrt_one_sub_norm_calibration_sq (a : H) :
    √(1 - ‖-(√(4 + ‖a‖ ^ 2))⁻¹ • a‖ ^ 2) = 2 / √(4 + ‖a‖ ^ 2) := by
  have hpos : 0 < 4 + ‖a‖ ^ 2 := by positivity
  have halg : 1 - (4 + ‖a‖ ^ 2)⁻¹ * ‖a‖ ^ 2 = 4 / (4 + ‖a‖ ^ 2) := by field_simp [hpos.ne']; ring
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_of_pos (Real.sqrt_pos.2 hpos), mul_pow,
    inv_pow, Real.sq_sqrt hpos.le, halg, Real.sqrt_div (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]

/-- The comap of Lebesgue volume to `(⊤ : Opens H)` is finite on compacts, hence σ-finite. -/
private theorem isFiniteMeasureOnCompacts_comap_top :
    IsFiniteMeasureOnCompacts ((volume : Measure H).comap Subtype.val : Measure (⊤ : Opens H)) :=
  ⟨fun _ hK => (Measure.comap_apply_le Subtype.val volume hK.nullMeasurableSet).trans_lt
    (hK.image continuous_subtype_val).measure_lt_top⟩

/-- Measurability of the quantitative excess weight `y ↦ 4 / √(4 + ‖∇ᵃv(y)‖²)`. -/
private theorem measurable_four_div_sqrt_four_add_norm_sq (v : H → ℝ) :
    Measurable fun y : H => ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤ v
      (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2)) :=
  ENNReal.continuous_ofReal.measurable.comp (measurable_const.div ((Real.continuous_sqrt.comp
    (continuous_const.add (continuous_norm.pow 2))).measurable.comp
    ((measurable_acDerivativeDensity (volume.comap Subtype.val)).comp
      (Continuous.subtype_mk continuous_id fun _ => trivial).measurable)))

/-- Construct the measurable calibration field `Φ₀ : (⊤ : Opens H) → H` of norm at most `1`
capturing the absolutely continuous density on `D'`, on `D'ᶜ`, and the singular polar density. -/
private theorem exists_measurable_calibrationField {v : H → ℝ} (hv : LocallyIntegrable v volume)
    (hvar : totalVariationOn volume ⊤ v ≠ ∞) {MD : Set H} (hMDm : MeasurableSet MD) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let gΩ : (⊤ : Opens H) → H := acDerivativeDensity volume ⊤ v ν
    let μs : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ v).singularPart ν
    let D' : Set (⊤ : Opens H) := Subtype.val ⁻¹' MD
    ∃ Φ₀ : (⊤ : Opens H) → H,
      Measurable Φ₀ ∧ (∀ z, ‖Φ₀ z‖ ≤ 1) ∧
      (∀ᵐ z ∂ν, z ∈ D' → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z) ∧
      (∀ᵐ z ∂ν, z ∉ D' → Φ₀ z = -‖gΩ z‖⁻¹ • gΩ z) ∧
      (∀ᵐ z ∂μs, -⟪Φ₀ z, polarDensity volume ⊤ v z⟫ = 1) := by
  classical
  intro ν gΩ μs D'
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  let σ := polarDensity volume ⊤ v
  have hmut := Measure.mutuallySingular_singularPart (variationMeasure volume ⊤ v) ν
  let N := hmut.nullSet
  let Φ₀ : (⊤ : Opens H) → H := fun z =>
    if z ∈ N then
      if z ∈ D' then -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z else -‖gΩ z‖⁻¹ • gΩ z
    else -‖σ z‖⁻¹ • σ z
  have hΦ₀m : Measurable Φ₀ := by
    have h1 : Measurable fun z : (⊤ : Opens H) => -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z :=
      ((Real.continuous_sqrt.comp (continuous_const.add
        (continuous_norm.pow 2))).measurable.comp (measurable_acDerivativeDensity ν)).inv.neg.smul
        (measurable_acDerivativeDensity ν)
    exact Measurable.ite hmut.measurableSet_nullSet
      (Measurable.ite (hMDm.preimage continuous_subtype_val.measurable) h1
        ((measurable_acDerivativeDensity ν).norm.inv.neg.smul (measurable_acDerivativeDensity ν)))
      (measurable_polarDensity.norm.inv.neg.smul measurable_polarDensity)
  have hΦ₀1 (z : (⊤ : Opens H)) : ‖Φ₀ z‖ ≤ 1 := by
    have hunit (u : H) : ‖-‖u‖⁻¹ • u‖ ≤ 1 := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_norm]
      by_cases hu0 : ‖u‖ = 0 <;> simp [hu0]
    dsimp only [Φ₀]
    split_ifs
    · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_mul_le_iff₀ (Real.sqrt_pos.2 (by positivity)), mul_one]
      exact Real.le_sqrt_of_sq_le (by linarith)
    · exact hunit _
    · exact hunit _
  have haeN : ∀ᵐ z ∂ν, z ∈ N := by rw [ae_iff]; exact hmut.measure_compl_nullSet
  have haeNc : ∀ᵐ z ∂μs, z ∉ N := by
    rw [ae_iff, show {z : (⊤ : Opens H) | ¬z ∉ N} = N by ext z; simp]
    exact hmut.measure_nullSet
  have hσ1 : ∀ᵐ z ∂μs, ‖σ z‖ = 1 :=
    (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ ν)).ae_le
      (ae_norm_polarDensity_eq_one (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩)
  refine ⟨Φ₀, hΦ₀m, hΦ₀1, haeN.mono fun z hzN hzD => by simp [Φ₀, hzN, hzD],
    haeN.mono fun z hzN hzD => by simp [Φ₀, hzN, hzD], ?_⟩
  filter_upwards [haeNc, hσ1] with z hzN hzσ
  simp [Φ₀, σ, hzN, hzσ]

/-- Approximate a bounded measurable field `Φ₀` by smooth compactly supported test fields `φ k` of
norm at most `1` in `L¹` against `ν.restrict D' + ν.withDensity ‖∇ᵃv‖ₑ + |Dˢv|`. -/
private theorem exists_calibration_testFunction_seq {v : H → ℝ} (hv : LocallyIntegrable v volume)
    (hvar : totalVariationOn volume ⊤ v ≠ ∞) {MD : Set H} (hMDm : MeasurableSet MD)
    (hMDfin : volume MD ≠ ∞) {Φ₀ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀)
    (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let gΩ : (⊤ : Opens H) → H := acDerivativeDensity volume ⊤ v ν
    let μs : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ v).singularPart ν
    let D' : Set (⊤ : Opens H) := Subtype.val ⁻¹' MD
    ∃ φ : ℕ → 𝓓((⊤ : Opens H), H), (∀ k y, ‖φ k y‖ ≤ 1) ∧
      (∀ k, ∫⁻ z in D', ‖Φ₀ z - φ k z‖ₑ ∂ν ≤ (1 / 2 : ℝ≥0∞) ^ k) ∧
      (∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖gΩ z‖ₑ ∂ν ≤ (1 / 2 : ℝ≥0∞) ^ k) ∧
      (∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μs ≤ (1 / 2 : ℝ≥0∞) ^ k) := by
  intro ν gΩ μs D'
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  have := isFiniteMeasureOnCompacts_comap_top (H := H)
  have hνD'_fin : ν D' < ∞ := (Measure.comap_apply_le Subtype.val volume
    (hMDm.preimage measurable_subtype_coe).nullMeasurableSet).trans_lt
    ((measure_mono (image_preimage_subset Subtype.val MD)).trans_lt hMDfin.lt_top)
  have hgΩ_int := integrable_acDerivativeDensity (hv.locallyIntegrableOn _) ν hvar
  have hμs_fin : μs univ < ∞ := (Measure.singularPart_le _ ν univ).trans_lt
    ((variationMeasure_univ (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩) ▸ hvar.lt_top)
  let μ : Measure (⊤ : Opens H) := ν.restrict D' + ν.withDensity (fun z => ‖gΩ z‖ₑ) + μs
  have : IsFiniteMeasure (ν.restrict D') := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have : IsFiniteMeasure (ν.withDensity (fun z => ‖gΩ z‖ₑ)) :=
    ⟨by rw [withDensity_apply _ .univ, Measure.restrict_univ]
        exact hasFiniteIntegral_iff_eNorm.1 hgΩ_int.2⟩
  have : IsFiniteMeasure μs := ⟨hμs_fin⟩
  have hmem : MemLp Φ₀ 1 μ := MemLp.of_bound hΦ₀m.aestronglyMeasurable 1 (.of_forall hΦ₀1)
  choose φ hφ1 hφerr using fun k : ℕ =>
    hmem.exists_testFunction_eLpNorm_sub_le_and_norm_le (n := (⊤ : ℕ∞)) ENNReal.one_ne_top
      zero_le_one (.of_forall hΦ₀1) (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 1 / 2) k).ne'
  have herr_μ (k : ℕ) : ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μ ≤ (1 / 2 : ℝ≥0∞) ^ k := by
    simpa only [Pi.sub_apply] using lintegral_eNorm_le_eLpNorm_one.trans (hφerr k)
  refine ⟨φ, hφ1,
    fun k => (lintegral_mono' ((Measure.le_add_right le_rfl).trans
      (Measure.le_add_right le_rfl)) le_rfl).trans (herr_μ k),
    fun k => ?_,
    fun k => (lintegral_mono' (Measure.le_add_left le_rfl) le_rfl).trans (herr_μ k)⟩
  calc ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖gΩ z‖ₑ ∂ν
      = ∫⁻ z, ((fun z => ‖gΩ z‖ₑ) * (fun z => ‖Φ₀ z - φ k z‖ₑ)) z ∂ν :=
        lintegral_congr fun _ => mul_comm _ _
    _ = ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂ν.withDensity (fun z => ‖gΩ z‖ₑ) :=
        (lintegral_withDensity_eq_lintegral_mul₀
          (measurable_acDerivativeDensity ν).eNorm.aemeasurable
          (hΦ₀m.sub (by fun_prop)).eNorm.aemeasurable).symm
    _ ≤ ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μ :=
        lintegral_mono' ((Measure.le_add_left le_rfl).trans (Measure.le_add_right le_rfl)) le_rfl
    _ ≤ (1 / 2 : ℝ≥0∞) ^ k := herr_μ k

/-- Dominated convergence of `2 * ∫⁻_S √(1 - ‖φ k‖²)` to `∫⁻_S 4 / √(4 + ‖gΩ‖²)` along a fast `L¹`
approximating sequence on `MD`. -/
private theorem tendsto_two_mul_setLIntegral_calibration {MD S : Set H} (hMDm : MeasurableSet MD)
    (hSm : NullMeasurableSet S volume) (hSfin : volume S ≠ ∞)
    (hSMD : ∀ᵐ y : H ∂volume, y ∈ S → y ∈ MD) {Φ₀ gΩ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀)
    (hΦ₀_D : ∀ᵐ z : (⊤ : Opens H) ∂(volume.comap Subtype.val),
      z ∈ Subtype.val ⁻¹' MD → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z)
    (φ : ℕ → 𝓓((⊤ : Opens H), H))
    (herr_D : ∀ k, ∫⁻ z in Subtype.val ⁻¹' MD, ‖Φ₀ z - φ k z‖ₑ
      ∂(volume.comap Subtype.val) ≤ (1 / 2 : ℝ≥0∞) ^ k) :
    Tendsto (fun k => 2 * ∫⁻ y in S, ENNReal.ofReal √(1 - ‖φ k y‖ ^ 2)) atTop
      (𝓝 (∫⁻ y in S, ENNReal.ofReal (4 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)))) := by
  have hae_MD : ∀ᵐ y : H ∂volume, y ∈ MD →
      Tendsto (fun k => φ k y) atTop (𝓝 (Φ₀ ⟨y, trivial⟩)) := by
    have hF (k : ℕ) : Measurable (MD.indicator fun y : H => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ) :=
      ((hΦ₀m.comp (Continuous.subtype_mk continuous_id fun _ => trivial).measurable).sub
        (φ k).continuous.measurable).eNorm.indicator hMDm
    have hle (k : ℕ) : ∫⁻ y : H, MD.indicator (fun y => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ) y ≤
        (1 / 2 : ℝ≥0∞) ^ k := by
      rw [lintegral_indicator hMDm]
      let T : Set ((⊤ : Opens H) : Set H) := Subtype.val ⁻¹' MD
      have hsub := setLIntegral_subtype (μ := volume) (s := ((⊤ : Opens H) : Set H))
        (⊤ : Opens H).isOpen.measurableSet T (fun y : H => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ)
      rw [show Subtype.val '' T = MD by
        ext y; exact ⟨fun ⟨_, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨⟨y, trivial⟩, hy, rfl⟩⟩] at hsub
      exact hsub.symm.trans_le (herr_D k)
    have hsum : (∑' k, ∫⁻ y : H, MD.indicator (fun y => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ) y) ≠ ∞ :=
      ne_top_of_le_ne_top (by simp [ENNReal.tsum_geometric]) (_root_.tsum_le_tsum hle)
    filter_upwards [ae_tendsto_zero_of_tsum_lintegral_ne_top (fun k => (hF k).aemeasurable) hsum]
      with y hy hyMD
    simp only [hyMD, indicator_of_mem] at hy
    exact tendsto_iff_norm_sub_tendsto_zero.2 <| by
      simpa only [Function.comp_def, ENNReal.toReal_zero, ← ofReal_norm, norm_sub_rev,
        ENNReal.toReal_ofReal (norm_nonneg _)] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hy
  have hae_val : ∀ᵐ y : H ∂volume, y ∈ MD →
      Φ₀ ⟨y, trivial⟩ = -(√(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2))⁻¹ • gΩ ⟨y, trivial⟩ := by
    have h := (ae_restrict_iff_subtype (μ := volume) (s := ((⊤ : Opens H) : Set H))
      (⊤ : Opens H).isOpen.measurableSet
      (p := fun y : H => y ∈ MD →
        Φ₀ ⟨y, trivial⟩ = -(√(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2))⁻¹ • gΩ ⟨y, trivial⟩)).2 hΦ₀_D
    rwa [Opens.coe_top, Measure.restrict_univ] at h
  have hdct : Tendsto (fun k => ∫⁻ y in S, ENNReal.ofReal √(1 - ‖φ k y‖ ^ 2)) atTop
      (𝓝 (∫⁻ y in S, ENNReal.ofReal (2 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)))) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞))
      (fun k => (ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_const.sub ((φ k).continuous.norm.pow 2)))).measurable)
      (fun k => .of_forall fun y => ENNReal.ofReal_le_one.2
        (Real.sqrt_le_one.2 (by nlinarith [norm_nonneg (φ k y)])))
      (by simp [hSfin]) ((ae_restrict_iff'₀ hSm).2 ?_)
    filter_upwards [hSMD, hae_MD, hae_val] with y hyS hy_lim hy_val hy_mem
    have hcont : Continuous fun u : H => ENNReal.ofReal √(1 - ‖u‖ ^ 2) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_norm.pow 2)))
    simpa only [Function.comp_def, hy_val (hyS hy_mem), sqrt_one_sub_norm_calibration_sq] using
      (hcont.tendsto _).comp (hy_lim (hyS hy_mem))
  have hmul_eq : ∫⁻ y in S, ENNReal.ofReal (4 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)) =
      2 * ∫⁻ y in S, ENNReal.ofReal (2 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_congr fun _ => ?_
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]; ring_nf
  rw [hmul_eq]
  exact ENNReal.Tendsto.const_mul hdct (.inr ENNReal.ofNat_ne_top)

/-- Weighted `L¹` convergence of `-∫ ⟪φ k, ψ⟫ ∂η` to `-∫ ⟪Φ₀, ψ⟫ ∂η` for bounded test fields. -/
private theorem tendsto_neg_integral_inner_of_lintegral_le {η : Measure (⊤ : Opens H)}
    {ψ Φ₀ : (⊤ : Opens H) → H} (hψm : AEStronglyMeasurable ψ η)
    (hψn : Integrable (fun z => ‖ψ z‖) η) (hΦ₀m : Measurable Φ₀) (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1)
    (φ : ℕ → 𝓓((⊤ : Opens H), H)) (hφ1 : ∀ k y, ‖φ k y‖ ≤ 1)
    (herr : ∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖ψ z‖ₑ ∂η ≤ (1 / 2 : ℝ≥0∞) ^ k) :
    Tendsto (fun k => -∫ z, ⟪φ k z, ψ z⟫ ∂η) atTop (𝓝 (-∫ z, ⟪Φ₀ z, ψ z⟫ ∂η)) := by
  have hpow0 : Tendsto (fun k => (∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖ψ z‖ₑ ∂η).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
        (fun _ => zero_le) herr)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hpow0)
  have hint_inner {u : (⊤ : Opens H) → H} (hum : AEStronglyMeasurable u η) (hu1 : ∀ z, ‖u z‖ ≤ 1) :
      Integrable (fun z => ⟪u z, ψ z⟫) η :=
    hψn.mono' (hum.inner hψm) (.of_forall fun z => (Real.norm_eq_abs _).trans_le
      ((abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hu1 z))))
  have hi_0 := hint_inner hΦ₀m.aestronglyMeasurable hΦ₀1
  have hi_k := hint_inner (by fun_prop) (fun z => hφ1 k z)
  have hdiff_int : Integrable (fun z => ‖Φ₀ z - φ k z‖ * ‖ψ z‖) η :=
    (hψn.const_mul 2).mono' ((hΦ₀m.sub (by fun_prop)).norm.aestronglyMeasurable.mul hψn.1)
      (.of_forall fun z => (Real.norm_of_nonneg (by positivity)).trans_le
        (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith [hΦ₀1 z, hφ1 k z]))
          (norm_nonneg _)))
  rw [dist_neg_neg, dist_eq_norm, norm_sub_rev, ← integral_sub hi_0 hi_k]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono (hi_0.sub hi_k).norm hdiff_int
    fun z => ?_).trans_eq ?_)
  · dsimp only [Pi.sub_apply]
    rw [← inner_sub_left]; exact (Real.norm_eq_abs _).trans_le (abs_real_inner_le_norm _ _)
  · rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity),
      ofReal_integral_eq_lintegral_ofReal hdiff_int (.of_forall fun _ => by positivity)]
    congr 1
    exact lintegral_congr fun z => by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- Convergence of the transverse divergence pairings `∫ div(φ k) v` to `-∫ ⟪Φ₀, gΩ⟫ ∂ν + |Dˢv|(H)`
along the calibration sequence. -/
private theorem tendsto_integral_divergenceCLM_calibration {v : H → ℝ}
    (hv : LocallyIntegrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {Φ₀ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀) (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1)
    (hΦ₀_μs : ∀ᵐ z ∂(variationMeasure volume ⊤ v).singularPart (volume.comap Subtype.val),
      -⟪Φ₀ z, polarDensity volume ⊤ v z⟫ = 1)
    (φ : ℕ → 𝓓((⊤ : Opens H), H)) (hφ1 : ∀ k y, ‖φ k y‖ ≤ 1)
    (herr_g : ∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ *
      ‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖ₑ
      ∂(volume.comap Subtype.val) ≤ (1 / 2 : ℝ≥0∞) ^ k)
    (herr_μs : ∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ
      ∂(variationMeasure volume ⊤ v).singularPart (volume.comap Subtype.val) ≤
      (1 / 2 : ℝ≥0∞) ^ k) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    Tendsto (fun k => ∫ y : H, divergenceCLM (φ k) y * v y) atTop
      (𝓝 (-∫ z, ⟪Φ₀ z, acDerivativeDensity volume ⊤ v ν z⟫ ∂ν +
        ((variationMeasure volume ⊤ v).singularPart ν).real univ)) := by
  intro ν
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  have := isFiniteMeasureOnCompacts_comap_top (H := H)
  let μs := (variationMeasure volume ⊤ v).singularPart ν
  let σ := polarDensity volume ⊤ v
  have hgΩ_int := integrable_acDerivativeDensity (hv.locallyIntegrableOn _) ν hvar
  have hμs_fin : μs univ < ∞ := (Measure.singularPart_le _ ν univ).trans_lt
    ((variationMeasure_univ (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩) ▸ hvar.lt_top)
  have : IsFiniteMeasure μs := ⟨hμs_fin⟩
  have hσ1 : ∀ᵐ z ∂μs, ‖σ z‖ = 1 :=
    (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ ν)).ae_le
      (ae_norm_polarDensity_eq_one (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩)
  have hlim_ac := tendsto_neg_integral_inner_of_lintegral_le hgΩ_int.aestronglyMeasurable
    hgΩ_int.norm hΦ₀m hΦ₀1 φ hφ1 herr_g
  have hlim_sing : Tendsto (fun k => -∫ z, ⟪φ k z, σ z⟫ ∂μs) atTop (𝓝 (μs.real univ)) := by
    have heq : -∫ z, ⟪Φ₀ z, σ z⟫ ∂μs = μs.real univ := by
      rw [← integral_neg, integral_congr_ae hΦ₀_μs, integral_const, smul_eq_mul, mul_one]
    rw [← heq]
    refine tendsto_neg_integral_inner_of_lintegral_le measurable_polarDensity.aestronglyMeasurable
      ((integrable_const (1 : ℝ)).congr (hσ1.mono fun _ h => h.symm)) hΦ₀m hΦ₀1 φ hφ1 fun k => ?_
    refine (lintegral_congr_ae (hσ1.mono fun z hz => ?_)).trans_le (herr_μs k)
    dsimp only [σ] at hz
    rw [← ofReal_norm (polarDensity volume ⊤ v z), hz, ENNReal.ofReal_one, mul_one]
  refine (hlim_ac.add hlim_sing).congr fun k => ?_
  have hleb := integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
    (hv.locallyIntegrableOn _) (fun _ _ hK => ⟨⊤, hK, hvar⟩) ν (φ k)
  linarith

/-- Identify `ENNReal.ofReal (-∫ ⟪Φ₀, gΩ⟫ ∂ν + |Dˢv|.real univ)` as
`∫⁻_D ‖g‖² / √(4 + ‖g‖²) + ∫⁻_{Dᶜ} ‖g‖ₑ + |Dˢv|(H)`. -/
private theorem ofReal_calibration_limit_eq {v : H → ℝ} (hv : LocallyIntegrable v volume)
    (hvar : totalVariationOn volume ⊤ v ≠ ∞) {D MD : Set H} (hMDm : MeasurableSet MD)
    (hMD_ae : D =ᵐ[volume] MD) {Φ₀ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀)
    (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1)
    (hΦ₀_D : ∀ᵐ z : (⊤ : Opens H) ∂(volume.comap Subtype.val), z ∈ Subtype.val ⁻¹' MD →
      Φ₀ z = -(√(4 + ‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖ ^ 2))⁻¹ •
        acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z)
    (hΦ₀_Dc : ∀ᵐ z : (⊤ : Opens H) ∂(volume.comap Subtype.val), z ∉ Subtype.val ⁻¹' MD →
      Φ₀ z = -‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖⁻¹ •
        acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let g : H → H := fun y => acDerivativeDensity volume ⊤ v ν ⟨y, trivial⟩
    ENNReal.ofReal (-∫ z, ⟪Φ₀ z, acDerivativeDensity volume ⊤ v ν z⟫ ∂ν +
        ((variationMeasure volume ⊤ v).singularPart ν).real univ) =
      (∫⁻ y in D, ENNReal.ofReal (‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2))) +
        (∫⁻ y in Dᶜ, ‖g y‖ₑ) + (variationMeasure volume ⊤ v).singularPart ν univ := by
  classical
  intro ν g
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  let gΩ := acDerivativeDensity volume ⊤ v ν
  let μs := (variationMeasure volume ⊤ v).singularPart ν
  have hgΩ_int := integrable_acDerivativeDensity (hv.locallyIntegrableOn _) ν hvar
  have hμs_fin : μs univ < ∞ := (Measure.singularPart_le _ ν univ).trans_lt
    ((variationMeasure_univ (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩) ▸ hvar.lt_top)
  have hi_0 : Integrable (fun z => -⟪Φ₀ z, gΩ z⟫) ν :=
    hgΩ_int.norm.mono' (hΦ₀m.aestronglyMeasurable.inner hgΩ_int.aestronglyMeasurable).neg
      (.of_forall fun z => (Real.norm_eq_abs _).trans_le ((abs_neg _).trans_le
        ((abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hΦ₀1 z)))))
  have hae_pt : (fun z : (⊤ : Opens H) => -⟪Φ₀ z, gΩ z⟫) =ᵐ[ν]
      fun z => if z ∈ Subtype.val ⁻¹' MD then ‖gΩ z‖ ^ 2 / √(4 + ‖gΩ z‖ ^ 2) else ‖gΩ z‖ := by
    filter_upwards [hΦ₀_D, hΦ₀_Dc] with z hzD hzDc
    change z ∈ Subtype.val ⁻¹' MD → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z at hzD
    change z ∉ Subtype.val ⁻¹' MD → Φ₀ z = -‖gΩ z‖⁻¹ • gΩ z at hzDc
    by_cases hz : z ∈ Subtype.val ⁻¹' MD
    · simp only [hz, ↓reduceIte]
      rw [hzD hz, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]; ring
    · simp only [hz, ↓reduceIte]
      rw [hzDc hz, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
      by_cases hg0 : ‖gΩ z‖ = 0
      · simp [hg0]
      · rw [neg_mul, neg_neg, sq, inv_mul_cancel_left₀ hg0]
  have hnonneg : 0 ≤ᵐ[ν] fun z => -⟪Φ₀ z, gΩ z⟫ :=
    hae_pt.mono fun z hz => by dsimp only [Pi.zero_apply] at hz ⊢; rw [hz]; split_ifs <;> positivity
  rw [← integral_neg, ENNReal.ofReal_add (integral_nonneg_of_ae hnonneg) measureReal_nonneg,
    measureReal_def, ENNReal.ofReal_toReal hμs_fin.ne,
    ofReal_integral_eq_lintegral_ofReal hi_0 hnonneg,
    lintegral_congr_ae (hae_pt.mono fun z hz => by dsimp only at hz; rw [hz])]
  have hsub := lintegral_subtype_comap (μ := volume) (s := ((⊤ : Opens H) : Set H))
    (⊤ : Opens H).isOpen.measurableSet
    (fun y : H => ENNReal.ofReal (if y ∈ MD then ‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2) else ‖g y‖))
  rw [Opens.coe_top, Measure.restrict_univ] at hsub
  rw [show (∫⁻ z : (⊤ : Opens H), ENNReal.ofReal
      (if z ∈ Subtype.val ⁻¹' MD then ‖gΩ z‖ ^ 2 / √(4 + ‖gΩ z‖ ^ 2) else ‖gΩ z‖) ∂ν) =
      ∫⁻ y : H, ENNReal.ofReal (if y ∈ MD then ‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2) else ‖g y‖) from hsub,
    ← lintegral_add_compl _ hMDm, setLIntegral_congr hMD_ae, setLIntegral_congr hMD_ae.compl]
  congr 2
  · exact setLIntegral_congr_fun hMDm fun y hy => by simp [hy]
  · exact setLIntegral_congr_fun hMDm.compl fun y hy => by
      have hy' : y ∉ MD := hy; simp [hy', ofReal_norm]

/-- Algebraic recombination `(4 / √(4 + ‖g‖²)) + (‖g‖² / √(4 + ‖g‖²)) = √(4 + ‖g‖²)` under the
Lebesgue integral on `D`. -/
private theorem setLIntegral_four_add_norm_sq_div_sqrt (v : H → ℝ) (D : Set H) :
    let g : H → H := fun y =>
      acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) ⟨y, trivial⟩
    (∫⁻ y in D, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2))) +
        (∫⁻ y in D, ENNReal.ofReal (‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2))) =
      ∫⁻ y in D, ENNReal.ofReal √(4 + ‖g y‖ ^ 2) := by
  intro g
  rw [← lintegral_add_left (measurable_four_div_sqrt_four_add_norm_sq v)]
  exact lintegral_congr fun _ => by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div, Real.div_sqrt]

/-- **Quantitative excess inequality for Steiner symmetrization.** Let `s` be a null-measurable set
of finite volume in `E`, `e` a unit vector, and `A ⊆ (ℝ ∙ e)ᗮ` a null-measurable family of
noninterval line sections. Then
`P(S_e s) + ∫_{y ∈ A} 4 / √(4 + ‖∇ᵃv(y)‖²) dy ≤ P(s)`,
where `v(y) = |{t | y + t • e ∈ s}|` and `∇ᵃv` is its absolutely continuous derivative density.
No finiteness assumption on `P(s)` is needed. -/
theorem perimeter_steinerSymmetrization_add_setLIntegral_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ (steinerSymmetrization e he s) +
      (∫⁻ y in A, ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤
        (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
        (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2))) ≤
      perimeter volume ⊤ s := by
  by_cases hP : perimeter volume ⊤ s = ∞
  · rw [hP]; exact le_top
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let v : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun y => acDerivativeDensity volume ⊤ v ν ⟨y, trivial⟩
  let D : Set (ℝ ∙ e)ᗮ := {y | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  have hv : Integrable v volume := integrable_measureReal_lineSection e he hs hfin
  have hvar : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDA_fin := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume D ≠ ∞ := fun htop => by
    rw [show {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} = D from rfl, htop,
      ENNReal.mul_top two_ne_zero, top_add, top_le_iff] at hDA_fin
    exact hP hDA_fin
  have hAfin : volume A ≠ ∞ := fun htop => by
    rw [htop, ENNReal.mul_top two_ne_zero, add_top, top_le_iff] at hDA_fin
    exact hP hDA_fin
  have hAD : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A → y ∈ D := by
    filter_upwards [hbad] with y hy hyA
    by_contra hyD
    exact hy hyA ∅ ordConnected_empty (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 hyD)))
  let MD := toMeasurable volume D
  have hMDm : MeasurableSet MD := measurableSet_toMeasurable volume D
  have hMD_ae : D =ᵐ[volume] MD := (NullMeasurableSet.toMeasurable_ae_eq hD).symm
  have hMDfin : volume MD ≠ ∞ := by rwa [measure_toMeasurable]
  have hsub_MD : ∀ y : (ℝ ∙ e)ᗮ, y ∈ D → y ∈ MD := fun _ hy => subset_toMeasurable volume D hy
  obtain ⟨Φ₀, hΦ₀m, hΦ₀1, hΦ₀_D, hΦ₀_Dc, hΦ₀_μs⟩ :=
    exists_measurable_calibrationField hv.locallyIntegrable hvar hMDm
  obtain ⟨φ, hφ1, herr_D, herr_g, herr_μs⟩ :=
    exists_calibration_testFunction_seq hv.locallyIntegrable hvar hMDm hMDfin hΦ₀m hΦ₀1
  have hlim_D := tendsto_two_mul_setLIntegral_calibration hMDm hD hDfin
    (.of_forall hsub_MD) hΦ₀m hΦ₀_D φ herr_D
  have hlim_A := tendsto_two_mul_setLIntegral_calibration hMDm hA hAfin
    (hAD.mono fun y hy h => hsub_MD y (hy h)) hΦ₀m hΦ₀_D φ herr_D
  have hlim_div := ENNReal.tendsto_ofReal
    (tendsto_integral_divergenceCLM_calibration hv.locallyIntegrable hvar hΦ₀m hΦ₀1 hΦ₀_μs φ hφ1
      herr_g herr_μs)
  rw [ofReal_calibration_limit_eq hv.locallyIntegrable hvar hMDm hMD_ae hΦ₀m hΦ₀1 hΦ₀_D hΦ₀_Dc]
    at hlim_div
  have hineq := le_of_tendsto ((hlim_D.add hlim_A).add hlim_div) (.of_forall fun k =>
    two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
      hs hfin e he hA hbad (φ k) (hφ1 k))
  refine (add_le_add_left
    (perimeter_steinerSymmetrization_le_lintegral_add_singularPart hs hfin hP e he) _).trans ?_
  calc ((∫⁻ y in D, ENNReal.ofReal √(4 + ‖g y‖ ^ 2)) + (∫⁻ y in Dᶜ, ‖g y‖ₑ) +
          (variationMeasure volume ⊤ v).singularPart ν univ) +
          (∫⁻ y in A, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2)))
      = ((∫⁻ y in D, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2))) +
          (∫⁻ y in A, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2)))) +
          ((∫⁻ y in D, ENNReal.ofReal (‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2))) +
            (∫⁻ y in Dᶜ, ‖g y‖ₑ) + (variationMeasure volume ⊤ v).singularPart ν univ) := by
        rw [← setLIntegral_four_add_norm_sq_div_sqrt v D]; abel
    _ ≤ perimeter volume ⊤ s := hineq

/-- **Quantitative excess inequality over all noninterval sections.** For every null-measurable set
`s` of finite volume and every unit direction `e`, the perimeter gap `P(s) - P(S_e s)` controls the
integral of `4 / √(4 + ‖∇ᵃv(y)‖²)` over the full family of transverse points whose line sections do
not agree almost everywhere with an interval. -/
theorem perimeter_steinerSymmetrization_add_lintegral_noninterval_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) :
    perimeter volume ⊤ (steinerSymmetrization e he s) +
      (∫⁻ y in {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
          ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I},
        ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤
          (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
          (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2))) ≤
      perimeter volume ⊤ s :=
  perimeter_steinerSymmetrization_add_setLIntegral_le hs hfin e he
    (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ => id)

/-- **Steiner perimeter equality forces interval sections.** If a null-measurable set `s` of finite
volume and finite perimeter has the same perimeter as its Steiner symmetral along a unit vector
`e`, then almost every parallel line section of `s` agrees almost everywhere with an interval. -/
theorem ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  let v : (ℝ ∙ e)ᗮ → ℝ := fun z => volume.real {t : ℝ | (z : E) + t • e ∈ s}
  let A : Set (ℝ ∙ e)ᗮ := {y | ∀ I : Set ℝ, I.OrdConnected →
    ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  let w : (ℝ ∙ e)ᗮ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤ v
      (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2))
  have hle := perimeter_steinerSymmetrization_add_lintegral_noninterval_le hs hfin e he
  rw [heq, ← add_zero (perimeter volume ⊤ s), add_assoc, zero_add] at hle
  have hzero : ∫⁻ y in A, w y = 0 := nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left hP).1 hle)
  have hae0 := (ae_restrict_iff'₀ (nullMeasurableSet_noninterval_lineSection hs hfin e he)).1
    ((lintegral_eq_zero_iff (measurable_four_div_sqrt_four_add_norm_sq v)).1 hzero)
  filter_upwards [hae0] with y hy
  by_contra hnot
  push Not at hnot
  exact (ENNReal.ofReal_pos.2 (div_pos (by norm_num) (Real.sqrt_pos.2 (by positivity)))).ne'
    (hy hnot)

end Rigidity

end TauCeti
