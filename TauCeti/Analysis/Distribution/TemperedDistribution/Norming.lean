/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.MeasureTheory.Function.Lp.Dual
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.MeasureTheory.Function.L1Space.Dual
import TauCeti.MeasureTheory.Function.LpSeminorm.WithDensity

/-!
# Norming `Lᵠ` functions by Schwartz functions

Let `μ` be a measure of temperate growth on a finite-dimensional real normed space, and let
`p < ∞` and `q` be Hölder conjugate. The Schwartz functions are dense in `Lᵖ(μ)`, so they norm the
dual space `Lᵠ(μ)`: an `Lᵠ` function `h` whose pairings with Schwartz functions satisfy
`‖∫ g h‖ ≤ B ‖g‖_p` has `‖h‖_q ≤ B`
(`MeasureTheory.Lp.norm_le_of_forall_norm_toTemperedDistribution_apply_le`), and every
`r < ‖h‖_q` is exceeded by `‖∫ g h‖` for some Schwartz function `g` with `‖g‖_p < 1`
(`MeasureTheory.Lp.exists_lt_norm_toTemperedDistribution_apply_of_lt_norm`).

Conversely, for `1 ≤ p < ∞` every tempered distribution `u` with `‖u g‖ ≤ B ‖g‖_p` for all
Schwartz functions `g` is an `Lᵠ` function of norm at most `B`
(`TemperedDistribution.exists_eq_toTemperedDistribution_and_norm_le`). For `1 < p` the bound
extends `u` from the dense Schwartz functions to a continuous linear functional on `Lᵖ(μ)`
(`TemperedDistribution.exists_strongDual_apply_toLp_eq`), and the dual of `Lᵖ(μ)` is `Lᵠ(μ)`
(`MeasureTheory.Lp.dualEquiv`). For `p = 1` the measure `μ` need not be finite, and the dual of
`L¹` is only available for finite measures (`MeasureTheory.Lp.dualOneEquiv`). So `u` is first
weighted: for a weight `0 < w ≤ 1`, integrable for `μ`, such that `w` and `1 / w` have temperate
growth, `g ↦ u (w g)` is bounded on `L¹` of the finite measure `w μ`, hence integration against
an `L^∞(w μ)` function, which also represents `u`. This is how an `Lᵠ` estimate for a
distribution is obtained by duality from estimates on test functions alone, for instance for the
blocks of a distribution in a Besov space of negative order.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.16.
-/

public section

noncomputable section

open scoped ENNReal NNReal SchwartzMap

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.HasTemperateGrowth]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

omit [FiniteDimensional ℝ E] in
/-- The pairing of `h ∈ Lᵠ` with a Schwartz function `g`, as a tempered distribution, is the
value at `g` of the functional `MeasureTheory.Lp.toDual` of `h` on `Lᵖ`. -/
theorem toTemperedDistribution_apply_eq_toDual_apply [SigmaFinite μ] (h : Lp ℂ q μ)
    (g : 𝓢(E, ℂ)) :
    (h : 𝓢'(E, ℂ)) g = toDual ℂ μ q p h (g.toLp p μ) := by
  rw [toTemperedDistribution_apply, toDual_apply]
  refine integral_congr_ae ?_
  filter_upwards [g.coeFn_toLp p μ] with x hx
  rw [hx, smul_eq_mul, mul_comm]

/-- **Nearly norming Schwartz functions.** For `p < ∞`, `q` Hölder conjugate to `p` and
`h ∈ Lᵠ(μ)`, every `r < ‖h‖_q` is exceeded by `‖∫ g h‖` for some Schwartz function `g` with
`‖g‖_p < 1`. -/
theorem exists_lt_norm_toTemperedDistribution_apply_of_lt_norm (hp : p ≠ ∞) (h : Lp ℂ q μ)
    {r : ℝ} (hr : r < ‖h‖) :
    ∃ g : 𝓢(E, ℂ), ‖g.toLp p μ‖ < 1 ∧ r < ‖(h : 𝓢'(E, ℂ)) g‖ := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  set Λ := toDual ℂ μ q p h
  -- The open set of `f` with `‖f‖ < 1` and `r < ‖Λ f‖` is nonempty, as `‖Λ‖ = ‖h‖`, so it meets
  -- the dense range of the Schwartz functions.
  obtain ⟨g, hg1, hg⟩ := (SchwartzMap.denseRange_toLpCLM (F := ℂ) hp (μ := μ)).exists_mem_open
    (s := {f | ‖f‖ < 1 ∧ r < ‖Λ f‖})
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (continuous_norm.comp Λ.continuous)))
    (Λ.exists_lt_apply_of_lt_opNorm (by rwa [LinearIsometry.norm_map]))
  rw [SchwartzMap.toLpCLM_apply] at hg1 hg
  exact ⟨g, hg1, by rwa [toTemperedDistribution_apply_eq_toDual_apply (p := p)]⟩

/-- **Norming by Schwartz functions.** For `p < ∞` and `q` Hölder conjugate to `p`, if
`h ∈ Lᵠ(μ)` satisfies `‖∫ g h‖ ≤ B ‖g‖_p` for every Schwartz function `g`, then `‖h‖_q ≤ B`. -/
theorem norm_le_of_forall_norm_toTemperedDistribution_apply_le (hp : p ≠ ∞) (h : Lp ℂ q μ)
    {B : ℝ} (hB : 0 ≤ B) (hh : ∀ g : 𝓢(E, ℂ), ‖(h : 𝓢'(E, ℂ)) g‖ ≤ B * ‖g.toLp p μ‖) :
    ‖h‖ ≤ B := by
  by_contra! hBh
  obtain ⟨g, hg1, hg⟩ := exists_lt_norm_toTemperedDistribution_apply_of_lt_norm hp h hBh
  exact (hg.trans_le ((hh g).trans (mul_le_of_le_one_right hB hg1.le))).false

end MeasureTheory.Lp

namespace TemperedDistribution

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.HasTemperateGrowth]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- **Extension from the Schwartz functions.** A linear functional `S` on the Schwartz functions
with `‖S g‖ ≤ B ‖g‖_p`, `p < ∞`, extends from the dense Schwartz functions to a continuous linear
functional on `Lᵖ(μ)` of norm at most `B`. -/
theorem exists_strongDual_apply_toLp_eq (hp_top : p ≠ ∞) (S : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hS : ∀ g : 𝓢(E, ℂ), ‖S g‖ ≤ B * ‖g.toLp p μ‖) :
    ∃ Λ : StrongDual ℂ (Lp ℂ p μ), ‖Λ‖ ≤ B ∧ ∀ g : 𝓢(E, ℂ), Λ (g.toLp p μ) = S g := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  set e : 𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ p μ := (SchwartzMap.toLpCLM ℂ ℂ p μ).toLinearMap
  have he : DenseRange e := by
    have hcoe : ⇑e = ⇑(SchwartzMap.toLpCLM ℝ ℂ p μ) := by
      ext g : 1
      simp [e]
    rw [DenseRange, hcoe]
    exact SchwartzMap.denseRange_toLpCLM hp_top
  have hS' : ∀ g, ‖S g‖ ≤ B * ‖e g‖ := fun g ↦ by simpa [e] using hS g
  refine ⟨S.extendOfNorm e, (S.extendOfNorm e).opNorm_le_bound hB
    (LinearMap.norm_extendOfNorm_apply_le he B hS'), fun g ↦ ?_⟩
  simpa [e] using LinearMap.extendOfNorm_eq he ⟨B, hS'⟩ g

/-- The case `1 < p < ∞` of `TemperedDistribution.exists_eq_toTemperedDistribution_and_norm_le`,
from the duality `(Lᵖ)^* = Lᵠ`. -/
private theorem exists_eq_toTemperedDistribution_and_norm_le_of_one_lt (hp : 1 < p)
    (hp_top : p ≠ ∞) (u : 𝓢'(E, ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ g : 𝓢(E, ℂ), ‖u g‖ ≤ B * ‖g.toLp p μ‖) :
    ∃ h : Lp ℂ q μ, (h : 𝓢'(E, ℂ)) = u ∧ ‖h‖ ≤ B := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  -- Extend `u` from the dense Schwartz functions to a functional `Λ` on `Lᵖ`.
  obtain ⟨Λ, hΛ, hΛu⟩ := exists_strongDual_apply_toLp_eq hp_top (u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) hB hu
  -- `Λ` is integration against some `h ∈ Lᵠ`, which represents `u`.
  refine ⟨(Lp.dualEquiv ℂ μ q p hp hp_top).symm Λ, ?_, by simpa using hΛ⟩
  ext g
  rw [Lp.toTemperedDistribution_apply_eq_toDual_apply (p := p), ← Lp.coe_dualEquiv hp hp_top,
    LinearIsometryEquiv.apply_symm_apply, hΛu]
  rfl

omit [FiniteDimensional ℝ E] [μ.HasTemperateGrowth] in
/-- **Representing `u` through the weighted measure.** Let `w` and `w' = 1 / w` have temperate
growth, with `w` real and nonnegative, and let `ν = w μ` be finite. If a functional `Λ` on `L¹(ν)`
agrees with `g ↦ u (w g)` on the Schwartz functions, then `u` is integration against the density
`h ∈ L^∞(ν)` of `Λ` with respect to `μ`: `u φ = u (w (w' φ)) = ∫ h w' φ dν = ∫ h φ dμ`. -/
private theorem apply_eq_integral_dualOneEquiv_symm {u : 𝓢'(E, ℂ)} {w w' : E → ℂ}
    (hw : w.HasTemperateGrowth) (hw' : w'.HasTemperateGrowth) (hww' : ∀ x, w x * w' x = 1)
    (hwn : ∀ x, (‖w x‖ : ℂ) = w x) {ν : Measure E}
    (hν : ν = μ.withDensity fun x ↦ (‖w x‖₊ : ℝ≥0∞)) [IsFiniteMeasure ν]
    (Λ : StrongDual ℂ (Lp ℂ 1 ν))
    (hΛu : ∀ g : 𝓢(E, ℂ), Λ (g.toLp 1 ν) = u (SchwartzMap.smulLeftCLM ℂ w g)) (φ : 𝓢(E, ℂ)) :
    u φ = ∫ x, φ x * (Lp.dualOneEquiv ℂ ν).symm Λ x ∂μ := by
  set h := (Lp.dualOneEquiv ℂ ν).symm Λ
  have hφ : SchwartzMap.smulLeftCLM ℂ w (SchwartzMap.smulLeftCLM ℂ w' φ) = φ := by
    ext x
    simp [SchwartzMap.smulLeftCLM_apply_apply hw, SchwartzMap.smulLeftCLM_apply_apply hw',
      ← mul_assoc, hww']
  have hint : u φ = ∫ x, h x * (w' x * φ x) ∂ν := by
    conv_lhs => rw [← hφ, ← hΛu, ← Lp.integral_dualOneEquiv_symm_mul]
    refine integral_congr_ae ?_
    filter_upwards [(SchwartzMap.smulLeftCLM ℂ w' φ).coeFn_toLp 1 ν] with x hx
    rw [hx, SchwartzMap.smulLeftCLM_apply_apply hw', smul_eq_mul]
  have hwd := integral_withDensity_eq_integral_smul (μ := μ) (f := fun x ↦ ‖w x‖₊)
    hw.1.continuous.nnNorm.measurable fun x ↦ h x * (w' x * φ x)
  simp only [← hν] at hwd
  rw [hint, hwd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [NNReal.smul_def, coe_nnNorm, Complex.real_smul, hwn]
  linear_combination (h x * φ x) * hww' x

/-- The case `p = 1` of `TemperedDistribution.exists_eq_toTemperedDistribution_and_norm_le`. Take
a weight `0 < w ≤ 1` integrable for `μ` such that `w` and `1 / w` have temperate growth
(`MeasureTheory.Measure.HasTemperateGrowth.exists_integrable_hasTemperateGrowth`). For the finite
measure `ν = w μ` the functional `g ↦ u (w g)` is bounded by `B ‖g‖_{L¹(ν)}`, so it is integration
against some `h` with `‖h‖_{L^∞(ν)} ≤ B`, by the duality `(L¹(ν))^* = L^∞(ν)`
(`MeasureTheory.Lp.dualOneEquiv`). Then `u` is integration against `h` for `μ`, and `μ` and `ν`
have the same null sets. -/
private theorem exists_eq_toTemperedDistribution_and_norm_le_of_one (u : 𝓢'(E, ℂ)) {B : ℝ}
    (hB : 0 ≤ B) (hu : ∀ g : 𝓢(E, ℂ), ‖u g‖ ≤ B * ‖g.toLp 1 μ‖) :
    ∃ h : Lp ℂ ∞ μ, (h : 𝓢'(E, ℂ)) = u ∧ ‖h‖ ≤ B := by
  obtain ⟨w₀, hw₀, hw₀', hw₀1, hw₀i⟩ :=
    Measure.HasTemperateGrowth.exists_integrable_hasTemperateGrowth μ
  -- The weight `w` and its reciprocal `w'`, as complex functions, and `ν = w μ`.
  set w : E → ℂ := fun x ↦ (w₀ x : ℂ)
  set w' : E → ℂ := fun x ↦ ((w₀ x)⁻¹ : ℂ)
  have hw : w.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp hw₀
  have hw' : w'.HasTemperateGrowth := by
    simpa [w', Function.comp_def] using Complex.hasTemperateGrowth_ofReal.comp hw₀'
  have hwm : AEStronglyMeasurable w μ := hw.1.continuous.aestronglyMeasurable
  set ν := μ.withDensity fun x ↦ (‖w x‖₊ : ℝ≥0∞) with hν
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity (hw₀i.ofReal (𝕜 := ℂ)).hasFiniteIntegral.ne
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous'
    hw.1.continuous.nnNorm.measurable.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa [w] using (hw₀1 x).1.ne')
  -- `g ↦ u (w g)` is bounded on `L¹(ν)`, so it is integration against some `h ∈ L^∞(ν)`.
  obtain ⟨Λ, hΛ, hΛu⟩ := exists_strongDual_apply_toLp_eq (μ := ν) ENNReal.one_ne_top
    ((u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) ∘ₗ (SchwartzMap.smulLeftCLM ℂ w).toLinearMap) hB fun g ↦ by
      refine (hu (SchwartzMap.smulLeftCLM ℂ w g)).trans_eq ?_
      rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, SchwartzMap.smulLeftCLM_apply hw]
      have := eLpNorm_smul_eq_eLpNorm_withDensity hwm g.continuous.aestronglyMeasurable
        ENNReal.one_ne_top
      simp only [ENNReal.toReal_one, ENNReal.rpow_one, eNorm_eq_nnNorm, ← hν] at this
      rw [← this]
      rfl
  set h := (Lp.dualOneEquiv ℂ ν).symm Λ
  have hle : eLpNorm h ∞ μ ≤ eLpNorm h ∞ ν := by
    rw [eLpNorm_exponent_top ((Lp.aestronglyMeasurable h).mono_ac hμν),
      eLpNorm_exponent_top (Lp.aestronglyMeasurable h)]
    exact eLpNormEssSup_mono_measure _ hμν
  have hh : MemLp h ∞ μ := memLp_iff.2 (hle.trans_lt (Lp.memLp h))
  refine ⟨hh.toLp h, ?_, ?_⟩
  · ext φ
    rw [Lp.toTemperedDistribution_apply, apply_eq_integral_dualOneEquiv_symm hw hw'
      (fun x ↦ by simp [w, w', (hw₀1 x).1.ne'])
      (fun x ↦ by simp [w, Real.norm_of_nonneg (hw₀1 x).1.le]) hν Λ (fun g ↦ by rw [hΛu]; rfl)]
    refine integral_congr_ae ?_
    filter_upwards [hh.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul]
  · rw [Lp.norm_toLp]
    refine (ENNReal.toReal_mono (Lp.memLp h).ne hle).trans ?_
    rw [← Lp.norm_def, LinearIsometryEquiv.norm_map]
    exact hΛ

/-- **Distributions bounded in `Lᵖ` are `Lᵠ` functions.** For `1 ≤ p < ∞` and `q` Hölder
conjugate to `p`, a tempered distribution `u` with `‖u g‖ ≤ B ‖g‖_p` for every Schwartz function
`g` is the tempered distribution of some `h ∈ Lᵠ(μ)` with `‖h‖_q ≤ B`. -/
theorem exists_eq_toTemperedDistribution_and_norm_le (hp_top : p ≠ ∞)
    (u : 𝓢'(E, ℂ)) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ g : 𝓢(E, ℂ), ‖u g‖ ≤ B * ‖g.toLp p μ‖) :
    ∃ h : Lp ℂ q μ, (h : 𝓢'(E, ℂ)) = u ∧ ‖h‖ ≤ B := by
  rcases (Fact.out : 1 ≤ p).eq_or_lt with rfl | hp
  · obtain rfl : q = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q 1).2 rfl
    exact exists_eq_toTemperedDistribution_and_norm_le_of_one u hB hu
  · exact exists_eq_toTemperedDistribution_and_norm_le_of_one_lt hp hp_top u hB hu

end TemperedDistribution
