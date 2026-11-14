/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.MeasureTheory.Measure.FiniteMeasure.Equicontinuous
import TauCeti.MeasureTheory.OptimalTransport.Entropic.SchroedingerSystem
import TauCeti.Topology.Instances.ENNReal
import TauCeti.Topology.MetricSpace.Equicontinuity

/-!
# Separate convexity, potential regularity, and weak continuity of entropic optimal transport

For a fixed temperature `ε` and cost `c`, the entropically regularised transport cost
`TauCeti.entropicTransportCost c ε μ ν` is separately convex in each marginal: mixing couplings
`π₀ ∈ Π(μ₀, ν)` and `π₁ ∈ Π(μ₁, ν)` mixes the reference products `μ₀ ⊗ ν` and `μ₁ ⊗ ν` with the
same weights, so joint convexity of relative entropy
(`TauCeti.klDiv_smul_add_smul_smul_add_smul_le`) bounds the regularised cost of the mixture.

At positive temperature and for a bounded cost `c ≤ B`, the `c`-softmin operator

`(S_ν ψ)(x) = -ε * log ∫ exp ((ψ(y) - c(x, y)) / ε) dν(y)`

turns any bounded measurable dual maximiser `(φ₀, ψ₀)` into a normalised pair `(φ, ψ)` of
Schrödinger potentials that still attains `(entropicTransportCost c ε μ ν).toReal`, satisfies the
marginal equation `∫ exp ((φ(x) + ψ(y) - c(x, y)) / ε) dμ(x) = 1` at *every* point `y : Y`, is
bounded by `B` and `2 * B` with `φ(x) + ψ(y) ≤ 2 * B`, and inherits every uniform coordinate
oscillation bound of `(c ·).toReal`.

Evaluating weak duality for a perturbed pair `(μ', ν')` at `(φ, ψ)` and substituting the pointwise
marginal identity `1 = ∫ G(x, y) dμ(x)` isolates the perturbation into marginal differences of
potentials and Gibbs slices. On compact spaces, for a continuous finite cost, the regularised
potentials and Gibbs slices are uniformly bounded and equicontinuous across all marginal pairs;
Ranga Rao's uniform weak convergence theorem
(`MeasureTheory.ProbabilityMeasure.tendstoUniformly_integral_of_equicontinuous`) then makes
`entropicTransportCost c ε` jointly continuous for the weak topology on
`ProbabilityMeasure X × ProbabilityMeasure Y`.

## Main statements

* `TauCeti.entropicTransportCost_smul_add_smul_left_le` and
  `TauCeti.entropicTransportCost_smul_add_smul_right_le`: separate convexity of
  `entropicTransportCost` in `ℝ≥0∞` for finite measures and arbitrary costs.
* `TauCeti.toReal_entropicTransportCost_smul_add_smul_left_le` and
  `TauCeti.toReal_entropicTransportCost_smul_add_smul_right_le`: the real-valued forms.
* `TauCeti.exists_regularized_entropicPotentials` and
  `TauCeti.exists_continuous_entropicDualValue_eq`: dual attainment by normalised `c`-softmin
  potentials bounded by `B` and `2 * B`, with `φ x + ψ y ≤ 2 * B`, coordinate oscillation
  inheritance, and the pointwise marginal identity (measurable in general, continuous on compact
  spaces).
* `TauCeti.continuous_toReal_entropicTransportCost` and
  `TauCeti.continuous_entropicTransportCost`: joint weak continuity on compact spaces.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*, AISTATS 2019,
  Proposition 2, for separate convexity and weak continuity of entropic transport.
-/

public section

noncomputable section

open Filter InformationTheory MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### Separate convexity in each marginal -/

section Convexity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **Convexity of entropic optimal transport in the first marginal.** For finite measures and
nonnegative weights summing to `1`, the regularised transport cost out of `a • μ₀ + b • μ₁` is at
most the weighted sum of the regularised transport costs out of `μ₀` and `μ₁`. No measurability of
the cost or normalisation of the measures is required. -/
theorem entropicTransportCost_smul_add_smul_left_le {μ₀ μ₁ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁] [IsFiniteMeasure ν] {a b : ℝ≥0} (hab : a + b = 1)
    (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) :
    entropicTransportCost c ε (a • μ₀ + b • μ₁) ν ≤
      a * entropicTransportCost c ε μ₀ ν + b * entropicTransportCost c ε μ₁ ν := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 1 := by simpa using hab
    simp [hb]
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a = 1 := by simpa using hab
    simp [ha]
  have ha' : (a : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 ha
  have hb' : (b : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hb
  by_cases h₀ : entropicTransportCost c ε μ₀ ν = ∞
  · simp [h₀, ENNReal.mul_top ha']
  by_cases h₁ : entropicTransportCost c ε μ₁ ν = ∞
  · simp [h₁, ENNReal.mul_top hb']
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
  have hδ' : (0 : ℝ≥0∞) < δ := ENNReal.coe_pos.2 hδ
  obtain ⟨π₀, hπ₀, hlt₀⟩ := entropicTransportCost_lt_iff.1
    (ENNReal.lt_add_right h₀ hδ'.ne')
  obtain ⟨π₁, hπ₁, hlt₁⟩ := entropicTransportCost_lt_iff.1
    (ENNReal.lt_add_right h₁ hδ'.ne')
  have := hπ₀.isFiniteMeasure
  have := hπ₁.isFiniteMeasure
  have hπ : IsCoupling (a • π₀ + b • π₁) (a • μ₀ + b • μ₁) ν := by
    have h := (hπ₀.smul (a : ℝ≥0∞)).add (hπ₁.smul (b : ℝ≥0∞))
    have hν : (a : ℝ≥0∞) • ν + (b : ℝ≥0∞) • ν = ν := by
      rw [← add_smul, ← ENNReal.coe_add, hab, ENNReal.coe_one, one_smul]
    rw [hν, Measure.coe_nnreal_smul, Measure.coe_nnreal_smul,
      Measure.coe_nnreal_smul, Measure.coe_nnreal_smul] at h
    exact h
  have hprod : (a • μ₀ + b • μ₁).prod ν = a • (μ₀.prod ν) + b • (μ₁.prod ν) := by
    rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]
  calc entropicTransportCost c ε (a • μ₀ + b • μ₁) ν
      ≤ ∫⁻ z, c z ∂(a • π₀ + b • π₁) + ε * klDiv (a • π₀ + b • π₁) ((a • μ₀ + b • μ₁).prod ν) :=
        entropicTransportCost_le hπ c ε
    _ ≤ a * (∫⁻ z, c z ∂π₀ + ε * klDiv π₀ (μ₀.prod ν)) +
          b * (∫⁻ z, c z ∂π₁ + ε * klDiv π₁ (μ₁.prod ν)) := by
        rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, hprod,
          ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        calc ((a : ℝ≥0∞) * ∫⁻ z, c z ∂π₀ + b * ∫⁻ z, c z ∂π₁) +
              ε * klDiv (a • π₀ + b • π₁) (a • μ₀.prod ν + b • μ₁.prod ν)
            ≤ (a * ∫⁻ z, c z ∂π₀ + b * ∫⁻ z, c z ∂π₁) +
                ε * (a * klDiv π₀ (μ₀.prod ν) + b * klDiv π₁ (μ₁.prod ν)) := by
              gcongr
              exact klDiv_smul_add_smul_smul_add_smul_le a b
          _ = _ := by ring
    _ ≤ a * (entropicTransportCost c ε μ₀ ν + δ) + b * (entropicTransportCost c ε μ₁ ν + δ) := by
        gcongr
    _ = a * entropicTransportCost c ε μ₀ ν + b * entropicTransportCost c ε μ₁ ν + δ := by
        have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
        calc a * (entropicTransportCost c ε μ₀ ν + δ) + b * (entropicTransportCost c ε μ₁ ν + δ)
            = a * entropicTransportCost c ε μ₀ ν + b * entropicTransportCost c ε μ₁ ν +
                ((a : ℝ≥0∞) + b) * δ := by ring
          _ = _ := by rw [hab', one_mul]

/-- **Convexity of entropic optimal transport in the second marginal.** -/
theorem entropicTransportCost_smul_add_smul_right_le {μ : Measure X} {ν₀ ν₁ : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] {a b : ℝ≥0} (hab : a + b = 1)
    (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) :
    entropicTransportCost c ε μ (a • ν₀ + b • ν₁) ≤
      a * entropicTransportCost c ε μ ν₀ + b * entropicTransportCost c ε μ ν₁ := by
  rw [← entropicTransportCost_comp_swap c ε (a • ν₀ + b • ν₁),
    ← entropicTransportCost_comp_swap c ε ν₀, ← entropicTransportCost_comp_swap c ε ν₁]
  exact entropicTransportCost_smul_add_smul_left_le hab (c ∘ Prod.swap) ε

/-- **Convexity of real-valued entropic optimal transport in the first marginal.** -/
theorem toReal_entropicTransportCost_smul_add_smul_left_le {μ₀ μ₁ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁] [IsFiniteMeasure ν] {a b : ℝ≥0} (hab : a + b = 1)
    {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} (h₀ : entropicTransportCost c ε μ₀ ν ≠ ∞)
    (h₁ : entropicTransportCost c ε μ₁ ν ≠ ∞) :
    (entropicTransportCost c ε (a • μ₀ + b • μ₁) ν).toReal ≤
      a * (entropicTransportCost c ε μ₀ ν).toReal +
        b * (entropicTransportCost c ε μ₁ ν).toReal := by
  have hrhs : (a : ℝ≥0∞) * entropicTransportCost c ε μ₀ ν +
      b * entropicTransportCost c ε μ₁ ν ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top h₀,
      ENNReal.mul_ne_top ENNReal.coe_ne_top h₁⟩
  have hle := ENNReal.toReal_mono hrhs (entropicTransportCost_smul_add_smul_left_le hab c ε)
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top h₀)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top h₁), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.coe_toReal] at hle

/-- **Convexity of real-valued entropic optimal transport in the second marginal.** -/
theorem toReal_entropicTransportCost_smul_add_smul_right_le {μ : Measure X} {ν₀ ν₁ : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] {a b : ℝ≥0} (hab : a + b = 1)
    {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} (h₀ : entropicTransportCost c ε μ ν₀ ≠ ∞)
    (h₁ : entropicTransportCost c ε μ ν₁ ≠ ∞) :
    (entropicTransportCost c ε μ (a • ν₀ + b • ν₁)).toReal ≤
      a * (entropicTransportCost c ε μ ν₀).toReal +
        b * (entropicTransportCost c ε μ ν₁).toReal := by
  rw [← entropicTransportCost_comp_swap c ε (a • ν₀ + b • ν₁),
    ← entropicTransportCost_comp_swap c ε ν₀, ← entropicTransportCost_comp_swap c ε ν₁]
  exact toReal_entropicTransportCost_smul_add_smul_left_le hab
    (by rwa [entropicTransportCost_comp_swap]) (by rwa [entropicTransportCost_comp_swap])

end Convexity

/-! ### Regularised Schrödinger potentials via the `c`-softmin operator -/

section Softmin

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0}
  {μ μ' : Measure X} {ν ν' : Measure Y}

/-- The `c`-softmin transform `-ε * log ∫ exp (-(c (x, y)).toReal / ε + ψ y / ε) dν(y)` of a
potential `ψ`, defined through the Sinkhorn half-step `TauCeti.logIntegralExp`. -/
private def entropicSoftmin (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (ν : Measure Y) (ψ : Y → ℝ) (x : X) :
    ℝ :=
  -(ε : ℝ) * logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x

private theorem measurable_entropicSoftmin [SFinite ν] (hc : Measurable c) {ψ : Y → ℝ}
    (hψ : Measurable ψ) : Measurable (entropicSoftmin c ε ν ψ) :=
  measurable_const.mul
    (measurable_logIntegralExp (h := fun z ↦ -(c z).toReal / ε)
      (hc.ennreal_toReal.neg.div_const _) (hψ.div_const _))

private theorem integrable_exp_neg_toReal_add [IsFiniteMeasure ν] (hc : Measurable c)
    {ψ : Y → ℝ} {C : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, |ψ y| ≤ C) (x : X) :
    Integrable (fun y ↦ Real.exp (-(c (x, y)).toReal / ε + ψ y / ε)) ν :=
  integrable_exp_add_of_le (h := fun z ↦ -(c z).toReal / ε) (ψ := fun y ↦ ψ y / ε)
    (M := 0) (C := C / ε) (hc.ennreal_toReal.neg.div_const _)
    (fun _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ENNReal.toReal_nonneg) ε.coe_nonneg)
    (hψ.div_const _)
    (fun y ↦ div_le_div_of_nonneg_right (le_of_abs_le (hψC y)) ε.coe_nonneg) x

private theorem abs_entropicSoftmin_le [IsProbabilityMeasure ν] (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {ψ : Y → ℝ} {C : ℝ} (hψ : Measurable ψ)
    (hψC : ∀ y, |ψ y| ≤ C) (x : X) :
    |entropicSoftmin c ε ν ψ x| ≤ C + B := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hlog := abs_logIntegralExp_le (ν := ν) (h := fun z ↦ -(c z).toReal / ε)
    (ψ := fun y ↦ ψ y / ε) (IsProbabilityMeasure.ne_zero ν)
    (hc.ennreal_toReal.neg.div_const _)
    (M := (B : ℝ) / ε) (fun z ↦ by
      rw [abs_div, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_pos hεpos]
      exact div_le_div_of_nonneg_right (ENNReal.toReal_le_coe_of_le_coe (hcB z)) hεpos.le)
    (hψ.div_const _) (C := C / ε) (fun y ↦ by
      rw [abs_div, abs_of_pos hεpos]
      exact div_le_div_of_nonneg_right (hψC y) hεpos.le) x
  rw [probReal_univ, Real.log_one, abs_zero, add_zero] at hlog
  rw [entropicSoftmin, abs_mul, abs_neg, abs_of_pos hεpos]
  calc (ε : ℝ) * |logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x|
      ≤ ε * ((B : ℝ) / ε + C / ε) := mul_le_mul_of_nonneg_left hlog hεpos.le
    _ = C + B := by
        rw [← add_div, mul_div_cancel₀ _ hεpos.ne', add_comm]

/-- The `c`-softmin inherits every uniform oscillation bound of `(c ·).toReal` in its first
variable, independently of the measure `ν`, the temperature `ε`, and the potential `ψ`. -/
private theorem abs_entropicSoftmin_sub_le [IsProbabilityMeasure ν] (hc : Measurable c)
    (hε : ε ≠ 0) {ψ : Y → ℝ} {C : ℝ} (hψ : Measurable ψ)
    (hψC : ∀ y, |ψ y| ≤ C) {x₁ x₂ : X} {δ : ℝ}
    (hosc : ∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) :
    |entropicSoftmin c ε ν ψ x₁ - entropicSoftmin c ε ν ψ x₂| ≤ δ := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hlog := abs_logIntegralExp_sub_le (ν := ν) (h := fun z ↦ -(c z).toReal / ε)
    (ψ := fun y ↦ ψ y / ε) (IsProbabilityMeasure.ne_zero ν)
    (hc.ennreal_toReal.neg.div_const _) (M := 0)
    (fun _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ENNReal.toReal_nonneg) hεpos.le)
    (hψ.div_const _) (C := C / ε)
    (fun y ↦ div_le_div_of_nonneg_right (le_of_abs_le (hψC y)) hεpos.le)
    (a₁ := x₁) (a₂ := x₂) (δ := δ / ε) fun y ↦ by
      have hrw : -(c (x₁, y)).toReal / (ε : ℝ) - -(c (x₂, y)).toReal / ε =
          -((c (x₁, y)).toReal - (c (x₂, y)).toReal) / ε := by ring
      rw [hrw, abs_div, abs_neg, abs_of_pos hεpos]
      exact div_le_div_of_nonneg_right (hosc y) hεpos.le
  have hsub : entropicSoftmin c ε ν ψ x₁ - entropicSoftmin c ε ν ψ x₂ =
      -(ε : ℝ) * (logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x₁ -
        logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x₂) := by
    simp only [entropicSoftmin]
    ring
  rw [hsub, abs_mul, abs_neg, abs_of_pos hεpos]
  exact (mul_le_mul_of_nonneg_left hlog hεpos.le).trans_eq (mul_div_cancel₀ _ hεpos.ne')

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- When `c (x, y) ≠ ∞`, the Gibbs factor splits into its `x`-potential factor and its tilted cost
kernel. -/
private theorem entropicGibbsFactor_eq_exp_mul_exp {φ : X → ℝ} {ψ : Y → ℝ} {x : X} {y : Y}
    (hfin : c (x, y) ≠ ∞) :
    entropicGibbsFactor c ε φ ψ (x, y) =
      Real.exp (φ x / ε) * Real.exp (-(c (x, y)).toReal / ε + ψ y / ε) := by
  rw [entropicGibbsFactor_of_ne_top hfin, ← Real.exp_add]
  congr 1
  ring

/-- At `φ = entropicSoftmin c ε ν ψ`, the Gibbs slice integrates to `1` against `ν` at *every*
point `x : X`. -/
private theorem integral_entropicGibbsFactor_entropicSoftmin [IsProbabilityMeasure ν]
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {ψ : Y → ℝ} {C : ℝ}
    (hψ : Measurable ψ) (hψC : ∀ y, |ψ y| ≤ C) (x : X) :
    ∫ y, entropicGibbsFactor c ε (entropicSoftmin c ε ν ψ) ψ (x, y) ∂ν = 1 := by
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  have hfin : ∀ y, c (x, y) ≠ ∞ := fun y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB (x, y))
  have hint := integrable_exp_neg_toReal_add (ν := ν) (ε := ε) hc hψ hψC x
  have hZpos : 0 < ∫ y, Real.exp (-(c (x, y)).toReal / ε + ψ y / ε) ∂ν := integral_exp_pos hint
  simp_rw [entropicGibbsFactor_eq_exp_mul_exp (hfin _)]
  rw [integral_const_mul, entropicSoftmin, logIntegralExp_def, neg_mul, neg_div,
    mul_div_cancel_left₀ _ hε', Real.exp_neg, Real.exp_log hZpos, inv_mul_cancel₀ hZpos.ne']

/-- Replacing `φ` by `entropicSoftmin c ε ν ψ` does not decrease `entropicDualValue`. -/
private theorem entropicDualValue_le_entropicSoftmin_left [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {φ : X → ℝ} {ψ : Y → ℝ} {Cφ Cψ : ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφC : ∀ x, |φ x| ≤ Cφ) (hψC : ∀ y, |ψ y| ≤ Cψ) :
    entropicDualValue c ε μ ν φ ψ ≤
      entropicDualValue c ε μ ν (entropicSoftmin c ε ν ψ) ψ := by
  -- Step 1: Integrability of `φ`, `φ₁ = entropicSoftmin c ε ν ψ`, `exp ((φ - φ₁) / ε)`, and both
  -- Gibbs factors.
  set φ₁ := entropicSoftmin c ε ν ψ
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hψC' : ∀ y, |ψ y| ≤ max Cψ 0 := fun y ↦ (hψC y).trans (le_max_left _ _)
  have hφ₁m : Measurable φ₁ := measurable_entropicSoftmin hc hψ
  have hφ₁C : ∀ x, |φ₁ x| ≤ max Cψ 0 + B := abs_entropicSoftmin_le hc hcB hε hψ hψC'
  have hφi : Integrable φ μ := .of_bound hφ.aestronglyMeasurable Cφ (ae_of_all _ hφC)
  have hφ₁i : Integrable φ₁ μ :=
    .of_bound hφ₁m.aestronglyMeasurable (max Cψ 0 + B) (ae_of_all _ hφ₁C)
  have hexp_diff : Integrable (fun x ↦ Real.exp ((φ x - φ₁ x) / ε)) μ :=
    .of_bound ((hφ.sub hφ₁m).div_const _).exp.aestronglyMeasurable
      (Real.exp ((Cφ + (max Cψ 0 + B)) / ε)) (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        refine div_le_div_of_nonneg_right ?_ hεpos.le
        linarith [le_of_abs_le (hφC x), (abs_le.1 (hφ₁C x)).1])
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ hψ
    (fun x ↦ le_of_abs_le (hφC x)) (fun y ↦ le_of_abs_le (hψC y))
  have hexp₁ := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ₁m hψ
    (fun x ↦ le_of_abs_le (hφ₁C x)) (fun y ↦ le_of_abs_le (hψC' y))
  -- Step 2: At `φ₁` the Gibbs penalty vanishes, while at `φ` each `x`-slice equals
  -- `exp ((φ x - φ₁ x) / ε)`.
  have hint₁ : ∫ z, (entropicGibbsFactor c ε φ₁ ψ z - 1) ∂μ.prod ν = 0 := by
    rw [integral_sub hexp₁ (integrable_const _), integral_prod _ hexp₁]
    simp [φ₁, integral_entropicGibbsFactor_entropicSoftmin hc hcB hε hψ hψC']
  have hslice (x : X) : ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν =
      Real.exp ((φ x - φ₁ x) / ε) := by
    have hfin : ∀ y, c (x, y) ≠ ∞ := fun y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB (x, y))
    have hint := integrable_exp_neg_toReal_add (ν := ν) (ε := ε) hc hψ hψC x
    have hZpos : 0 < ∫ y, Real.exp (-(c (x, y)).toReal / ε + ψ y / ε) ∂ν := integral_exp_pos hint
    simp_rw [entropicGibbsFactor_eq_exp_mul_exp (hfin _)]
    rw [integral_const_mul, ← Real.exp_log hZpos, ← Real.exp_add]
    congr 1
    simp only [φ₁, entropicSoftmin, logIntegralExp_def]
    field_simp
    ring
  have hpen : ∫ z, (entropicGibbsFactor c ε φ ψ z - 1) ∂μ.prod ν =
      ∫ x, (Real.exp ((φ x - φ₁ x) / ε) - 1) ∂μ := by
    rw [integral_sub hexp (integrable_const _), integral_prod _ hexp,
      integral_sub hexp_diff (integrable_const _)]
    simp_rw [hslice]
    simp
  -- Step 3: Integrate the pointwise inequality `φ x - ε * (exp ((φ x - φ₁ x) / ε) - 1) ≤ φ₁ x`.
  have hpt : ∫ x, (φ x - ε * (Real.exp ((φ x - φ₁ x) / ε) - 1)) ∂μ ≤ ∫ x, φ₁ x ∂μ := by
    have hexp_sub1 : Integrable (fun x ↦ Real.exp ((φ x - φ₁ x) / ε) - 1) μ :=
      hexp_diff.sub (integrable_const _)
    refine integral_mono (hφi.sub (hexp_sub1.const_mul _)) hφ₁i fun x ↦ ?_
    have hexp_le := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((φ x - φ₁ x) / ε)) hεpos.le
    rw [mul_add, mul_div_cancel₀ _ hεpos.ne', mul_one] at hexp_le
    linarith
  have hrew : ∫ x, φ x ∂μ - ε * ∫ x, (Real.exp ((φ x - φ₁ x) / ε) - 1) ∂μ =
      ∫ x, (φ x - ε * (Real.exp ((φ x - φ₁ x) / ε) - 1)) ∂μ := by
    have hexp_sub1 : Integrable (fun x ↦ Real.exp ((φ x - φ₁ x) / ε) - 1) μ :=
      hexp_diff.sub (integrable_const _)
    rw [integral_sub hφi (hexp_sub1.const_mul _), integral_const_mul]
  rw [entropicDualValue_def, entropicDualValue_def, kantorovichDualValue_def,
    kantorovichDualValue_def, hint₁, hpen]
  linarith

/-- Bundled regularity, normalisation, and optimality properties of a `c`-softmin Schrödinger
potential pair `(φ, ψ)` for a cost bounded by `B`. -/
private structure IsRegularizedPotentialPair (c : X × Y → ℝ≥0∞) (ε B : ℝ≥0)
    (μ : Measure X) (ν : Measure Y) (φ : X → ℝ) (ψ : Y → ℝ) : Prop where
  measurable_left : Measurable φ
  measurable_right : Measurable ψ
  abs_left_le : ∀ x, |φ x| ≤ B
  abs_right_le : ∀ y, |ψ y| ≤ 2 * B
  add_le : ∀ x y, φ x + ψ y ≤ 2 * B
  abs_sub_left_le : ∀ x₁ x₂ δ, 0 ≤ δ →
    (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) → |φ x₁ - φ x₂| ≤ δ
  abs_sub_right_le : ∀ y₁ y₂ δ, 0 ≤ δ →
    (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) → |ψ y₁ - ψ y₂| ≤ δ
  integral_gibbs_eq_one : ∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1
  dualValue_eq : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal

private theorem exists_isRegularizedPotentialPair [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), IsRegularizedPotentialPair c ε B μ ν φ ψ := by
  -- Step 1: Take any bounded measurable dual maximiser `(φ₀, ψ₀)` and apply one `c`-softmin
  -- half-step on `X`, recentered at a base point `x₀`, followed by one half-step on `Y`.
  obtain ⟨φ₀, ψ₀, C₀, hφ₀, hψ₀, hφ₀C, hψ₀C, hval₀⟩ :=
    exists_entropicDualValue_eq_toReal_entropicTransportCost (μ := μ) (ν := ν) hc hcB hε
  have hψ₀C' : ∀ y, |ψ₀ y| ≤ max C₀ 0 := fun y ↦ (hψ₀C y).trans (le_max_left _ _)
  set φ₁ := entropicSoftmin c ε ν ψ₀
  have x₀ : X := μ.nonempty_of_neZero.some
  set a : ℝ := φ₁ x₀
  set φ : X → ℝ := fun x ↦ φ₁ x - a
  set ψ₁ : Y → ℝ := fun y ↦ ψ₀ y + a
  set ψ : Y → ℝ := entropicSoftmin (c ∘ Prod.swap) ε μ φ
  have hcs : Measurable (c ∘ Prod.swap) := hc.comp measurable_swap
  have hcsB : ∀ z, (c ∘ Prod.swap) z ≤ B := fun z ↦ hcB z.swap
  have hφ₁m : Measurable φ₁ := measurable_entropicSoftmin hc hψ₀
  have hφm : Measurable φ := hφ₁m.sub_const a
  have hψ₁m : Measurable ψ₁ := hψ₀.add_const a
  have hψm : Measurable ψ := measurable_entropicSoftmin hcs hφm
  -- Step 2: Oscillation inheritance gives `|φ| ≤ B` (since `φ x₀ = 0`), `|ψ| ≤ 2 * B`, and
  -- `φ x + ψ y ≤ 2 * B`.
  have hosc_B : ∀ x₁ x₂ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ B := fun x₁ x₂ y ↦ by
    rw [abs_le]
    have h1 := ENNReal.toReal_le_coe_of_le_coe (hcB (x₁, y))
    have h2 := ENNReal.toReal_le_coe_of_le_coe (hcB (x₂, y))
    exact ⟨by linarith [(c (x₁, y)).toReal_nonneg], by linarith [(c (x₂, y)).toReal_nonneg]⟩
  have hφ_osc : ∀ x₁ x₂ δ, 0 ≤ δ →
      (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) → |φ x₁ - φ x₂| ≤ δ := by
    intro x₁ x₂ δ _ h
    simpa only [φ, sub_sub_sub_cancel_right] using
      abs_entropicSoftmin_sub_le (ν := ν) hc hε hψ₀ hψ₀C' h
  have hφB : ∀ x, |φ x| ≤ B := fun x ↦ by
    simpa only [φ, a, sub_self, sub_zero] using hφ_osc x x₀ B B.coe_nonneg (hosc_B x x₀)
  have hψB : ∀ y, |ψ y| ≤ 2 * B := fun y ↦ by
    simpa only [two_mul] using abs_entropicSoftmin_le (ν := μ) hcs hcsB hε hφm hφB y
  have hφψ_sum : ∀ x y, φ x + ψ y ≤ 2 * B := fun x y ↦ by
    have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
    have hint := integrable_exp_neg_toReal_add (ν := μ) (ε := ε) hcs hφm hφB y
    have hlower : Real.exp ((φ x - 2 * B) / ε) ≤
        ∫ x', Real.exp (-((c ∘ Prod.swap) (y, x')).toReal / ε + φ x' / ε) ∂μ := by
      calc Real.exp ((φ x - 2 * B) / ε) = ∫ _, Real.exp ((φ x - 2 * B) / ε) ∂μ := by simp
        _ ≤ ∫ x', Real.exp (-((c ∘ Prod.swap) (y, x')).toReal / ε + φ x' / ε) ∂μ :=
            integral_mono (integrable_const _) hint fun x' ↦ Real.exp_le_exp.2 <| by
              have hdiff : φ x - φ x' ≤ B :=
                (le_abs_self _).trans (hφ_osc x x' B B.coe_nonneg (hosc_B x x'))
              have hc' : ((c ∘ Prod.swap) (y, x')).toReal ≤ B :=
                ENNReal.toReal_le_coe_of_le_coe (hcB (x', y))
              have hrw : -((c ∘ Prod.swap) (y, x')).toReal / (ε : ℝ) + φ x' / ε =
                  (φ x' - ((c ∘ Prod.swap) (y, x')).toReal) / ε := by ring
              rw [hrw]
              exact div_le_div_of_nonneg_right (by linarith) hεpos.le
    have hlog := (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hlower)
    have hmul := mul_le_mul_of_nonneg_left hlog hεpos.le
    rw [mul_div_cancel₀ _ hεpos.ne'] at hmul
    simp only [ψ, entropicSoftmin, logIntegralExp_def]
    linarith
  have hψ_osc : ∀ y₁ y₂ δ, 0 ≤ δ →
      (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) → |ψ y₁ - ψ y₂| ≤ δ :=
    fun y₁ y₂ δ _ h ↦ abs_entropicSoftmin_sub_le (ν := μ) hcs hε hφm hφB h
  -- Step 3: Verify the pointwise `y`-marginal equation and optimality via monotonicity of the
  -- two softmin half-steps and shift invariance of `entropicDualValue`.
  have hslice : ∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1 := fun y ↦ by
    have h := integral_entropicGibbsFactor_entropicSoftmin (ν := μ) hcs hcsB hε hφm hφB y
    simpa only [entropicGibbsFactor_comp_swap, Function.comp_apply, Prod.swap_prod_mk] using h
  have hφ₁C : ∀ x, |φ₁ x| ≤ max C₀ 0 + B := abs_entropicSoftmin_le (ν := ν) hc hcB hε hψ₀ hψ₀C'
  have hψ₁C : ∀ y, |ψ₁ y| ≤ max C₀ 0 + (max C₀ 0 + B) := fun y ↦
    (abs_add_le _ _).trans (add_le_add (hψ₀C' y) (hφ₁C x₀))
  have hval : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
    apply le_antisymm
    · exact entropicDualValue_le_toReal_entropicTransportCost
        (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε
        (.of_bound hφm.aestronglyMeasurable B (ae_of_all _ hφB))
        (.of_bound hψm.aestronglyMeasurable (2 * B) (ae_of_all _ hψB))
        (integrable_entropicGibbsFactor_of_le hc hφm hψm
          (fun x ↦ le_of_abs_le (hφB x)) (fun y ↦ le_of_abs_le (hψB y)))
    · have h1 : (entropicTransportCost c ε μ ν).toReal ≤ entropicDualValue c ε μ ν φ₁ ψ₀ :=
        hval₀ ▸ entropicDualValue_le_entropicSoftmin_left hc hcB hε hφ₀ hψ₀ hφ₀C hψ₀C
      have h2 : entropicDualValue c ε μ ν φ₁ ψ₀ = entropicDualValue c ε μ ν φ ψ₁ := by
        have := entropicDualValue_add_const_sub_const (c := c) (ε := ε) (μ := μ) (ν := ν)
          (.of_bound hφ₁m.aestronglyMeasurable (max C₀ 0 + B) (ae_of_all _ hφ₁C))
          (.of_bound hψ₀.aestronglyMeasurable C₀ (ae_of_all _ hψ₀C)) (by simp) (-a)
        simpa only [φ, ψ₁, sub_eq_add_neg, neg_neg] using this.symm
      have h3 : entropicDualValue c ε μ ν φ ψ₁ ≤ entropicDualValue c ε μ ν φ ψ := by
        rw [← entropicDualValue_comp_swap (c := c), ← entropicDualValue_comp_swap (c := c)]
        exact entropicDualValue_le_entropicSoftmin_left hcs hcsB hε hψ₁m hφm hψ₁C hφB
      exact (h1.trans_eq h2).trans h3
  exact ⟨φ, ψ, ⟨hφm, hψm, hφB, hψB, hφψ_sum, hφ_osc, hψ_osc, hslice, hval⟩⟩

/-- **Existence of normalised `c`-softmin optimal potentials.** For probability measures, a bounded
measurable cost `c ≤ B` and a positive temperature `ε`, there exist measurable potentials `(φ, ψ)`
bounded by `B` and `2 * B` that attain `(entropicTransportCost c ε μ ν).toReal`, satisfy
`φ(x) + ψ(y) ≤ 2 * B` and `∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1` at *every* `y : Y`, and
inherit every uniform coordinate oscillation bound of `(c ·).toReal`. -/
theorem exists_regularized_entropicPotentials [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, |φ x| ≤ B) ∧ (∀ y, |ψ y| ≤ 2 * B) ∧ (∀ x y, φ x + ψ y ≤ 2 * B) ∧
      (∀ x₁ x₂ δ, 0 ≤ δ → (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) →
        |φ x₁ - φ x₂| ≤ δ) ∧
      (∀ y₁ y₂ δ, 0 ≤ δ → (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) →
        |ψ y₁ - ψ y₂| ≤ δ) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨φ, ψ, h⟩ := exists_isRegularizedPotentialPair (μ := μ) (ν := ν) hc hcB hε
  exact ⟨φ, ψ, h.measurable_left, h.measurable_right, h.abs_left_le, h.abs_right_le, h.add_le,
    h.abs_sub_left_le, h.abs_sub_right_le, h.integral_gibbs_eq_one, h.dualValue_eq⟩

/-- **One-sided dual perturbation bound.** When `(φ, ψ)` attains
`(entropicTransportCost c ε μ ν).toReal` and satisfies the pointwise marginal equation
`∫ x, G(x, y) ∂μ = 1` for every `y`, subtracting weak duality at `(μ', ν')` expresses the drop in
optimal value through marginal differences of `φ`, `ψ`, and the `x`-slices of `G`. -/
private theorem IsRegularizedPotentialPair.toReal_entropicTransportCost_sub_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν'] {φ : X → ℝ} {ψ : Y → ℝ}
    (h : IsRegularizedPotentialPair c ε B μ ν φ ψ) (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    (entropicTransportCost c ε μ ν).toReal - (entropicTransportCost c ε μ' ν').toReal ≤
      (∫ x, φ x ∂μ - ∫ x, φ x ∂μ') + (∫ y, ψ y ∂ν - ∫ y, ψ y ∂ν') +
        ε * ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
          ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν' := by
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc
    h.measurable_left h.measurable_right
    (fun x ↦ le_of_abs_le (h.abs_left_le x)) (fun y ↦ le_of_abs_le (h.abs_right_le y))
  have hexp' := integrable_entropicGibbsFactor_of_le (μ := μ') (ν := ν') (ε := ε) hc
    h.measurable_left h.measurable_right
    (fun x ↦ le_of_abs_le (h.abs_left_le x)) (fun y ↦ le_of_abs_le (h.abs_right_le y))
  have hval_eq : (entropicTransportCost c ε μ ν).toReal = ∫ x, φ x ∂μ + ∫ y, ψ y ∂ν := by
    rw [← h.dualValue_eq, entropicDualValue_def, kantorovichDualValue_def,
      integral_sub hexp (integrable_const _), integral_prod_symm _ hexp]
    simp [h.integral_gibbs_eq_one]
  have hdual' := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε
    (.of_bound h.measurable_left.aestronglyMeasurable B (ae_of_all _ h.abs_left_le))
    (.of_bound h.measurable_right.aestronglyMeasurable (2 * B) (ae_of_all _ h.abs_right_le))
    hexp'
  rw [entropicDualValue_def, kantorovichDualValue_def,
    integral_sub hexp' (integrable_const _), integral_prod_symm _ hexp'] at hdual'
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hdual'
  have hpen : ∫ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' ∂ν' - 1 =
      ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
        ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν' := by
    simp_rw [h.integral_gibbs_eq_one]
    rw [integral_sub hexp'.integral_prod_right (integrable_const _)]
    simp
  rw [hval_eq, ← hpen]
  linarith

/-- Quantitative form of `toReal_entropicTransportCost_sub_le` when each of the three marginal
differences is within `η / 3`. -/
private theorem IsRegularizedPotentialPair.toReal_entropicTransportCost_sub_lt
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν'] {φ : X → ℝ} {ψ : Y → ℝ}
    (h : IsRegularizedPotentialPair c ε B μ ν φ ψ) (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) {η : ℝ} (hφ : ∫ x, φ x ∂μ - ∫ x, φ x ∂μ' < η / 3)
    (hψ : ∫ y, ψ y ∂ν - ∫ y, ψ y ∂ν' < η / 3)
    (hG : ∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
      ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ ≤ η / (3 * ε)) :
    (entropicTransportCost c ε μ ν).toReal - (entropicTransportCost c ε μ' ν').toReal < η := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hexp_r := integrable_entropicGibbsFactor_of_le (μ := μ') (ν := ν') (ε := ε) hc
    h.measurable_left h.measurable_right
    (fun x ↦ le_of_abs_le (h.abs_left_le x)) (fun y ↦ le_of_abs_le (h.abs_right_le y))
  have hexp_qr := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν') (ε := ε) hc
    h.measurable_left h.measurable_right
    (fun x ↦ le_of_abs_le (h.abs_left_le x)) (fun y ↦ le_of_abs_le (h.abs_right_le y))
  have hpen : ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
        ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν' ≤ η / (3 * ε) := by
    calc ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
            ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν'
        ≤ ∫ _, η / (3 * ε) ∂ν' :=
          integral_mono (hexp_r.integral_prod_right.sub hexp_qr.integral_prod_right)
            (integrable_const _) hG
      _ = η / (3 * ε) := by simp
  have hmul : (ε : ℝ) * ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
        ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν' ≤ η / 3 := by
    refine (mul_le_mul_of_nonneg_left hpen hεpos.le).trans_eq ?_
    field_simp
  have hpert := h.toReal_entropicTransportCost_sub_le (μ' := μ') (ν' := ν') hc hcB hε
  linarith

end Softmin

/-! ### Joint weak continuity on compact spaces -/

section Compact

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [OpensMeasurableSpace (X × Y)] {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0}

omit [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [OpensMeasurableSpace (X × Y)] in
/-- Equicontinuity in `x` of the Gibbs slices `(q, y) ↦ entropicGibbsFactor c ε (φ q) (ψ q) (·, y)`
for any family of regularised potential pairs. -/
private theorem equicontinuous_entropicGibbsFactor {ι : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : ι → Measure X} {ν : ι → Measure Y} {φ : ι → X → ℝ} {ψ : ι → Y → ℝ}
    (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0)
    (hpair : ∀ q, IsRegularizedPotentialPair c ε B (μ q) (ν q) (φ q) (ψ q)) :
    Equicontinuous
      fun qy : ι × Y ↦ fun x ↦ entropicGibbsFactor c ε (φ qy.1) (ψ qy.1) (x, qy.2) := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  refine Metric.equicontinuous_of_forall_dist_le (hc.ennreal_toReal hfin)
    (L := Real.exp (2 * B / ε) * (2 / ε)) fun x₁ x₂ δ hδ h qy ↦ ?_
  have h' : ∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ := by
    simpa only [Real.dist_eq] using h
  simp only [Real.dist_eq, entropicGibbsFactor_of_ne_top (hfin (x₁, qy.2)),
    entropicGibbsFactor_of_ne_top (hfin (x₂, qy.2))]
  have hexp1 : (φ qy.1 x₁ + ψ qy.1 qy.2 - (c (x₁, qy.2)).toReal) / ε ≤ 2 * B / ε :=
    div_le_div_of_nonneg_right
      (by linarith [(hpair qy.1).add_le x₁ qy.2, (c (x₁, qy.2)).toReal_nonneg]) hεpos.le
  have hexp2 : (φ qy.1 x₂ + ψ qy.1 qy.2 - (c (x₂, qy.2)).toReal) / ε ≤ 2 * B / ε :=
    div_le_div_of_nonneg_right
      (by linarith [(hpair qy.1).add_le x₂ qy.2, (c (x₂, qy.2)).toReal_nonneg]) hεpos.le
  refine (Real.abs_exp_sub_exp_le hexp1 hexp2).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hφd := (hpair qy.1).abs_sub_left_le x₁ x₂ δ hδ h'
  have hcd := h' qy.2
  have hdiff : |(φ qy.1 x₁ + ψ qy.1 qy.2 - (c (x₁, qy.2)).toReal) / ε -
      (φ qy.1 x₂ + ψ qy.1 qy.2 - (c (x₂, qy.2)).toReal) / ε| =
      |(φ qy.1 x₁ - φ qy.1 x₂) - ((c (x₁, qy.2)).toReal - (c (x₂, qy.2)).toReal)| / ε := by
    rw [← sub_div, abs_div, abs_of_pos hεpos]
    congr 2
    ring
  rw [hdiff, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hεpos]
  calc |(φ qy.1 x₁ - φ qy.1 x₂) - ((c (x₁, qy.2)).toReal - (c (x₂, qy.2)).toReal)|
      ≤ |φ qy.1 x₁ - φ qy.1 x₂| + |(c (x₁, qy.2)).toReal - (c (x₂, qy.2)).toReal| := abs_sub _ _
    _ ≤ 2 * δ := by linarith

omit [OpensMeasurableSpace X] [OpensMeasurableSpace Y] in
/-- **Existence of continuous optimal Schrödinger potentials on compact spaces.** For probability
measures on compact spaces, a continuous cost bounded by `B` and a positive temperature `ε`, the
entropic dual problem is attained by continuous `c`-softmin potentials `(φ, ψ)` bounded by `B` and
`2 * B`, with `φ x + ψ y ≤ 2 * B`, inheriting every uniform coordinate oscillation bound of
`(c ·).toReal`, and satisfying `∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1` for every
`y : Y`. -/
theorem exists_continuous_entropicDualValue_eq {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Continuous c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Continuous φ ∧ Continuous ψ ∧
      (∀ x, |φ x| ≤ B) ∧ (∀ y, |ψ y| ≤ 2 * B) ∧ (∀ x y, φ x + ψ y ≤ 2 * B) ∧
      (∀ x₁ x₂ δ, 0 ≤ δ → (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) →
        |φ x₁ - φ x₂| ≤ δ) ∧
      (∀ y₁ y₂ δ, 0 ≤ δ → (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) →
        |ψ y₁ - ψ y₂| ≤ δ) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  have hfin : ∀ z, c z ≠ ∞ := fun z ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  obtain ⟨φ, ψ, hp⟩ := exists_isRegularizedPotentialPair (μ := μ) (ν := ν) hc.measurable hcB hε
  have hcR : Continuous fun z : X × Y ↦ (c z).toReal := hc.ennreal_toReal hfin
  have hφc : Continuous φ :=
    (Metric.equicontinuous_of_forall_dist_le (F := fun _ : Unit ↦ φ) (L := 1) hcR
      fun x₁ x₂ δ hδ h _ ↦ by
        simpa only [Real.dist_eq, one_mul] using
          hp.abs_sub_left_le x₁ x₂ δ hδ (by simpa only [Real.dist_eq] using h)).continuous ()
  have hψc : Continuous ψ :=
    (Metric.equicontinuous_of_forall_dist_le (F := fun _ : Unit ↦ ψ) (L := 1)
      (hcR.comp continuous_swap) fun y₁ y₂ δ hδ h _ ↦ by
        simpa only [Real.dist_eq, one_mul] using hp.abs_sub_right_le y₁ y₂ δ hδ
          (by simpa only [Real.dist_eq, Function.comp_apply, Prod.swap_prod_mk] using h)).continuous
      ()
  exact ⟨φ, ψ, hφc, hψc, hp.abs_left_le, hp.abs_right_le, hp.add_le,
    hp.abs_sub_left_le, hp.abs_sub_right_le, hp.integral_gibbs_eq_one, hp.dualValue_eq⟩

/-- **Joint weak continuity of real-valued entropic optimal transport on compact spaces.** For a
continuous finite-valued cost on compact spaces and a positive temperature `ε`, the map
`(μ, ν) ↦ (entropicTransportCost c ε μ ν).toReal` is jointly continuous on
`ProbabilityMeasure X × ProbabilityMeasure Y`. -/
theorem continuous_toReal_entropicTransportCost (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞)
    (hε : ε ≠ 0) :
    Continuous fun p : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (entropicTransportCost c ε (p.1 : Measure X) (p.2 : Measure Y)).toReal := by
  set I := ProbabilityMeasure X × ProbabilityMeasure Y
  obtain ⟨B, hcB⟩ := exists_le_of_continuous_of_ne_top hc hfin
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hcR : Continuous fun z : X × Y ↦ (c z).toReal := hc.ennreal_toReal hfin
  -- Choose normalised `c`-softmin potentials `(φ q, ψ q)` for each pair `q = (μ, ν)`.
  have hex (q : I) := exists_isRegularizedPotentialPair
    (μ := (q.1 : Measure X)) (ν := (q.2 : Measure Y)) hc.measurable hcB hε
  let φ : I → X → ℝ := fun q ↦ (hex q).choose
  let ψ : I → Y → ℝ := fun q ↦ (hex q).choose_spec.choose
  have hspec (q : I) : IsRegularizedPotentialPair c ε B (q.1 : Measure X) (q.2 : Measure Y)
      (φ q) (ψ q) :=
    (hex q).choose_spec.choose_spec
  -- Equicontinuity and pointwise boundedness of `φ`, `ψ`, and the Gibbs slices `G`.
  have hequi_φ : Equicontinuous φ :=
    Metric.equicontinuous_of_forall_dist_le (L := 1) hcR fun x₁ x₂ δ hδ h q ↦ by
      simpa only [Real.dist_eq, one_mul] using
        (hspec q).abs_sub_left_le x₁ x₂ δ hδ (by simpa only [Real.dist_eq] using h)
  have hequi_ψ : Equicontinuous ψ :=
    Metric.equicontinuous_of_forall_dist_le (L := 1) (hcR.comp continuous_swap)
      fun y₁ y₂ δ hδ h q ↦ by
        simpa only [Real.dist_eq, one_mul] using (hspec q).abs_sub_right_le y₁ y₂ δ hδ
          (by simpa only [Real.dist_eq, Function.comp_apply, Prod.swap_prod_mk] using h)
  let G : I × Y → X → ℝ := fun qy x ↦ entropicGibbsFactor c ε (φ qy.1) (ψ qy.1) (x, qy.2)
  have hequi_G : Equicontinuous G := equicontinuous_entropicGibbsFactor hc hfin hε hspec
  have htb_φ : ∀ x, TotallyBounded (range fun q ↦ φ q x) := fun x ↦
    (isCompact_Icc (a := -(B : ℝ)) (b := B)).totallyBounded.subset <| by
      rintro _ ⟨q, rfl⟩
      exact abs_le.1 ((hspec q).abs_left_le x)
  have htb_ψ : ∀ y, TotallyBounded (range fun q ↦ ψ q y) := fun y ↦
    (isCompact_Icc (a := -(2 * (B : ℝ))) (b := 2 * B)).totallyBounded.subset <| by
      rintro _ ⟨q, rfl⟩
      exact abs_le.1 ((hspec q).abs_right_le y)
  have htb_G : ∀ x, TotallyBounded (range fun qy ↦ G qy x) := fun x ↦
    (isCompact_Icc (a := (0 : ℝ)) (b := Real.exp (2 * B / ε))).totallyBounded.subset <| by
      rintro _ ⟨qy, rfl⟩
      refine ⟨entropicGibbsFactor_nonneg _, ?_⟩
      simp only [G, entropicGibbsFactor_of_ne_top (hfin (x, qy.2)), Real.exp_le_exp]
      exact div_le_div_of_nonneg_right
        (by linarith [(hspec qy.1).add_le x qy.2, (c (x, qy.2)).toReal_nonneg]) hεpos.le
  -- Apply Ranga Rao's uniform convergence theorem to `φ`, `ψ`, and `G`, and combine both
  -- one-sided perturbation bounds.
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro η hη
  have hunif_φ := ProbabilityMeasure.tendstoUniformly_integral_of_equicontinuous
    (continuous_fst.tendsto p₀) hequi_φ htb_φ
  have hunif_ψ := ProbabilityMeasure.tendstoUniformly_integral_of_equicontinuous
    (continuous_snd.tendsto p₀) hequi_ψ htb_ψ
  have hunif_G := ProbabilityMeasure.tendstoUniformly_integral_of_equicontinuous
    (continuous_fst.tendsto p₀) hequi_G htb_G
  filter_upwards [Metric.tendstoUniformly_iff.1 hunif_φ (η / 3) (by positivity),
    Metric.tendstoUniformly_iff.1 hunif_ψ (η / 3) (by positivity),
    Metric.tendstoUniformly_iff.1 hunif_G (η / (3 * ε)) (by positivity)]
    with p hpφ hpψ hpG
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · refine (hspec p).toReal_entropicTransportCost_sub_lt hc.measurable hcB hε ?_ ?_ fun y ↦ ?_
    · have h := hpφ p; rw [Real.dist_eq] at h; linarith [(abs_lt.1 h).1]
    · have h := hpψ p; rw [Real.dist_eq] at h; linarith [(abs_lt.1 h).1]
    · have h := (hpG (p, y)).le; rw [Real.dist_eq] at h; linarith [(abs_le.1 h).2]
  · refine (hspec p₀).toReal_entropicTransportCost_sub_lt hc.measurable hcB hε ?_ ?_ fun y ↦ ?_
    · have h := hpφ p₀; rw [Real.dist_eq] at h; linarith [(abs_lt.1 h).2]
    · have h := hpψ p₀; rw [Real.dist_eq] at h; linarith [(abs_lt.1 h).2]
    · have h := (hpG (p₀, y)).le; rw [Real.dist_eq] at h; linarith [(abs_le.1 h).1]

/-- **Joint weak continuity of `ℝ≥0∞`-valued entropic optimal transport on compact spaces.** -/
theorem continuous_entropicTransportCost (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞)
    (hε : ε ≠ 0) :
    Continuous fun p : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε (p.1 : Measure X) (p.2 : Measure Y) := by
  set I := ProbabilityMeasure X × ProbabilityMeasure Y
  obtain ⟨B, hcB⟩ := exists_le_of_continuous_of_ne_top hc hfin
  have heq : (fun p : I ↦ entropicTransportCost c ε (p.1 : Measure X) (p.2 : Measure Y)) =
      fun p : I ↦ ENNReal.ofReal
        (entropicTransportCost c ε (p.1 : Measure X) (p.2 : Measure Y)).toReal :=
    funext fun p ↦ (ENNReal.ofReal_toReal
      (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp (continuous_toReal_entropicTransportCost hc hfin hε)

end Compact

end TauCeti
