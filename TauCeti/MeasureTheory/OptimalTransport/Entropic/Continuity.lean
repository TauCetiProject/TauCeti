/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.FiniteMeasure.Equicontinuous

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
bounded in terms of `B` alone, and inherits every uniform coordinate oscillation bound of
`(c ·).toReal`.

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
* `TauCeti.exists_continuous_entropicDualValue_eq`: dual attainment on compact spaces by continuous
  potentials satisfying the pointwise marginal identity.
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
  have hrhs : (a : ℝ≥0∞) * entropicTransportCost c ε μ ν₀ +
      b * entropicTransportCost c ε μ ν₁ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top h₀,
      ENNReal.mul_ne_top ENNReal.coe_ne_top h₁⟩
  have hle := ENNReal.toReal_mono hrhs (entropicTransportCost_smul_add_smul_right_le hab c ε)
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top h₀)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top h₁), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.coe_toReal] at hle

end Convexity

/-! ### Regularised Schrödinger potentials via the `c`-softmin operator -/

section Softmin

/-- On `(-∞, M]`, the real exponential is `exp M`-Lipschitz. -/
private theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  wlog hba : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hba)
  rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hba)), abs_of_nonneg (sub_nonneg.2 hba)]
  have h1 : 1 - Real.exp (b - a) ≤ a - b := by linarith [Real.add_one_le_exp (b - a)]
  have h2 : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_sub_cancel]
  rw [h2]
  exact (mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ha) (sub_nonneg.2 hba))

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0}
  {μ μ' : Measure X} {ν ν' : Measure Y}

/-- The `c`-softmin transform `-ε * log ∫ exp ((ψ(y) - c(x, y)) / ε) dν(y)` of a potential `ψ`. -/
private def entropicSoftmin (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (ν : Measure Y) (ψ : Y → ℝ) (x : X) :
    ℝ :=
  -(ε : ℝ) * Real.log (∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν)

private theorem measurable_entropicSoftmin [SFinite ν] (hc : Measurable c) {ψ : Y → ℝ}
    (hψ : Measurable ψ) : Measurable (entropicSoftmin c ε ν ψ) := by
  have hsm : StronglyMeasurable fun z : X × Y ↦ Real.exp ((ψ z.2 - (c z).toReal) / ε) :=
    (by fun_prop :
      Measurable fun z : X × Y ↦ Real.exp ((ψ z.2 - (c z).toReal) / ε)).stronglyMeasurable
  exact hsm.integral_prod_right'.measurable.log.const_mul _

private theorem integrable_exp_sub_toReal [IsFiniteMeasure ν] (hc : Measurable c)
    {ψ : Y → ℝ} {C : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, |ψ y| ≤ C)
    (x : X) : Integrable (fun y ↦ Real.exp ((ψ y - (c (x, y)).toReal) / ε)) ν := by
  have hcx : Measurable fun y ↦ (c (x, y)).toReal := (hc.comp measurable_prodMk_left).ennreal_toReal
  refine .of_bound ((hψ.sub hcx).div_const _).exp.aestronglyMeasurable (Real.exp (C / ε))
    (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  refine div_le_div_of_nonneg_right ?_ ε.coe_nonneg
  linarith [le_of_abs_le (hψC y), (c (x, y)).toReal_nonneg]

private theorem abs_entropicSoftmin_le [IsProbabilityMeasure ν] (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {ψ : Y → ℝ} {C : ℝ} (hψ : Measurable ψ)
    (hψC : ∀ y, |ψ y| ≤ C) (x : X) :
    |entropicSoftmin c ε ν ψ x| ≤ C + B := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hint := integrable_exp_sub_toReal (ν := ν) (ε := ε) hc hψ hψC x
  have hZpos : 0 < ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint
  have hle_B : ∀ y, (c (x, y)).toReal ≤ B := fun y ↦
    ENNReal.toReal_le_coe_of_le_coe (hcB (x, y))
  have hupper : ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν ≤ Real.exp ((C + B) / ε) := by
    calc ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν
        ≤ ∫ _, Real.exp ((C + B) / ε) ∂ν :=
          integral_mono hint (integrable_const _) fun y ↦ Real.exp_le_exp.2 <|
            div_le_div_of_nonneg_right
              (by linarith [le_of_abs_le (hψC y), (c (x, y)).toReal_nonneg, B.coe_nonneg])
              ε.coe_nonneg
      _ = Real.exp ((C + B) / ε) := by simp
  have hlower : Real.exp (-(C + B) / ε) ≤ ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν := by
    calc Real.exp (-(C + B) / ε) = ∫ _, Real.exp (-(C + B) / ε) ∂ν := by simp
      _ ≤ ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν :=
          integral_mono (integrable_const _) hint fun y ↦ Real.exp_le_exp.2 <|
            div_le_div_of_nonneg_right
              (by linarith [(abs_le.1 (hψC y)).1, hle_B y]) ε.coe_nonneg
  have hlog_u := (Real.log_le_log hZpos hupper).trans_eq (Real.log_exp _)
  have hlog_l := (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hlower)
  rw [entropicSoftmin, abs_le]
  constructor
  · have := mul_le_mul_of_nonneg_left hlog_u hεpos.le
    rw [mul_div_cancel₀ _ hεpos.ne'] at this
    linarith
  · have := mul_le_mul_of_nonneg_left hlog_l hεpos.le
    rw [neg_div, mul_neg, mul_div_cancel₀ _ hεpos.ne'] at this
    linarith

/-- The `c`-softmin inherits every uniform oscillation bound of `(c ·).toReal` in its first
variable, independently of the measure `ν`, the temperature `ε`, and the potential `ψ`. -/
private theorem abs_entropicSoftmin_sub_le [IsProbabilityMeasure ν] (hc : Measurable c)
    (hε : ε ≠ 0) {ψ : Y → ℝ} {C : ℝ} (hψ : Measurable ψ)
    (hψC : ∀ y, |ψ y| ≤ C) {x₁ x₂ : X} {δ : ℝ}
    (hosc : ∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) :
    |entropicSoftmin c ε ν ψ x₁ - entropicSoftmin c ε ν ψ x₂| ≤ δ := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have one_side {u v : X} (huv : ∀ y, (c (v, y)).toReal - (c (u, y)).toReal ≤ δ) :
      entropicSoftmin c ε ν ψ v - entropicSoftmin c ε ν ψ u ≤ δ := by
    have hint_u := integrable_exp_sub_toReal (ν := ν) (ε := ε) hc hψ hψC u
    have hint_v := integrable_exp_sub_toReal (ν := ν) (ε := ε) hc hψ hψC v
    have hZu : 0 < ∫ y, Real.exp ((ψ y - (c (u, y)).toReal) / ε) ∂ν := integral_exp_pos hint_u
    have hZv : 0 < ∫ y, Real.exp ((ψ y - (c (v, y)).toReal) / ε) ∂ν := integral_exp_pos hint_v
    have hle : ∫ y, Real.exp ((ψ y - (c (u, y)).toReal) / ε) ∂ν ≤
        Real.exp (δ / ε) * ∫ y, Real.exp ((ψ y - (c (v, y)).toReal) / ε) ∂ν := by
      rw [← integral_const_mul]
      refine integral_mono hint_u (hint_v.const_mul _) fun y ↦ ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hεpos.le
      linarith [huv y]
    have hlog : Real.log (∫ y, Real.exp ((ψ y - (c (u, y)).toReal) / ε) ∂ν) ≤
        δ / ε + Real.log (∫ y, Real.exp ((ψ y - (c (v, y)).toReal) / ε) ∂ν) := by
      refine (Real.log_le_log hZu hle).trans_eq ?_
      rw [Real.log_mul (Real.exp_pos _).ne' hZv.ne', Real.log_exp]
    have hmul := mul_le_mul_of_nonneg_left hlog hεpos.le
    rw [mul_add, mul_div_cancel₀ _ hεpos.ne'] at hmul
    simp only [entropicSoftmin]
    linarith
  rw [abs_sub_le_iff]
  exact ⟨one_side fun y ↦ by linarith [(abs_le.1 (hosc y)).2],
    one_side fun y ↦ by linarith [(abs_le.1 (hosc y)).1]⟩

/-- At `φ = entropicSoftmin c ε ν ψ`, the Gibbs slice integrates to `1` against `ν` at *every*
point `x : X`. -/
private theorem integral_entropicGibbsFactor_entropicSoftmin [IsProbabilityMeasure ν]
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {ψ : Y → ℝ} {C : ℝ}
    (hψ : Measurable ψ) (hψC : ∀ y, |ψ y| ≤ C) (x : X) :
    ∫ y, entropicGibbsFactor c ε (entropicSoftmin c ε ν ψ) ψ (x, y) ∂ν = 1 := by
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  have hfin : ∀ y, c (x, y) ≠ ∞ := fun y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB (x, y))
  have hint := integrable_exp_sub_toReal (ν := ν) (ε := ε) hc hψ hψC x
  have hZpos : 0 < ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ entropicGibbsFactor c ε (entropicSoftmin c ε ν ψ) ψ (x, y)) =
      fun y ↦ Real.exp (entropicSoftmin c ε ν ψ x / ε) *
        Real.exp ((ψ y - (c (x, y)).toReal) / ε) := by
    funext y
    rw [entropicGibbsFactor_of_ne_top (hfin y), ← Real.exp_add]
    congr 1
    ring
  rw [hsplit, integral_const_mul, entropicSoftmin, neg_mul, neg_div, mul_div_cancel_left₀ _ hε',
    Real.exp_neg, Real.exp_log hZpos, inv_mul_cancel₀ hZpos.ne']

/-- Replacing `φ` by `entropicSoftmin c ε ν ψ` does not decrease `entropicDualValue`. -/
private theorem entropicDualValue_le_entropicSoftmin_left [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {φ : X → ℝ} {ψ : Y → ℝ} {Cφ Cψ : ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφC : ∀ x, |φ x| ≤ Cφ) (hψC : ∀ y, |ψ y| ≤ Cψ) :
    entropicDualValue c ε μ ν φ ψ ≤
      entropicDualValue c ε μ ν (entropicSoftmin c ε ν ψ) ψ := by
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
  have hint₁ : ∫ z, (entropicGibbsFactor c ε φ₁ ψ z - 1) ∂μ.prod ν = 0 := by
    rw [integral_sub hexp₁ (integrable_const _), integral_prod _ hexp₁]
    simp [φ₁, integral_entropicGibbsFactor_entropicSoftmin hc hcB hε hψ hψC']
  have hslice (x : X) : ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν =
      Real.exp ((φ x - φ₁ x) / ε) := by
    have hfin : ∀ y, c (x, y) ≠ ∞ := fun y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB (x, y))
    have hint := integrable_exp_sub_toReal (ν := ν) (ε := ε) hc hψ hψC x
    have hZpos : 0 < ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint
    have hsplit : (fun y ↦ entropicGibbsFactor c ε φ ψ (x, y)) =
        fun y ↦ Real.exp (φ x / ε) * Real.exp ((ψ y - (c (x, y)).toReal) / ε) := by
      funext y
      rw [entropicGibbsFactor_of_ne_top (hfin y), ← Real.exp_add]
      congr 1
      ring
    rw [hsplit, integral_const_mul, ← Real.exp_log hZpos, ← Real.exp_add]
    congr 1
    simp only [φ₁, entropicSoftmin]
    field_simp
    ring
  have hpen : ∫ z, (entropicGibbsFactor c ε φ ψ z - 1) ∂μ.prod ν =
      ∫ x, (Real.exp ((φ x - φ₁ x) / ε) - 1) ∂μ := by
    rw [integral_sub hexp (integrable_const _), integral_prod _ hexp,
      integral_sub hexp_diff (integrable_const _)]
    simp_rw [hslice]
    simp
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

/-- **Existence of normalised `c`-softmin optimal potentials.** For probability measures, a bounded
measurable cost `c ≤ B` and a positive temperature `ε`, there exist measurable potentials `(φ, ψ)`
bounded by `B` and `2 * B` that attain `(entropicTransportCost c ε μ ν).toReal`, satisfy
`φ(x) + ψ(y) ≤ 2 * B` and `∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1` at *every* `y : Y`, and
inherit every uniform coordinate oscillation bound of `(c ·).toReal`. -/
private theorem exists_regularized_entropicPotentials [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, |φ x| ≤ B) ∧ (∀ y, |ψ y| ≤ 2 * B) ∧ (∀ x y, φ x + ψ y ≤ 2 * B) ∧
      (∀ x₁ x₂ δ, 0 ≤ δ → (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) →
        |φ x₁ - φ x₂| ≤ δ) ∧
      (∀ y₁ y₂ δ, 0 ≤ δ → (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) →
        |ψ y₁ - ψ y₂| ≤ δ) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
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
    have hint := integrable_exp_sub_toReal (ν := μ) (ε := ε) hcs hφm hφB y
    have hlower : Real.exp ((φ x - 2 * B) / ε) ≤
        ∫ x', Real.exp ((φ x' - ((c ∘ Prod.swap) (y, x')).toReal) / ε) ∂μ := by
      calc Real.exp ((φ x - 2 * B) / ε) = ∫ _, Real.exp ((φ x - 2 * B) / ε) ∂μ := by simp
        _ ≤ ∫ x', Real.exp ((φ x' - ((c ∘ Prod.swap) (y, x')).toReal) / ε) ∂μ :=
            integral_mono (integrable_const _) hint fun x' ↦ Real.exp_le_exp.2 <|
              div_le_div_of_nonneg_right
                (by
                  have hdiff : φ x - φ x' ≤ B :=
                    (le_abs_self _).trans (hφ_osc x x' B B.coe_nonneg (hosc_B x x'))
                  have hc' : ((c ∘ Prod.swap) (y, x')).toReal ≤ B :=
                    ENNReal.toReal_le_coe_of_le_coe (hcB (x', y))
                  linarith)
                hεpos.le
    have hlog := (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hlower)
    have hmul := mul_le_mul_of_nonneg_left hlog hεpos.le
    rw [mul_div_cancel₀ _ hεpos.ne'] at hmul
    simp only [ψ, entropicSoftmin]
    linarith
  have hψ_osc : ∀ y₁ y₂ δ, 0 ≤ δ →
      (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) → |ψ y₁ - ψ y₂| ≤ δ :=
    fun y₁ y₂ δ _ h ↦ abs_entropicSoftmin_sub_le (ν := μ) hcs hε hφm hφB h
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
  exact ⟨φ, ψ, hφm, hψm, hφB, hψB, hφψ_sum, hφ_osc, hψ_osc, hslice, hval⟩

/-- **One-sided dual perturbation bound.** When `(φ, ψ)` attains
`(entropicTransportCost c ε μ ν).toReal` and satisfies the pointwise marginal equation
`∫ x, G(x, y) ∂μ = 1` for every `y`, subtracting weak duality at `(μ', ν')` expresses the drop in
optimal value through marginal differences of `φ`, `ψ`, and the `x`-slices of `G`. -/
private theorem toReal_entropicTransportCost_sub_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {φ : X → ℝ} {ψ : Y → ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφB : ∀ x, |φ x| ≤ B) (hψB : ∀ y, |ψ y| ≤ 2 * B)
    (hslice : ∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1)
    (hval : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal) :
    (entropicTransportCost c ε μ ν).toReal - (entropicTransportCost c ε μ' ν').toReal ≤
      (∫ x, φ x ∂μ - ∫ x, φ x ∂μ') + (∫ y, ψ y ∂ν - ∫ y, ψ y ∂ν') +
        ε * ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
          ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν' := by
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ hψ
    (fun x ↦ le_of_abs_le (hφB x)) (fun y ↦ le_of_abs_le (hψB y))
  have hexp' := integrable_entropicGibbsFactor_of_le (μ := μ') (ν := ν') (ε := ε) hc hφ hψ
    (fun x ↦ le_of_abs_le (hφB x)) (fun y ↦ le_of_abs_le (hψB y))
  have hval_eq : (entropicTransportCost c ε μ ν).toReal = ∫ x, φ x ∂μ + ∫ y, ψ y ∂ν := by
    rw [← hval, entropicDualValue_def, kantorovichDualValue_def,
      integral_sub hexp (integrable_const _), integral_prod_symm _ hexp]
    simp [hslice]
  have hdual' := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε
    (.of_bound hφ.aestronglyMeasurable B (ae_of_all _ hφB))
    (.of_bound hψ.aestronglyMeasurable (2 * B) (ae_of_all _ hψB)) hexp'
  rw [entropicDualValue_def, kantorovichDualValue_def,
    integral_sub hexp' (integrable_const _), integral_prod_symm _ hexp'] at hdual'
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hdual'
  have hpen : ∫ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' ∂ν' - 1 =
      ∫ y, (∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ' -
        ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ) ∂ν' := by
    simp_rw [hslice]
    rw [integral_sub hexp'.integral_prod_right (integrable_const _)]
    simp
  rw [hval_eq, ← hpen]
  linarith

end Softmin

/-! ### Joint weak continuity on compact spaces -/

section Compact

/-- By the tube lemma on `{x₀} × Y`, a family `F : ι → X → ℝ` controlled linearly by the uniform
`Y`-oscillation of a jointly continuous function `g : X × Y → ℝ` on compact `Y` is
equicontinuous. -/
private theorem equicontinuous_of_forall_oscillation_le {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {g : X × Y → ℝ} (hg : Continuous g) {F : ι → X → ℝ}
    {L : ℝ} (hL : 0 < L)
    (hosc : ∀ x₁ x₂ δ, 0 ≤ δ → (∀ y, |g (x₁, y) - g (x₂, y)| ≤ δ) →
      ∀ i, |F i x₁ - F i x₂| ≤ L * δ) :
    Equicontinuous F := by
  intro x₀
  rw [Metric.uniformity_basis_dist.equicontinuousAt_iff_right]
  intro r hr
  set δ : ℝ := r / (2 * L)
  have hδ : 0 < δ := by positivity
  set n : Set (X × Y) := {z | |g z - g (x₀, z.2)| < δ}
  have hn : IsOpen n :=
    isOpen_lt (Continuous.abs (hg.sub (hg.comp (continuous_const.prodMk continuous_snd))))
      continuous_const
  have hsub : ({x₀} : Set X) ×ˢ (univ : Set Y) ⊆ n := by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain rfl := mem_singleton_iff.1 hx
    simp [n, hδ]
  obtain ⟨u, v, hu, -, hx₀u, huv_univ, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hsub
  filter_upwards [hu.mem_nhds (hx₀u rfl)] with x hxu i
  have hxy : ∀ y, |g (x, y) - g (x₀, y)| ≤ δ := fun y ↦
    (huv ⟨hxu, huv_univ (mem_univ y)⟩).le
  rw [Real.dist_eq, abs_sub_comm]
  calc |F i x - F i x₀| ≤ L * δ := hosc x x₀ δ hδ.le hxy i
    _ = r / 2 := by
        simp only [δ]
        field_simp
    _ < r := half_lt_self hr

/-- On a compact space, a continuous finite-valued `ℝ≥0∞` cost is bounded above by a finite `ℝ≥0`
constant. -/
private theorem exists_le_of_continuous_of_ne_top {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {c : Z → ℝ≥0∞} (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) :
    ∃ B : ℝ≥0, ∀ z, c z ≤ B := by
  have hcR : Continuous fun z : Z ↦ (c z).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous hc hfin
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcR.continuousOn
  refine ⟨Real.toNNReal M, fun z ↦ ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin z), ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hz : (c z).toReal ≤ M := (le_abs_self _).trans (by simpa using hM z (mem_univ z))
  exact hz.trans (Real.le_coe_toNNReal M)

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [OpensMeasurableSpace (X × Y)] {c : X × Y → ℝ≥0∞} {ε : ℝ≥0}

omit [OpensMeasurableSpace X] [OpensMeasurableSpace Y] in
/-- **Existence of continuous optimal Schrödinger potentials on compact spaces.** For probability
measures on compact spaces, a continuous finite-valued cost and a positive temperature, the
entropic dual problem is attained by continuous potentials `(φ, ψ)` satisfying the pointwise
marginal identity `∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1` for every `y : Y`. -/
theorem exists_continuous_entropicDualValue_eq {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞)
    (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Continuous φ ∧ Continuous ψ ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨B, hcB⟩ := exists_le_of_continuous_of_ne_top hc hfin
  obtain ⟨φ, ψ, -, -, -, -, -, hφ_osc, hψ_osc, hslice, hval⟩ :=
    exists_regularized_entropicPotentials (μ := μ) (ν := ν) hc.measurable hcB hε
  have hcR : Continuous fun z : X × Y ↦ (c z).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous hc hfin
  have hφc : Continuous φ :=
    (equicontinuous_of_forall_oscillation_le (ι := Unit) hcR zero_lt_one
      fun x₁ x₂ δ hδ h _ ↦ by simpa using hφ_osc x₁ x₂ δ hδ h).continuous ()
  have hψc : Continuous ψ :=
    (equicontinuous_of_forall_oscillation_le (ι := Unit) (hcR.comp continuous_swap) zero_lt_one
      fun y₁ y₂ δ hδ h _ ↦ by simpa using hψ_osc y₁ y₂ δ hδ h).continuous ()
  exact ⟨φ, ψ, hφc, hψc, hslice, hval⟩

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
  have hcR : Continuous fun z : X × Y ↦ (c z).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous hc hfin
  have hex (q : I) := exists_regularized_entropicPotentials
    (μ := (q.1 : Measure X)) (ν := (q.2 : Measure Y)) hc.measurable hcB hε
  let φ : I → X → ℝ := fun q ↦ (hex q).choose
  let ψ : I → Y → ℝ := fun q ↦ (hex q).choose_spec.choose
  have hspec (q : I) := (hex q).choose_spec.choose_spec
  have hφm (q : I) : Measurable (φ q) := (hspec q).1
  have hψm (q : I) : Measurable (ψ q) := (hspec q).2.1
  have hφB (q : I) (x : X) : |φ q x| ≤ B := (hspec q).2.2.1 x
  have hψB (q : I) (y : Y) : |ψ q y| ≤ 2 * B := (hspec q).2.2.2.1 y
  have hsum (q : I) (x : X) (y : Y) : φ q x + ψ q y ≤ 2 * B := (hspec q).2.2.2.2.1 x y
  have hφ_osc (q : I) := (hspec q).2.2.2.2.2.1
  have hψ_osc (q : I) := (hspec q).2.2.2.2.2.2.1
  have hslice (q : I) := (hspec q).2.2.2.2.2.2.2.1
  have hval (q : I) := (hspec q).2.2.2.2.2.2.2.2
  have hequi_φ : Equicontinuous φ :=
    equicontinuous_of_forall_oscillation_le hcR zero_lt_one fun x₁ x₂ δ hδ h q ↦ by
      simpa using hφ_osc q x₁ x₂ δ hδ h
  have hequi_ψ : Equicontinuous ψ :=
    equicontinuous_of_forall_oscillation_le (hcR.comp continuous_swap) zero_lt_one
      fun y₁ y₂ δ hδ h q ↦ by simpa using hψ_osc q y₁ y₂ δ hδ h
  let G : I × Y → X → ℝ := fun qy x ↦ entropicGibbsFactor c ε (φ qy.1) (ψ qy.1) (x, qy.2)
  have hequi_G : Equicontinuous G := by
    refine equicontinuous_of_forall_oscillation_le hcR
      (L := Real.exp (2 * B / ε) * (2 / ε)) (by positivity) fun x₁ x₂ δ hδ h qy ↦ ?_
    simp only [G, entropicGibbsFactor_of_ne_top (hfin (x₁, qy.2)),
      entropicGibbsFactor_of_ne_top (hfin (x₂, qy.2))]
    have hexp1 : (φ qy.1 x₁ + ψ qy.1 qy.2 - (c (x₁, qy.2)).toReal) / ε ≤ 2 * B / ε :=
      div_le_div_of_nonneg_right
        (by linarith [hsum qy.1 x₁ qy.2, (c (x₁, qy.2)).toReal_nonneg]) hεpos.le
    have hexp2 : (φ qy.1 x₂ + ψ qy.1 qy.2 - (c (x₂, qy.2)).toReal) / ε ≤ 2 * B / ε :=
      div_le_div_of_nonneg_right
        (by linarith [hsum qy.1 x₂ qy.2, (c (x₂, qy.2)).toReal_nonneg]) hεpos.le
    refine (abs_exp_sub_exp_le hexp1 hexp2).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hφd := hφ_osc qy.1 x₁ x₂ δ hδ h
    have hcd := h qy.2
    have hdiff : |(φ qy.1 x₁ + ψ qy.1 qy.2 - (c (x₁, qy.2)).toReal) / ε -
        (φ qy.1 x₂ + ψ qy.1 qy.2 - (c (x₂, qy.2)).toReal) / ε| =
        |(φ qy.1 x₁ - φ qy.1 x₂) - ((c (x₁, qy.2)).toReal - (c (x₂, qy.2)).toReal)| / ε := by
      rw [← sub_div, abs_div, abs_of_pos hεpos]
      congr 2
      ring
    rw [hdiff, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hεpos]
    calc |(φ qy.1 x₁ - φ qy.1 x₂) - ((c (x₁, qy.2)).toReal - (c (x₂, qy.2)).toReal)|
        ≤ |φ qy.1 x₁ - φ qy.1 x₂| + |(c (x₁, qy.2)).toReal - (c (x₂, qy.2)).toReal| :=
          abs_sub _ _
      _ ≤ 2 * δ := by linarith
  have htb_φ : ∀ x, TotallyBounded (range fun q ↦ φ q x) := fun x ↦
    (isCompact_Icc (a := -(B : ℝ)) (b := B)).totallyBounded.subset <| by
      rintro _ ⟨q, rfl⟩
      exact abs_le.1 (hφB q x)
  have htb_ψ : ∀ y, TotallyBounded (range fun q ↦ ψ q y) := fun y ↦
    (isCompact_Icc (a := -(2 * (B : ℝ))) (b := 2 * B)).totallyBounded.subset <| by
      rintro _ ⟨q, rfl⟩
      exact abs_le.1 (hψB q y)
  have htb_G : ∀ x, TotallyBounded (range fun qy ↦ G qy x) := fun x ↦
    (isCompact_Icc (a := (0 : ℝ)) (b := Real.exp (2 * B / ε))).totallyBounded.subset <| by
      rintro _ ⟨qy, rfl⟩
      refine ⟨entropicGibbsFactor_nonneg _, ?_⟩
      simp only [G, entropicGibbsFactor_of_ne_top (hfin (x, qy.2)), Real.exp_le_exp]
      exact div_le_div_of_nonneg_right
        (by linarith [hsum qy.1 x qy.2, (c (x, qy.2)).toReal_nonneg]) hεpos.le
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
  have bound_one_side (q r : I)
      (hφqr : ∫ x, φ q x ∂(q.1 : Measure X) - ∫ x, φ q x ∂(r.1 : Measure X) < η / 3)
      (hψqr : ∫ y, ψ q y ∂(q.2 : Measure Y) - ∫ y, ψ q y ∂(r.2 : Measure Y) < η / 3)
      (hGqr : ∀ y, ∫ x, G (q, y) x ∂(r.1 : Measure X) -
        ∫ x, G (q, y) x ∂(q.1 : Measure X) ≤ η / (3 * ε)) :
      (entropicTransportCost c ε (q.1 : Measure X) (q.2 : Measure Y)).toReal -
        (entropicTransportCost c ε (r.1 : Measure X) (r.2 : Measure Y)).toReal < η := by
    have hexp_r := integrable_entropicGibbsFactor_of_le (μ := (r.1 : Measure X))
      (ν := (r.2 : Measure Y)) (ε := ε) hc.measurable (hφm q) (hψm q)
      (fun x ↦ le_of_abs_le (hφB q x)) (fun y ↦ le_of_abs_le (hψB q y))
    have hexp_qr := integrable_entropicGibbsFactor_of_le (μ := (q.1 : Measure X))
      (ν := (r.2 : Measure Y)) (ε := ε) hc.measurable (hφm q) (hψm q)
      (fun x ↦ le_of_abs_le (hφB q x)) (fun y ↦ le_of_abs_le (hψB q y))
    have hpen : ∫ y, (∫ x, entropicGibbsFactor c ε (φ q) (ψ q) (x, y) ∂(r.1 : Measure X) -
          ∫ x, entropicGibbsFactor c ε (φ q) (ψ q) (x, y) ∂(q.1 : Measure X))
          ∂(r.2 : Measure Y) ≤ η / (3 * ε) := by
      calc ∫ y, (∫ x, entropicGibbsFactor c ε (φ q) (ψ q) (x, y) ∂(r.1 : Measure X) -
              ∫ x, entropicGibbsFactor c ε (φ q) (ψ q) (x, y) ∂(q.1 : Measure X))
              ∂(r.2 : Measure Y)
          ≤ ∫ _, η / (3 * ε) ∂(r.2 : Measure Y) :=
            integral_mono (hexp_r.integral_prod_right.sub hexp_qr.integral_prod_right)
              (integrable_const _) hGqr
        _ = η / (3 * ε) := by simp
    have hmul : (ε : ℝ) * ∫ y,
        (∫ x, entropicGibbsFactor c ε (φ q) (ψ q) (x, y) ∂(r.1 : Measure X) -
          ∫ x, entropicGibbsFactor c ε (φ q) (ψ q) (x, y) ∂(q.1 : Measure X))
        ∂(r.2 : Measure Y) ≤ η / 3 := by
      refine (mul_le_mul_of_nonneg_left hpen hεpos.le).trans_eq ?_
      field_simp
    have hpert := toReal_entropicTransportCost_sub_le (μ := (q.1 : Measure X))
      (ν := (q.2 : Measure Y)) (μ' := (r.1 : Measure X)) (ν' := (r.2 : Measure Y))
      hc.measurable hcB hε (hφm q) (hψm q) (hφB q) (hψB q) (hslice q) (hval q)
    linarith
  constructor
  · refine bound_one_side p p₀ ?_ ?_ fun y ↦ ?_
    · have h := hpφ p
      rw [Real.dist_eq] at h
      linarith [(abs_lt.1 h).1]
    · have h := hpψ p
      rw [Real.dist_eq] at h
      linarith [(abs_lt.1 h).1]
    · have h := (hpG (p, y)).le
      rw [Real.dist_eq] at h
      linarith [(abs_le.1 h).2]
  · refine bound_one_side p₀ p ?_ ?_ fun y ↦ ?_
    · have h := hpφ p₀
      rw [Real.dist_eq] at h
      linarith [(abs_lt.1 h).2]
    · have h := hpψ p₀
      rw [Real.dist_eq] at h
      linarith [(abs_lt.1 h).2]
    · have h := (hpG (p₀, y)).le
      rw [Real.dist_eq] at h
      linarith [(abs_le.1 h).1]

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
