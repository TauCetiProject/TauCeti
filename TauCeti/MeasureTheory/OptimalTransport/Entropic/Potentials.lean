/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality
import TauCeti.Basic.ENNReal.Real
import TauCeti.MeasureTheory.Integral.Exp.Log

/-!
# Canonical Schrödinger potentials and softmin regularity

At positive temperature `ε ≠ 0` and for a bounded measurable cost `c ≤ B`, entropic duality
(`TauCeti.exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost`) furnishes bounded
measurable potentials `(φ₀, ψ₀)` whose Gibbs density couples two probability measures `μ` and `ν`
and satisfies both Schrödinger marginal equations pointwise everywhere on `X` and `Y`.

Shifting `(φ₀, ψ₀)` by the single log-partition constant `-ε * log ∫ exp (ψ₀ / ε) dν` produces
*canonical Schrödinger potentials* `(φ, ψ)` (Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré,
Proposition 1; Nutz, §2):

1. **Everywhere marginal normalisation, uniform `L^∞` bounds, and oscillation inheritance
   (`TauCeti.exists_measurable_entropicDualValue_eq`).**
   The canonical potentials satisfy both marginal equations
   `∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1` and
   `∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1` *pointwise everywhere* on `X` and `Y`
   (including off the supports of `μ` and `ν`), obey the temperature-independent bounds
   `0 ≤ φ ≤ B` and `|ψ| ≤ B`, inherit every uniform coordinate oscillation bound of
   `(c ·).toReal`, and attain the regularised transport cost in both the Kantorovich and entropic
   dual objectives.
2. **Slicewise oscillation and Lipschitz regularity, uniformly in the temperature
   (`TauCeti.abs_sub_le_of_integral_entropicGibbsFactor_eq_one`,
   `TauCeti.lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one`,
   `TauCeti.exists_lipschitzWith_entropicDualValue_eq`).**
   Any pair `(φ, ψ)` solving the pointwise `ν`-marginal equation for a finite-valued measurable
   cost satisfies `φ x = -ε * log ∫ exp ((ψ y - (c (x, y)).toReal) / ε) dν(y)`, and therefore
   inherits every uniform slice oscillation bound and slice Lipschitz constant `K` of
   `x ↦ (c (x, y)).toReal` independently of `ε`, without requiring a metric on `Y` or an upper
   bound on `c`.

## Main statements

* `TauCeti.abs_sub_le_of_integral_entropicGibbsFactor_eq_one`: any solution `φ` to the pointwise
  `ν`-marginal equation at `x₁` and `x₂` against a measurable potential `ψ` bounded above inherits
  every uniform slice oscillation bound of `(c ·).toReal` between `x₁` and `x₂`, uniformly in
  `ε ≠ 0`.
* `TauCeti.lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one`: any solution `φ` to the
  pointwise `ν`-marginal equation against a measurable potential `ψ` bounded above inherits the
  slice Lipschitz constant of `x ↦ (c (x, y)).toReal`, uniformly in `ε ≠ 0`.
* `TauCeti.exists_measurable_entropicDualValue_eq`: existence of canonical measurable Schrödinger
  potentials satisfying `0 ≤ φ ≤ B` and `|ψ| ≤ B`, inheriting coordinate oscillation bounds, and
  normalised pointwise everywhere on both `X` and `Y`.
* `TauCeti.exists_lipschitzWith_entropicDualValue_eq`: canonical Schrödinger potentials on extended
  pseudometric spaces inherit the slice Lipschitz constants of the cost in both variables, uniformly
  in `ε ≠ 0`.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Proposition 1.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  §2, for uniform bounds and equicontinuity of Schrödinger potentials.
-/

public section

noncomputable section

open InformationTheory MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

section Softmin

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} {ν : Measure Y}

private theorem integrable_exp_neg_toReal_div_add [IsFiniteMeasure ν] (hc : Measurable c)
    {ψ : Y → ℝ} {Cψ : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, ψ y ≤ Cψ) (x : X) :
    Integrable (fun y ↦ Real.exp (-(c (x, y)).toReal / ε + ψ y / ε)) ν :=
  integrable_exp_add_of_le (h := fun z ↦ -(c z).toReal / ε) (ψ := fun y ↦ ψ y / ε)
    (a := x) (M := 0) (C := Cψ / ε)
    ((hc.comp measurable_prodMk_left).ennreal_toReal.neg.div_const _)
    (fun _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ENNReal.toReal_nonneg) ε.coe_nonneg)
    (hψ.div_const _)
    (fun y ↦ div_le_div_of_nonneg_right (hψC y) ε.coe_nonneg)

private theorem integrable_exp_sub_toReal_div [IsFiniteMeasure ν] (hc : Measurable c)
    {ψ : Y → ℝ} {Cψ : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, ψ y ≤ Cψ) (x : X) :
    Integrable (fun y ↦ Real.exp ((ψ y - (c (x, y)).toReal) / ε)) ν :=
  (integrable_exp_neg_toReal_div_add hc hψ hψC x).congr
    (ae_of_all _ fun y ↦ congrArg Real.exp (by ring))

/-- Pointwise softmin identity: any `(φ, ψ)` solving
`∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1` for a finite-valued measurable cost `c` and a
measurable potential `ψ` bounded above satisfies
`φ x = -ε * logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x`. -/
private theorem eq_neg_mul_logIntegralExp_of_integral_entropicGibbsFactor_eq_one
    [IsFiniteMeasure ν] [NeZero ν] (hc : Measurable c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0)
    {φ : X → ℝ} {ψ : Y → ℝ} {Cψ : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, ψ y ≤ Cψ) {x : X}
    (hrow : ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) :
    φ x = -(ε : ℝ) * logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x := by
  have hε_ne : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  have hint := integrable_exp_neg_toReal_div_add (ν := ν) (ε := ε) hc hψ hψC x
  have hZ : 0 < ∫ y, Real.exp (-(c (x, y)).toReal / ε + ψ y / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ entropicGibbsFactor c ε φ ψ (x, y)) =
      fun y ↦ Real.exp (φ x / ε) * Real.exp (-(c (x, y)).toReal / ε + ψ y / ε) :=
    funext fun y ↦ by
      rw [entropicGibbsFactor_of_ne_top (hfin (x, y)), ← Real.exp_add]
      congr 1
      ring
  rw [hsplit, integral_const_mul] at hrow
  have hlog := congrArg Real.log hrow
  rw [Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp, Real.log_one] at hlog
  have hdiv : φ x / ε = -logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x := by
    rw [logIntegralExp_def]
    linarith
  rw [(div_eq_iff hε_ne).1 hdiv]
  ring

private theorem eq_neg_mul_log_of_integral_entropicGibbsFactor_eq_one [IsFiniteMeasure ν]
    [NeZero ν] (hc : Measurable c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) {φ : X → ℝ} {ψ : Y → ℝ}
    {Cψ : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, ψ y ≤ Cψ) {x : X}
    (hrow : ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) :
    φ x = -(ε : ℝ) * Real.log (∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν) := by
  rw [eq_neg_mul_logIntegralExp_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ hψC hrow,
    logIntegralExp_def]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun y ↦ congrArg Real.exp (by ring))

/-- Shifting a solution `φ₀` of the pointwise `ν`-marginal equation by the log-partition constant
`a = -ε * log ∫ exp (ψ₀ / ε) dν` places `φ₀ x - a` inside `[0, B]` whenever `0 ≤ c ≤ B`. -/
private theorem mem_Icc_sub_neg_mul_log_of_integral_entropicGibbsFactor_eq_one
    [IsFiniteMeasure ν] [NeZero ν] {B : ℝ≥0} (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) {φ₀ : X → ℝ} {ψ₀ : Y → ℝ} {Cψ : ℝ} (hψ₀ : Measurable ψ₀)
    (hψ₀C : ∀ y, ψ₀ y ≤ Cψ) {x : X}
    (hrow : ∫ y, entropicGibbsFactor c ε φ₀ ψ₀ (x, y) ∂ν = 1) :
    0 ≤ φ₀ x - (-(ε : ℝ) * Real.log (∫ y, Real.exp (ψ₀ y / ε) ∂ν)) ∧
      φ₀ x - (-(ε : ℝ) * Real.log (∫ y, Real.exp (ψ₀ y / ε) ∂ν)) ≤ B := by
  have hfin (z : X × Y) : c z ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hφ₀_eq :=
    eq_neg_mul_log_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ₀ hψ₀C hrow
  have hint_a : Integrable (fun y ↦ Real.exp (ψ₀ y / ε)) ν := by
    simpa only [zero_add] using integrable_exp_add_of_le (h := fun _ : Unit × Y ↦ (0 : ℝ))
      (a := ()) (M := 0) (C := Cψ / ε) measurable_const (fun _ ↦ le_rfl) (hψ₀.div_const _)
      fun y ↦ div_le_div_of_nonneg_right (hψ₀C y) ε.coe_nonneg
  have hint_x := integrable_exp_sub_toReal_div (ν := ν) (ε := ε) hc hψ₀ hψ₀C x
  have hhi := mul_log_integral_exp_div_le_add_of_ae_le (δ := B) hε0 hint_a hint_x
    (ae_of_all _ fun y ↦ by linarith [ENNReal.toReal_le_coe_of_le_coe (hcB (x, y))])
  have hlo := mul_log_integral_exp_div_le_add_of_ae_le (δ := 0) hε0 hint_x hint_a
    (ae_of_all _ fun y ↦ by linarith [ENNReal.toReal_nonneg (a := c (x, y))])
  rw [hφ₀_eq]
  exact ⟨by linarith, by linarith⟩

/-- For a probability measure `ν` and a cost `c ≤ B`, a potential `φ` solving the pointwise
`ν`-marginal equation against a measurable potential `ψ` taking values in `[0, B]` satisfies
`|φ x| ≤ B`. -/
private theorem abs_le_of_integral_entropicGibbsFactor_eq_one [IsProbabilityMeasure ν]
    {B : ℝ≥0} (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {φ : X → ℝ} {ψ : Y → ℝ}
    (hψ : Measurable ψ) (hψB : ∀ y, 0 ≤ ψ y ∧ ψ y ≤ B) {x : X}
    (hrow : ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) :
    |φ x| ≤ B := by
  have hfin (z : X × Y) : c z ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hφ_eq := eq_neg_mul_log_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ
    (fun y ↦ (hψB y).2) hrow
  have hint_x := integrable_exp_sub_toReal_div (ν := ν) (ε := ε) hc hψ (fun y ↦ (hψB y).2) x
  have hint_0 : Integrable (fun _ : Y ↦ Real.exp ((0 : ℝ) / ε)) ν := integrable_const _
  have h0_val : (ε : ℝ) * Real.log (∫ _ : Y, Real.exp ((0 : ℝ) / ε) ∂ν) = 0 := by simp
  have hhi := mul_log_integral_exp_div_le_add_of_ae_le (δ := B) hε0 hint_0 hint_x
    (ae_of_all _ fun y ↦ by linarith [(hψB y).1, ENNReal.toReal_le_coe_of_le_coe (hcB (x, y))])
  have hlo := mul_log_integral_exp_div_le_add_of_ae_le (δ := B) hε0 hint_x hint_0
    (ae_of_all _ fun y ↦ by linarith [(hψB y).2, ENNReal.toReal_nonneg (a := c (x, y))])
  rw [hφ_eq, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Oscillation inheritance for Schrödinger marginal solutions.** For any nonzero finite measure
`ν` on `Y`, a finite-valued measurable cost `c`, and a pair `(φ, ψ)` with `ψ` measurable and bounded
above solving the `ν`-marginal equation at `x₁` and `x₂`, `|φ x₁ - φ x₂|` is bounded by any uniform
`Y`-slice oscillation bound `δ` of `(c (x₁, ·)).toReal - (c (x₂, ·)).toReal`, independently of
`ε ≠ 0` and `ν`, and with no upper bound on `c`. -/
theorem abs_sub_le_of_integral_entropicGibbsFactor_eq_one [IsFiniteMeasure ν] [NeZero ν]
    (hc : Measurable c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) {φ : X → ℝ} {ψ : Y → ℝ} {Cψ : ℝ}
    (hψ : Measurable ψ) (hψC : ∀ y, ψ y ≤ Cψ) {x₁ x₂ : X} {δ : ℝ}
    (hrow₁ : ∫ y, entropicGibbsFactor c ε φ ψ (x₁, y) ∂ν = 1)
    (hrow₂ : ∫ y, entropicGibbsFactor c ε φ ψ (x₂, y) ∂ν = 1)
    (hosc : ∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) :
    |φ x₁ - φ x₂| ≤ δ := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hφ₁ := eq_neg_mul_logIntegralExp_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ hψC
    hrow₁
  have hφ₂ := eq_neg_mul_logIntegralExp_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ hψC
    hrow₂
  have hlog := abs_logIntegralExp_sub_le (ν := ν) (h := fun z ↦ -(c z).toReal / ε)
    (ψ := fun y ↦ ψ y / ε) (NeZero.ne ν)
    (integrable_exp_neg_toReal_div_add hc hψ hψC x₁)
    (integrable_exp_neg_toReal_div_add hc hψ hψC x₂) (δ := δ / ε) fun y ↦ by
      rw [← sub_div, neg_sub_neg, abs_div, abs_sub_comm, abs_of_pos hε0]
      exact div_le_div_of_nonneg_right (hosc y) hε0.le
  have hdiff : φ x₁ - φ x₂ = -(ε : ℝ) *
      (logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x₁ -
        logIntegralExp (fun z ↦ -(c z).toReal / ε) ν (fun y ↦ ψ y / ε) x₂) := by
    rw [hφ₁, hφ₂]
    ring
  rw [hdiff, abs_mul, abs_neg, abs_of_pos hε0]
  exact (mul_le_mul_of_nonneg_left hlog hε0.le).trans_eq (mul_div_cancel₀ δ hε0.ne')

/-- **Lipschitz regularity of Schrödinger marginal solutions.** For any nonzero finite measure `ν`
on a measurable space `Y`, a finite-valued measurable cost `c` whose source slices
`x ↦ (c (x, y)).toReal` are `K`-Lipschitz on an extended pseudometric space `X`, and any pair
`(φ, ψ)` with `ψ` measurable and bounded above solving
`∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1`, the source potential `φ` is `K`-Lipschitz,
uniformly in `ε ≠ 0` and with no metric on `Y` or upper bound on `c`. -/
theorem lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one [PseudoEMetricSpace X]
    [IsFiniteMeasure ν] [NeZero ν] {K : ℝ≥0} (hc : Measurable c) (hfin : ∀ z, c z ≠ ∞)
    (hε : ε ≠ 0) (hL : ∀ y, LipschitzWith K fun x ↦ (c (x, y)).toReal) {φ : X → ℝ} {ψ : Y → ℝ}
    {Cψ : ℝ} (hψ : Measurable ψ) (hψC : ∀ y, ψ y ≤ Cψ)
    (hrow : ∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) :
    LipschitzWith K φ := by
  intro x x'
  rcases eq_or_ne K 0 with rfl | hK
  · have h0 : |φ x - φ x'| ≤ 0 :=
      abs_sub_le_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ hψC (hrow x) (hrow x')
        fun y ↦ by
          have hy := (hL y) x x'
          rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at hy
          simp [hy]
    simp [sub_eq_zero.1 (abs_nonpos_iff.1 h0)]
  rcases eq_or_ne (edist x x') ∞ with htop | hd_fin
  · rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hK)]
    exact le_top
  have habs : |φ x - φ x'| ≤ K * (edist x x').toReal :=
    abs_sub_le_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ hψC (hrow x) (hrow x')
      fun y ↦ le_coe_mul_of_ofReal_le (by simpa only [edist_dist, Real.dist_eq] using (hL y) x x')
        hd_fin
  have hKd_ne_top : (K : ℝ≥0∞) * edist x x' ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hd_fin
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_toReal hKd_ne_top, ENNReal.toReal_mul,
    ENNReal.coe_toReal]
  exact ENNReal.ofReal_le_ofReal habs

end Softmin

section CanonicalPotentials

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0} {μ : Measure X} {ν : Measure Y}

/-- **Canonical measurable Schrödinger potentials for a bounded cost.** For probability measures
`μ` and `ν`, a measurable cost bounded by `B` and a positive temperature `ε`, there exist measurable
potentials `φ` and `ψ` that satisfy `0 ≤ φ ≤ B` and `|ψ| ≤ B` everywhere, inherit every uniform
coordinate oscillation bound of `(c ·).toReal`, solve both Schrödinger marginal equations pointwise
everywhere on `X` and `Y`, and attain the regularised transport cost in both the Kantorovich and
entropic dual objectives.

This establishes Proposition 1 of Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré (2019), together with
the two-sided everywhere fixed-point equations. -/
theorem exists_measurable_entropicDualValue_eq
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x₁ x₂ δ, (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) →
        |φ x₁ - φ x₂| ≤ δ) ∧
      (∀ y₁ y₂ δ, (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) →
        |ψ y₁ - ψ y₂| ≤ δ) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  have hfin (z : X × Y) : c z ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  -- Start from bounded Schrödinger potentials `(φ₀, ψ₀)` realising an optimal coupling `π`, and
  -- shift by the log-partition constant `a` to normalise `φ` into `[0, B]`.
  obtain ⟨π, hπ, hopt, φ₀, ψ₀, _, hφ₀, hψ₀, _, hψ₀C, hrow₀, hcol₀, hπeq⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost (μ := μ) (ν := ν) hc hcB hε
  set a : ℝ := -(ε : ℝ) * Real.log (∫ y, Real.exp (ψ₀ y / ε) ∂ν)
  set φ : X → ℝ := fun x ↦ φ₀ x - a
  set ψ : Y → ℝ := fun y ↦ ψ₀ y + a
  have hφ : Measurable φ := hφ₀.sub_const a
  have hψ : Measurable ψ := hψ₀.add_const a
  have hfactor : entropicGibbsFactor c ε φ ψ = entropicGibbsFactor c ε φ₀ ψ₀ := by
    simpa only [φ, ψ, sub_eq_add_neg, neg_neg] using
      entropicGibbsFactor_add_const_sub_const (c := c) (ε := ε) (φ := φ₀) (ψ := ψ₀) (-a)
  have hrow₀' (x : X) : ∫ y, entropicGibbsFactor c ε φ₀ ψ₀ (x, y) ∂ν = 1 := by
    simpa only [entropicGibbsFactor_of_ne_top (hfin _)] using hrow₀ x
  have hrow (x : X) : ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1 := by
    simpa only [hfactor] using hrow₀' x
  have hcol (y : Y) : ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1 := by
    rw [hfactor]; simpa only [entropicGibbsFactor_of_ne_top (hfin _)] using hcol₀ y
  have hcol_swap (y : Y) : ∫ x, entropicGibbsFactor (c ∘ Prod.swap) ε ψ φ (y, x) ∂μ = 1 := by
    simpa only [entropicGibbsFactor_comp_swap, Function.comp_apply, Prod.swap_prod_mk] using hcol y
  -- Derive `0 ≤ φ ≤ B` and `|ψ| ≤ B`, then evaluate the dual objectives by complementary slackness.
  have hφB (x : X) : 0 ≤ φ x ∧ φ x ≤ B :=
    mem_Icc_sub_neg_mul_log_of_integral_entropicGibbsFactor_eq_one hc hcB hε hψ₀
      (fun y ↦ le_of_abs_le (hψ₀C y)) (hrow₀' x)
  have hψB (y : Y) : |ψ y| ≤ B :=
    abs_le_of_integral_entropicGibbsFactor_eq_one (c := c ∘ Prod.swap) (ν := μ)
      (hc.comp measurable_swap) (fun w ↦ hcB w.swap) hε hφ hφB (hcol_swap y)
  have hπ_new : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) := by
    rw [hfactor, entropicGibbsFactor_eq_exp_of_forall_ne_top hfin, hπeq]
  have hφi : Integrable φ μ := .of_bound hφ.aestronglyMeasurable B
    (ae_of_all _ fun x ↦ abs_le.2 ⟨by linarith [(hφB x).1, B.coe_nonneg], (hφB x).2⟩)
  have hψi : Integrable ψ ν := .of_bound hψ.aestronglyMeasurable B (ae_of_all _ hψB)
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ hψ
    (fun x ↦ (hφB x).2) (fun y ↦ le_of_abs_le (hψB y))
  have hent_val : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
    rw [← hopt]
    exact (hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc.aemeasurable hε hφi hψi
      hexp (hopt ▸ entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).2 hπ_new
  refine ⟨φ, ψ, hφ, hψ, hφB, hψB,
    fun x₁ x₂ _ h ↦ abs_sub_le_of_integral_entropicGibbsFactor_eq_one hc hfin hε hψ
      (fun y ↦ le_of_abs_le (hψB y)) (hrow x₁) (hrow x₂) h,
    fun y₁ y₂ _ h ↦ abs_sub_le_of_integral_entropicGibbsFactor_eq_one (c := c ∘ Prod.swap) (ν := μ)
      (hc.comp measurable_swap) (fun w ↦ hfin w.swap) hε hφ (fun x ↦ (hφB x).2)
      (hcol_swap y₁) (hcol_swap y₂) h,
    hrow, hcol, by rw [← hπ.entropicDualValue_eq_of_eq_withDensity hπ_new hexp, hent_val], hent_val⟩

/-- **Lipschitz regularity of canonical Schrödinger potentials (Feydy et al., Proposition 1).** On
extended pseudometric spaces, when the cost is bounded by `B` and its slices are `K₁`- and
`K₂`-Lipschitz, the canonical Schrödinger potentials of `exists_measurable_entropicDualValue_eq`
are themselves `K₁`- and `K₂`-Lipschitz, uniformly in the temperature `ε ≠ 0`. -/
theorem exists_lipschitzWith_entropicDualValue_eq
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K₁ K₂ : ℝ≥0} (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      LipschitzWith K₁ φ ∧ LipschitzWith K₂ ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  have hfin (z : X × Y) : c z ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  obtain ⟨φ, ψ, hφ, hψ, hφB, hψB, -, -, hrow, hcol, hkant, hent⟩ :=
    exists_measurable_entropicDualValue_eq (μ := μ) (ν := ν) hc hcB hε
  have hφL : LipschitzWith K₁ φ :=
    lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one hc hfin hε hL₁ hψ
      (fun y ↦ le_of_abs_le (hψB y)) hrow
  have hψL : LipschitzWith K₂ ψ :=
    lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one (c := c ∘ Prod.swap)
      (hc.comp measurable_swap) (fun w ↦ hfin w.swap) hε hL₂ hφ (fun x ↦ (hφB x).2) fun y ↦ by
        simpa only [entropicGibbsFactor_comp_swap, Function.comp_apply, Prod.swap_prod_mk] using
          hcol y
  exact ⟨φ, ψ, hφ, hψ, hφL, hψL, hφB, hψB, hrow, hcol, hkant, hent⟩

end CanonicalPotentials

end TauCeti
