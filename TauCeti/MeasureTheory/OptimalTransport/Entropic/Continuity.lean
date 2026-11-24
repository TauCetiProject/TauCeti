/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Potentials
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import TauCeti.Basic.ENNReal.Real
import TauCeti.MeasureTheory.Constructions.BorelSpace.Prod
import TauCeti.MeasureTheory.OptimalTransport.Entropic.ZeroTemperature
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.BoundedLipschitz
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein
import TauCeti.Topology.ContinuousMap.Compact
import TauCeti.Topology.Instances.ENNReal
import TauCeti.Topology.MetricSpace.Equicontinuity

/-!
# Quantitative stability and weak continuity of entropic optimal transport

On Polish spaces, the entropically regularised transport cost
`TauCeti.entropicTransportCost c ε μ ν` of a lower semicontinuous cost is jointly weakly lower
semicontinuous in its marginals (`TauCeti.lowerSemicontinuous_entropicTransportCost`). Weak
convergence of the marginals does not give the matching upper bound by primal compactness alone,
because the reference measure `μ ⊗ ν` of the relative entropy moves with the marginals.

At positive temperature `ε ≠ 0` and for a bounded cost `c ≤ B`, canonical Schrödinger potentials
(`TauCeti.MeasureTheory.OptimalTransport.Entropic.Potentials`) supply continuous potentials on
compact spaces, quantitative `W₁`-Lipschitz stability, and joint weak continuity, following
Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré, Propositions 1 and 2:

1. **Continuous canonical potentials on compact spaces
   (`TauCeti.exists_continuous_entropicDualValue_eq`).**
   On compact spaces `X` and `Y` with measurable opens on each factor, a continuous cost bounded by
   `B` is automatically product-measurable
   (`Continuous.measurable_prod_of_sigmaCompact_of_compact`),
   and the tube-lemma equicontinuity criterion (`Metric.equicontinuous_of_forall_dist_le`) upgrades
   the canonical measurable potentials of `TauCeti.exists_measurable_entropicDualValue_eq` to
   continuous potentials satisfying `0 ≤ φ ≤ B`, `|ψ| ≤ B`, and both marginal equations everywhere.
2. **Temperature-independent `W₁` stability
   (`TauCeti.ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one`).**
   Evaluating weak duality for `(μ, ν')` at the canonical potentials `(φ', ψ')` of `(μ', ν')` and
   transferring slicewise Lipschitz regularity via
   `TauCeti.lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one`, the exponential penalty
   vanishes identically because `φ'` solves the `ν'`-marginal equation at every point of `X`, even
   off the support of `μ'`. Thus `OT_ε(μ', ν') - OT_ε(μ, ν') ≤ ∫ φ' d(μ' - μ) ≤ K₁ W₁(μ', μ)`,
   with no factor depending on `ε` or `B`. Combining with the symmetric target estimate yields
   `|OT_ε(μ', ν') - OT_ε(μ, ν)| ≤ K₁ W₁(μ', μ) + K₂ W₁(ν', ν)`.
3. **Joint weak continuity (`TauCeti.continuous_entropicTransportCost_of_lipschitzWith`,
   `TauCeti.continuous_entropicTransportCost`).**
   Because `0 ≤ φ' ≤ B`, centering `φ'` by `B / 2` also bounds the difference by truncated optimal
   transport
   (`TauCeti.abs_integral_sub_integral_le_add_one_mul_toReal_transportCost_truncated_dist`),
   which metrises weak convergence on separable pseudometric spaces without moment assumptions
   (`TauCeti.tendsto_probabilityMeasure_iff_transportCost_truncated_dist`). Because the truncated
   transport bound is independent of `ε`, passing `ε → 0⁺` via
   `TauCeti.tendsto_entropicTransportCost_transportCost_of_continuous` extends weak continuity on
   compact pseudometric spaces to `ε = 0`. On arbitrary compact spaces `X` and `Y` with measurable
   opens on each factor, factoring a continuous finite cost through compact pseudometric ranges
   (`ContinuousMap.exists_factor_lipschitzWith_one`,
   `TauCeti.entropicTransportCost_comp_prodMap_of_continuous`) yields joint weak continuity at every
   temperature `ε : ℝ≥0` with neither metrisability nor `[OpensMeasurableSpace (X × Y)]`.

## Main statements

* `TauCeti.exists_continuous_entropicDualValue_eq`: existence of continuous canonical Schrödinger
  potentials on compact spaces satisfying `0 ≤ φ ≤ B`, `|ψ| ≤ B`, coordinate oscillation bounds, and
  both pointwise marginal equations.
* `TauCeti.ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one` and
  `TauCeti.abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one`: `W₁`-Lipschitz stability
  of entropic optimal transport on extended pseudometric spaces.
* `TauCeti.continuous_toReal_entropicTransportCost_of_lipschitzWith` and
  `TauCeti.continuous_entropicTransportCost_of_lipschitzWith`: joint weak continuity on separable
  pseudometric spaces for bounded slicewise-Lipschitz costs.
* `TauCeti.continuous_toReal_entropicTransportCost` and
  `TauCeti.continuous_entropicTransportCost`: joint weak continuity on compact spaces for arbitrary
  continuous finite costs at every temperature `ε : ℝ≥0`.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Propositions 1 and 2.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  §2.
-/

public section

noncomputable section

open Filter InformationTheory MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section ContinuousPotentials

/-- **Existence of continuous canonical Schrödinger potentials on compact spaces.** For probability
measures on compact spaces `X` and `Y` with measurable opens on each factor, a continuous cost
bounded by `B`, and a positive temperature `ε`, the entropic dual problem is attained by continuous
potentials `(φ, ψ)` satisfying `0 ≤ φ ≤ B` and `|ψ| ≤ B`, inheriting every uniform coordinate
oscillation bound of `(c ·).toReal`, solving both Schrödinger marginal equations pointwise
everywhere on `X` and `Y`, and attaining `(entropicTransportCost c ε μ ν).toReal` in both the
Kantorovich and entropic dual objectives. -/
theorem exists_continuous_entropicDualValue_eq
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0} {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Continuous c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Continuous φ ∧ Continuous ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x₁ x₂ δ, (∀ y, |(c (x₁, y)).toReal - (c (x₂, y)).toReal| ≤ δ) →
        |φ x₁ - φ x₂| ≤ δ) ∧
      (∀ y₁ y₂ δ, (∀ x, |(c (x, y₁)).toReal - (c (x, y₂)).toReal| ≤ δ) →
        |ψ y₁ - ψ y₂| ≤ δ) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  have hfin : ∀ z, c z ≠ ∞ := fun z ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  have hc_real : Continuous fun z ↦ (c z).toReal := hc.ennreal_toReal hfin
  obtain ⟨φ, ψ, -, -, hφB, hψB, hφ_osc, hψ_osc, hrow, hcol, hkant, hent⟩ :=
    exists_measurable_entropicDualValue_eq (μ := μ) (ν := ν)
      hc.measurable_prod_of_sigmaCompact_of_compact hcB hε
  have hφc : Continuous φ :=
    (Metric.equicontinuous_of_forall_dist_le (F := fun _ : Unit ↦ φ) (L := 1) hc_real
      fun x₁ x₂ δ _ h _ ↦ by
        simpa only [Real.dist_eq, one_mul] using
          hφ_osc x₁ x₂ δ (by simpa only [Real.dist_eq] using h)).continuous ()
  have hψc : Continuous ψ :=
    (Metric.equicontinuous_of_forall_dist_le (F := fun _ : Unit ↦ ψ) (L := 1)
      (hc_real.comp continuous_swap) fun y₁ y₂ δ _ h _ ↦ by
        simpa only [Real.dist_eq, one_mul] using hψ_osc y₁ y₂ δ
          (by simpa only [Real.dist_eq, Function.comp_apply, Prod.swap_prod_mk] using h)).continuous
      ()
  exact ⟨φ, ψ, hφc, hψc, hφB, hψB, hφ_osc, hψ_osc, hrow, hcol, hkant, hent⟩

end ContinuousPotentials

section MarginalStability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0} {μ μ' : Measure X} {ν ν' : Measure Y}

/-- Varying only the source marginal from `μ'` to `μ` increases the regularised cost by at most
the difference of expectations of the `K₁`-Lipschitz canonical source potential of `(μ', ν)`. -/
private theorem exists_lipschitzWith_source_potential_diff_bound [PseudoEMetricSpace X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ∃ φ' : X → ℝ, Measurable φ' ∧ LipschitzWith K₁ φ' ∧ (∀ x, 0 ≤ φ' x ∧ φ' x ≤ B) ∧
      (∀ ρ : Measure X, [IsFiniteMeasure ρ] → Integrable φ' ρ) ∧
      (entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal ≤
        ∫ x, φ' x ∂μ' - ∫ x, φ' x ∂μ := by
  have hfin (z : X × Y) : c z ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  obtain ⟨φ', ψ', hφ', hψ', hφ'B, hψ'B, -, -, hrow, -, hkant, -⟩ :=
    exists_measurable_entropicDualValue_eq (μ := μ') (ν := ν) hc hcB hε
  have hφ'L : LipschitzWith K₁ φ' :=
    lipschitzWith_of_forall_integral_entropicGibbsFactor_eq_one hc hfin hε hL₁ hψ'
      (fun y ↦ le_of_abs_le (hψ'B y)) hrow
  have hφ'abs : ∀ x, |φ' x| ≤ B := fun x ↦
    abs_le.2 ⟨by linarith [(hφ'B x).1, B.coe_nonneg], (hφ'B x).2⟩
  have hφ'i (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable φ' ρ :=
    .of_bound hφ'.aestronglyMeasurable B (ae_of_all _ hφ'abs)
  have hψ'ν : Integrable ψ' ν := .of_bound hψ'.aestronglyMeasurable B (ae_of_all _ hψ'B)
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ' hψ'
    (fun x ↦ (hφ'B x).2) (fun y ↦ le_of_abs_le (hψ'B y))
  have hint_one : ∫ z, entropicGibbsFactor c ε φ' ψ' z ∂μ.prod ν = 1 := by
    rw [integral_prod _ hexp]
    simp [hrow]
  have hdual := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε
    (hφ'i μ) hψ'ν hexp
  rw [entropicDualValue_def, integral_sub hexp (integrable_const _), hint_one] at hdual
  simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero, sub_zero] at hdual
  rw [kantorovichDualValue_def] at hkant hdual
  exact ⟨φ', hφ', hφ'L, hφ'B, hφ'i, by linarith⟩

/-- Source-marginal `W₁` stability of entropic optimal transport, in `ℝ≥0∞`. -/
private theorem ofReal_abs_toReal_entropicTransportCost_sub_left_le_wassersteinEDist_one
    [PseudoEMetricSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ENNReal.ofReal |(entropicTransportCost c ε μ' ν).toReal -
        (entropicTransportCost c ε μ ν).toReal| ≤
      K₁ * wassersteinEDist 1 μ' μ := by
  obtain ⟨φ₁, _, hφ₁L, _, hφ₁i, hle₁⟩ :=
    exists_lipschitzWith_source_potential_diff_bound (μ := μ) (μ' := μ') (ν := ν) hc hcB hL₁ hε
  obtain ⟨φ₂, _, hφ₂L, _, hφ₂i, hle₂⟩ :=
    exists_lipschitzWith_source_potential_diff_bound (μ := μ') (μ' := μ) (ν := ν) hc hcB hL₁ hε
  rcases le_total (entropicTransportCost c ε μ ν).toReal
      (entropicTransportCost c ε μ' ν).toReal with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact (ENNReal.ofReal_le_ofReal (hle₁.trans (le_abs_self _))).trans
      (ofReal_abs_integral_sub_integral_le_mul_wassersteinEDist_one (by simp) hφ₁L
        (hφ₁i μ') (hφ₁i μ))
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact (ENNReal.ofReal_le_ofReal
        (hle₂.trans ((le_abs_self _).trans_eq (abs_sub_comm _ _)))).trans
      (ofReal_abs_integral_sub_integral_le_mul_wassersteinEDist_one (by simp) hφ₂L
        (hφ₂i μ') (hφ₂i μ))

/-- **`W₁`-Lipschitz stability of entropic optimal transport, in `ℝ≥0∞`
(Feydy et al., Proposition 2).** On extended pseudometric spaces, for probability marginals, a
measurable cost bounded by `B` with `K₁`- and `K₂`-Lipschitz slices, and a positive temperature
`ε`, the regularised transport cost is `(K₁, K₂)`-Lipschitz with respect to the `1`-Wasserstein
distance, with constants independent of `ε` and `B`. No measurability of the ground distances and
no finiteness of `W₁` is required. -/
theorem ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ENNReal.ofReal |(entropicTransportCost c ε μ' ν').toReal -
        (entropicTransportCost c ε μ ν).toReal| ≤
      K₁ * wassersteinEDist 1 μ' μ + K₂ * wassersteinEDist 1 ν' ν := by
  have htri : |(entropicTransportCost c ε μ' ν').toReal -
      (entropicTransportCost c ε μ ν).toReal| ≤
      |(entropicTransportCost c ε μ' ν').toReal - (entropicTransportCost c ε μ ν').toReal| +
        |(entropicTransportCost c ε μ ν').toReal - (entropicTransportCost c ε μ ν).toReal| :=
    abs_sub_le _ _ _
  refine (ENNReal.ofReal_le_ofReal htri).trans (ENNReal.ofReal_add_le.trans ?_)
  gcongr
  · exact ofReal_abs_toReal_entropicTransportCost_sub_left_le_wassersteinEDist_one hc hcB hL₁ hε
  · rw [← entropicTransportCost_comp_swap c ε ν', ← entropicTransportCost_comp_swap c ε ν]
    exact ofReal_abs_toReal_entropicTransportCost_sub_left_le_wassersteinEDist_one
      (hc.comp measurable_swap) (fun w ↦ hcB w.swap) hL₂ hε

/-- **`W₁`-Lipschitz stability of entropic optimal transport, in real form
(Feydy et al., Proposition 2).** When the two `1`-Wasserstein distances are finite, the difference
of regularised transport costs is bounded by `K₁ * W₁(μ', μ) + K₂ * W₁(ν', ν)`. -/
theorem abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0)
    (hw₁ : wassersteinEDist 1 μ' μ ≠ ∞) (hw₂ : wassersteinEDist 1 ν' ν ≠ ∞) :
    |(entropicTransportCost c ε μ' ν').toReal - (entropicTransportCost c ε μ ν).toReal| ≤
      K₁ * (wassersteinEDist 1 μ' μ).toReal + K₂ * (wassersteinEDist 1 ν' ν).toReal :=
  le_coe_mul_add_coe_mul_of_ofReal_le
    (ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one hc hcB hL₁ hL₂ hε) hw₁ hw₂

/-- Source-marginal stability of entropic optimal transport in terms of truncated optimal
transport, with no moment assumption. -/
private theorem abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
    [PseudoMetricSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    |(entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal| ≤
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal := by
  obtain ⟨φ₁, _, hφ₁L, hφ₁B, -, hle₁⟩ :=
    exists_lipschitzWith_source_potential_diff_bound (μ := μ) (μ' := μ') (ν := ν) hc hcB hL₁ hε
  obtain ⟨φ₂, _, hφ₂L, hφ₂B, -, hle₂⟩ :=
    exists_lipschitzWith_source_potential_diff_bound (μ := μ') (μ' := μ) (ν := ν) hc hcB hL₁ hε
  have hcent {φ : X → ℝ} (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ B) (x : X) :
      ‖φ x - (B : ℝ) / 2‖ ≤ ((B : ℝ) + 1) / 2 := by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [(hb x).1], by linarith [(hb x).2]⟩
  have hcap : 2 * (((B : ℝ) + 1) / 2) / (K₁ + 1 : ℝ) = ((B : ℝ) + 1) / (K₁ + 1 : ℝ) := by ring
  have hb₁ : (entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal ≤
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal := by
    refine (hle₁.trans (le_abs_self _)).trans ?_
    simpa only [hcap] using
      abs_integral_sub_integral_le_add_one_mul_toReal_transportCost_truncated_dist
        (μ := μ') (ν := μ) hφ₁L (hcent hφ₁B)
  have hb₂ : (entropicTransportCost c ε μ ν).toReal - (entropicTransportCost c ε μ' ν).toReal ≤
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal := by
    refine (hle₂.trans (le_abs_self _)).trans ((abs_sub_comm _ _).trans_le ?_)
    simpa only [hcap] using
      abs_integral_sub_integral_le_add_one_mul_toReal_transportCost_truncated_dist
        (μ := μ') (ν := μ) hφ₂L (hcent hφ₂B)
  exact abs_sub_le_iff.2 ⟨hb₁, hb₂⟩

end MarginalStability

section WeakContinuity

private theorem continuous_of_abs_sub_le_transportCost_truncated_dist
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0}
    (hleft : ∀ (μ μ' : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν],
      |(entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal| ≤
        (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
          ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal)
    (hright : ∀ (ν ν' : Measure Y) (μ : Measure X) [IsProbabilityMeasure ν]
      [IsProbabilityMeasure ν'] [IsProbabilityMeasure μ],
      |(entropicTransportCost c ε μ ν').toReal - (entropicTransportCost c ε μ ν).toReal| ≤
        (K₂ + 1 : ℝ) * (transportCost (fun z : Y × Y ↦
          ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₂ + 1)))) ν' ν).toReal) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  set R₁ : ℝ := ((B : ℝ) + 1) / (2 * (K₁ + 1 : ℝ))
  set R₂ : ℝ := ((B : ℝ) + 1) / (2 * (K₂ + 1 : ℝ))
  have hR₁ : 0 < R₁ := by positivity
  have hR₂ : 0 < R₂ := by positivity
  have h2R₁ : 2 * R₁ = ((B : ℝ) + 1) / (K₁ + 1 : ℝ) := by dsimp [R₁]; field_simp
  have h2R₂ : 2 * R₂ = ((B : ℝ) + 1) / (K₂ + 1 : ℝ) := by dsimp [R₂]; field_simp
  -- Truncated transport costs metrise weak convergence on both factors.
  have ht₁ : Tendsto (fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R₁)))
        q.1.toMeasure q₀.1.toMeasure).toReal) (𝓝 q₀) (𝓝 0) := by
    have h := (tendsto_probabilityMeasure_iff_transportCost_truncated_dist (R := R₁) hR₁).1
      (continuous_fst.tendsto q₀)
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rwa [ENNReal.toReal_zero] at h0
  have ht₂ : Tendsto (fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (transportCost (fun z : Y × Y ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R₂)))
        q.2.toMeasure q₀.2.toMeasure).toReal) (𝓝 q₀) (𝓝 0) := by
    have h := (tendsto_probabilityMeasure_iff_transportCost_truncated_dist (R := R₂) hR₂).1
      (continuous_snd.tendsto q₀)
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rwa [ENNReal.toReal_zero] at h0
  have hub : Tendsto (fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R₁)))
        q.1.toMeasure q₀.1.toMeasure).toReal +
      (K₂ + 1 : ℝ) * (transportCost (fun z : Y × Y ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R₂)))
        q.2.toMeasure q₀.2.toMeasure).toReal) (𝓝 q₀) (𝓝 0) := by
    simpa using (ht₁.const_mul (K₁ + 1 : ℝ)).add (ht₂.const_mul (K₂ + 1 : ℝ))
  -- Combine the separate left and right bounds by the triangle inequality.
  refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
  filter_upwards [hub.eventually (gt_mem_nhds hδ)] with q hq
  rw [Real.dist_eq]
  have hb₁ := hleft q₀.1.toMeasure q.1.toMeasure q.2.toMeasure
  have hb₂ := hright q₀.2.toMeasure q.2.toMeasure q₀.1.toMeasure
  rw [← h2R₁] at hb₁
  rw [← h2R₂] at hb₂
  exact ((abs_sub_le _ (entropicTransportCost c ε q₀.1.toMeasure q.2.toMeasure).toReal _).trans
    (add_le_add hb₁ hb₂)).trans_lt hq

/-- **Joint weak continuity of entropic optimal transport for bounded slicewise-Lipschitz costs.**
On separable pseudometric spaces whose open sets are measurable (for instance Polish spaces with
their Borel σ-algebras), for a measurable cost bounded by `B` with `K₁`- and `K₂`-Lipschitz slices
and a positive temperature `ε`, the real-valued regularised transport cost is jointly continuous on
`ProbabilityMeasure X × ProbabilityMeasure Y`. No compactness or moment assumption is needed. -/
theorem continuous_toReal_entropicTransportCost_of_lipschitzWith
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0}
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal :=
  continuous_of_abs_sub_le_transportCost_truncated_dist
    (fun μ μ' ν _ _ _ ↦
      abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
        (μ := μ) (μ' := μ') (ν := ν) hc hcB hL₁ hε)
    (fun ν ν' μ _ _ _ ↦ by
      have hb := abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
        (c := c ∘ Prod.swap) (μ := ν) (μ' := ν') (ν := μ)
        (hc.comp measurable_swap) (fun w ↦ hcB w.swap) hL₂ hε
      rwa [entropicTransportCost_comp_swap c ε ν', entropicTransportCost_comp_swap c ε ν] at hb)

/-- **Joint weak continuity of entropic optimal transport in `ℝ≥0∞`, for bounded
slicewise-Lipschitz costs.** -/
theorem continuous_entropicTransportCost_of_lipschitzWith
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [PseudoMetricSpace Y] [TopologicalSpace.SeparableSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0}
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure := by
  have heq : (fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure) =
      fun q ↦ ENNReal.ofReal (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal :=
    funext fun _ ↦ (ENNReal.ofReal_toReal
      (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp
    (continuous_toReal_entropicTransportCost_of_lipschitzWith hc hcB hL₁ hL₂ hε)

private theorem abs_toReal_entropicTransportCost_sub_left_le_of_compact
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {b : X × Y → ℝ≥0} {ε B K₁ : ℝ≥0} (hb : Continuous b)
    (hbB : ∀ z, b z ≤ B) (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (b (x, y) : ℝ))
    (μ μ' : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] :
    |(entropicTransportCost (fun z ↦ (b z : ℝ≥0∞)) ε μ' ν).toReal -
        (entropicTransportCost (fun z ↦ (b z : ℝ≥0∞)) ε μ ν).toReal| ≤
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal := by
  set c : X × Y → ℝ≥0∞ := fun z ↦ (b z : ℝ≥0∞) with c_def
  have hc : Measurable c := (ENNReal.continuous_coe.comp hb).measurable
  have hcB : ∀ z, c z ≤ B := fun z ↦ ENNReal.coe_le_coe.2 (hbB z)
  have hcL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal := by
    simpa only [c_def, ENNReal.coe_toReal] using hL₁
  rcases eq_or_ne ε 0 with rfl | hε
  · have htend (ρ : Measure X) [IsProbabilityMeasure ρ] :
        Tendsto (fun ε' : ℝ≥0 ↦ (entropicTransportCost c ε' ρ ν).toReal) (𝓝[>] 0)
          (𝓝 (entropicTransportCost c 0 ρ ν).toReal) := by
      have h0 : transportCost c ρ ν = entropicTransportCost c 0 ρ ν :=
        entropicTransportCost_zero.symm
      have hfin : transportCost c ρ ν ≠ ∞ :=
        h0 ▸ entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) 0
      simpa only [Function.comp_def, ← c_def, h0] using (ENNReal.tendsto_toReal hfin).comp
        (tendsto_entropicTransportCost_transportCost_of_continuous hb ρ ν)
    exact le_of_tendsto ((htend μ').sub (htend μ)).abs
      (eventually_nhdsWithin_of_forall fun ε' hε' ↦
        abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
          (μ := μ) (μ' := μ') (ν := ν) hc hcB hcL₁ (mem_Ioi.1 hε').ne')
  · exact abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
      (μ := μ) (μ' := μ') (ν := ν) hc hcB hcL₁ hε

/-- **Joint weak continuity of entropic optimal transport on compact spaces.** For arbitrary
compact topological spaces `X` and `Y` whose open sets are measurable (with neither metrisability
nor `[OpensMeasurableSpace (X × Y)]`), a continuous finite-valued cost `c`, and any temperature
`ε : ℝ≥0` (including the unregularised Kantorovich transport cost at `ε = 0`), the real-valued
regularised transport cost is jointly continuous on
`ProbabilityMeasure X × ProbabilityMeasure Y`. -/
theorem continuous_toReal_entropicTransportCost
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} (hc : Continuous c)
    (hfin : ∀ z, c z ≠ ∞) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal := by
  obtain ⟨B, hB⟩ := hc.exists_forall_le_coe_of_ne_top hfin
  -- Factor `c.toReal` through continuous surjections `Φ : X → K`, `Ψ : Y → L` onto compact
  -- pseudometric spaces with a continuous reduced cost `g : K × L → ℝ` whose slices are
  -- `1`-Lipschitz in both variables.
  let f : C(X × Y, ℝ) := ⟨fun z ↦ (c z).toReal, hc.ennreal_toReal hfin⟩
  obtain ⟨K, L, _, _, _, _, Φ, Ψ, g, hΦc, hΦs, hΨc, hΨs, hgc, hgL₁, hgL₂, hfg⟩ :=
    f.exists_factor_lipschitzWith_one
  borelize K L
  have hg_surj : ∀ w : K × L, ∃ x y, g w = (c (x, y)).toReal := fun ⟨k, l⟩ ↦ by
    obtain ⟨x, rfl⟩ := hΦs k
    obtain ⟨y, rfl⟩ := hΨs l
    exact ⟨x, y, hfg x y⟩
  have hg0 (w : K × L) : 0 ≤ g w := by
    obtain ⟨x, y, hxy⟩ := hg_surj w
    exact hxy ▸ ENNReal.toReal_nonneg
  let b : K × L → ℝ≥0 := fun w ↦ ⟨g w, hg0 w⟩
  have hbc : Continuous b := Continuous.subtype_mk hgc hg0
  have hbB (w : K × L) : b w ≤ B := by
    obtain ⟨x, y, hxy⟩ := hg_surj w
    exact Subtype.mk_le_mk.2 (hxy ▸ ENNReal.toReal_le_coe_of_le_coe (hB (x, y)))
  -- On `K × L`, `b` has `1`-Lipschitz slices, so weak continuity holds at every `ε : ℝ≥0`.
  have hcontKL : Continuous fun q' : ProbabilityMeasure K × ProbabilityMeasure L ↦
      (entropicTransportCost (fun w ↦ (b w : ℝ≥0∞)) ε q'.1.toMeasure q'.2.toMeasure).toReal :=
    continuous_of_abs_sub_le_transportCost_truncated_dist (B := B) (K₁ := 1) (K₂ := 1)
      (abs_toReal_entropicTransportCost_sub_left_le_of_compact hbc hbB hgL₁)
      (fun ν ν' μ _ _ _ ↦ by
        have hb := abs_toReal_entropicTransportCost_sub_left_le_of_compact
          (ε := ε) (B := B) (K₁ := 1) (b := b ∘ Prod.swap) (hbc.comp continuous_swap)
          (fun w ↦ hbB w.swap) hgL₂ ν ν' μ
        have hswap : (fun w : L × K ↦ ((b ∘ Prod.swap) w : ℝ≥0∞)) =
            (fun w : K × L ↦ (b w : ℝ≥0∞)) ∘ Prod.swap := rfl
        rwa [hswap, entropicTransportCost_comp_swap _ ε ν',
          entropicTransportCost_comp_swap _ ε ν] at hb)
  -- Pull continuity back along the pushforward map `(q.1, q.2) ↦ (q.1.map Φ, q.2.map Ψ)`.
  have hcost_eq : c = fun z ↦ (b (Prod.map Φ Ψ z) : ℝ≥0∞) := funext fun z ↦ by
    rw [← ENNReal.ofReal_toReal (hfin z), ← ENNReal.ofReal_coe_nnreal]
    exact congrArg ENNReal.ofReal (hfg z.1 z.2).symm
  have hpush (q : ProbabilityMeasure X × ProbabilityMeasure Y) :
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure =
        entropicTransportCost (fun w ↦ (b w : ℝ≥0∞)) ε
          (q.1.map Φ).toMeasure (q.2.map Ψ).toMeasure := by
    rw [hcost_eq, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
    exact entropicTransportCost_comp_prodMap_of_continuous hΦc.measurable hΨc.measurable hbc ε
  exact (hcontKL.comp ((ProbabilityMeasure.continuous_map hΦc).prodMap
    (ProbabilityMeasure.continuous_map hΨc))).congr fun q ↦
      congrArg ENNReal.toReal (hpush q).symm

/-- **Joint weak continuity of entropic optimal transport in `ℝ≥0∞` on compact spaces** at every
temperature `ε : ℝ≥0`. -/
theorem continuous_entropicTransportCost
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} (hc : Continuous c)
    (hfin : ∀ z, c z ≠ ∞) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure := by
  obtain ⟨B, hB⟩ := hc.exists_forall_le_coe_of_ne_top hfin
  have heq : (fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure) =
      fun q ↦ ENNReal.ofReal (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal :=
    funext fun _ ↦ (ENNReal.ofReal_toReal
      (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hB) ε)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp (continuous_toReal_entropicTransportCost hc hfin)

end WeakContinuity

end TauCeti
