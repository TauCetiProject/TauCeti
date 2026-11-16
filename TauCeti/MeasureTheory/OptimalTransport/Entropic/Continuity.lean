/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Potentials
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.BoundedLipschitz
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein

/-!
# Quantitative stability and weak continuity of entropic optimal transport

On Polish spaces, the entropically regularised transport cost
`TauCeti.entropicTransportCost c ε μ ν` of a lower semicontinuous cost is jointly weakly lower
semicontinuous in its marginals (`TauCeti.lowerSemicontinuous_entropicTransportCost`). Weak
convergence of the marginals does not give the matching upper bound by primal compactness alone,
because the reference measure `μ ⊗ ν` of the relative entropy moves with the marginals.

At positive temperature `ε ≠ 0` and for a bounded cost `c ≤ B`, canonical Schrödinger potentials
(`TauCeti.MeasureTheory.OptimalTransport.Entropic.Potentials`) supply both quantitative Lipschitz
stability and joint weak continuity, following Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré,
Proposition 2:

1. **Temperature-independent `W₁` stability
   (`TauCeti.ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one`).**
   Evaluating weak duality for `(μ, ν')` at the canonical potentials `(φ', ψ')` of `(μ', ν')`
   (`TauCeti.exists_lipschitzWith_left_entropicDualValue_eq_toReal_entropicTransportCost`), the
   exponential penalty vanishes identically because `φ'` solves the `ν'`-marginal equation at every
   point of `X`, even off the support of `μ'`. Thus
   `OT_ε(μ', ν') - OT_ε(μ, ν') ≤ ∫ φ' d(μ' - μ) ≤ K₁ W₁(μ', μ)`, with no factor depending on `ε`
   or `B`. Combining with the symmetric target estimate yields
   `|OT_ε(μ', ν') - OT_ε(μ, ν)| ≤ K₁ W₁(μ', μ) + K₂ W₁(ν', ν)`.
2. **Joint weak continuity (`TauCeti.continuous_entropicTransportCost`).**
   Because `0 ≤ φ' ≤ B`, centering `φ'` by `B / 2` also bounds the difference by truncated optimal
   transport, which metrises weak convergence on separable pseudometric spaces without moment
   assumptions (`TauCeti.tendsto_probabilityMeasure_iff_transportCost_truncated_dist`). On compact
   pseudometrizable spaces, every continuous finite cost is uniformly approximated via infimal
   convolution by bounded slicewise-Lipschitz costs, and uniform cost stability
   (`TauCeti.abs_toReal_entropicTransportCost_sub_le`) transfers joint weak continuity to the limit.

## Main statements

* `TauCeti.entropicTransportCost_le_add_of_forall_le` and
  `TauCeti.abs_toReal_entropicTransportCost_sub_le`: uniform cost-perturbation stability of
  entropic optimal transport, at every temperature.
* `TauCeti.ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one` and
  `TauCeti.abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one`: `W₁`-Lipschitz stability
  of entropic optimal transport on extended pseudometric spaces.
* `TauCeti.continuous_toReal_entropicTransportCost_of_lipschitzWith` and
  `TauCeti.continuous_entropicTransportCost_of_lipschitzWith`: joint weak continuity on separable
  pseudometric spaces for bounded slicewise-Lipschitz costs.
* `TauCeti.continuous_toReal_entropicTransportCost` and
  `TauCeti.continuous_entropicTransportCost`: joint weak continuity on compact pseudometrizable
  spaces for arbitrary continuous finite costs.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Proposition 2.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  §2.
-/

public section

noncomputable section

open Filter InformationTheory MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section CostPerturbation

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

/-- Increasing a transport cost by at most `a` pointwise increases the regularised transport cost
from a probability source `μ` to any target `ν` by at most `a`, at every temperature and with no
measurability hypothesis on the costs. -/
theorem entropicTransportCost_le_add_of_forall_le [IsProbabilityMeasure μ]
    {c₁ c₂ : X × Y → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ z, c₁ z ≤ c₂ z + a) (ε : ℝ≥0) :
    entropicTransportCost c₁ ε μ ν ≤ entropicTransportCost c₂ ε μ ν + a := by
  simp only [entropicTransportCost_def, ENNReal.iInf_add]
  refine iInf₂_mono fun π hπ ↦ ?_
  have := hπ.isProbabilityMeasure
  calc ∫⁻ z, c₁ z ∂π + ε * klDiv π (μ.prod ν)
      ≤ ∫⁻ z, (c₂ z + a) ∂π + ε * klDiv π (μ.prod ν) := by
        gcongr
        exact h _
    _ = ∫⁻ z, c₂ z ∂π + ε * klDiv π (μ.prod ν) + a := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        ring

/-- **Uniform cost-perturbation stability of entropic optimal transport.** If two finite-valued
costs differ pointwise by at most `δ`, then the regularised transport costs of any two probability
measures differ by at most `δ`, at every temperature. Finiteness of one regularised cost implies
finiteness of the other. -/
theorem abs_toReal_entropicTransportCost_sub_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c₁ c₂ : X × Y → ℝ≥0∞} {δ : ℝ} {ε : ℝ≥0} (hc₁ : ∀ z, c₁ z ≠ ∞) (hc₂ : ∀ z, c₂ z ≠ ∞)
    (hfin : entropicTransportCost c₂ ε μ ν ≠ ∞) (hδ : ∀ z, |(c₁ z).toReal - (c₂ z).toReal| ≤ δ) :
    |(entropicTransportCost c₁ ε μ ν).toReal - (entropicTransportCost c₂ ε μ ν).toReal| ≤ δ := by
  obtain ⟨x₀⟩ := μ.nonempty_of_neZero
  obtain ⟨y₀⟩ := ν.nonempty_of_neZero
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ (x₀, y₀))
  have h₁₂ : ∀ z, c₁ z ≤ c₂ z + ENNReal.ofReal δ := fun z ↦ by
    rw [← ENNReal.ofReal_toReal (hc₁ z), ← ENNReal.ofReal_toReal (hc₂ z),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ0]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hδ z)).2])
  have h₂₁ : ∀ z, c₂ z ≤ c₁ z + ENNReal.ofReal δ := fun z ↦ by
    rw [← ENNReal.ofReal_toReal (hc₁ z), ← ENNReal.ofReal_toReal (hc₂ z),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hδ0]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hδ z)).1])
  have hle₁ := entropicTransportCost_le_add_of_forall_le (μ := μ) (ν := ν) h₁₂ ε
  have hle₂ := entropicTransportCost_le_add_of_forall_le (μ := μ) (ν := ν) h₂₁ ε
  have hfin₁ : entropicTransportCost c₁ ε μ ν ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hle₁
  have hr₁ : (entropicTransportCost c₁ ε μ ν).toReal ≤
      (entropicTransportCost c₂ ε μ ν).toReal + δ := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hle₁
    rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hδ0] at this
  have hr₂ : (entropicTransportCost c₂ ε μ ν).toReal ≤
      (entropicTransportCost c₁ ε μ ν).toReal + δ := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin₁, ENNReal.ofReal_ne_top⟩) hle₂
    rwa [ENNReal.toReal_add hfin₁ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hδ0] at this
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

end CostPerturbation

section MarginalStability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0} {μ μ' : Measure X} {ν ν' : Measure Y}

omit [MeasurableSpace X] in
private theorem lipschitzWith_one_sub_div [PseudoEMetricSpace X] {φ : X → ℝ} {K : ℝ≥0}
    (hK : K ≠ 0) (hL : LipschitzWith K φ) (a : ℝ) :
    LipschitzWith 1 (fun x ↦ (φ x - a) / K) := fun x x' ↦ by
  have hK0 : (0 : ℝ) < K := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK)
  have hsub : (φ x - a) / K - (φ x' - a) / K = (φ x - φ x') / K := by ring
  rw [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq, hsub, abs_div, abs_of_pos hK0,
    ENNReal.ofReal_div_of_pos hK0, ENNReal.ofReal_coe_nnreal, ← Real.dist_eq, ← edist_dist]
  exact ENNReal.div_le_of_le_mul' (hL x x')

/-- Varying only the source marginal from `μ'` to `μ` increases the regularised cost by at most
the difference of expectations of the `K₁`-Lipschitz canonical source potential of `(μ', ν)`. -/
private theorem exists_lipschitzWith_source_potential_diff_bound [PseudoEMetricSpace X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ∃ φ' : X → ℝ, Measurable φ' ∧ LipschitzWith K₁ φ' ∧ (∀ x, 0 ≤ φ' x ∧ φ' x ≤ B) ∧
      (∀ ρ : Measure X, [IsFiniteMeasure ρ] → Integrable φ' ρ) ∧
      (entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal ≤
        ∫ x, φ' x ∂μ' - ∫ x, φ' x ∂μ := by
  obtain ⟨φ', ψ', hφ', hψ', hφ'L, hφ'B, hψ'B, hrow, -, hkant, -⟩ :=
    exists_lipschitzWith_left_entropicDualValue_eq_toReal_entropicTransportCost
      (μ := μ') (ν := ν) hc hcB hL₁ hε
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
  rcases eq_or_ne K₁ 0 with rfl | hK₁
  · obtain ⟨x₀⟩ := μ.nonempty_of_neZero
    have hc₀ {φ : X → ℝ} (hL : LipschitzWith 0 φ) : φ = fun _ ↦ φ x₀ := funext fun x ↦ by
      simpa using hL x x₀
    rw [hc₀ hφ₁L] at hle₁; rw [hc₀ hφ₂L] at hle₂
    simp only [integral_const, probReal_univ, one_smul, sub_self] at hle₁ hle₂
    simp [ENNReal.ofReal_of_nonpos (abs_sub_le_iff.2 ⟨hle₁, hle₂⟩)]
  have hK₁pos : (0 : ℝ) < K₁ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK₁)
  have hlip_div {φ : X → ℝ} (hL : LipschitzWith K₁ φ) : LipschitzWith 1 (fun x ↦ φ x / K₁) := by
    simpa only [sub_zero] using lipschitzWith_one_sub_div hK₁ hL 0
  rcases le_total (entropicTransportCost c ε μ ν).toReal
      (entropicTransportCost c ε μ' ν).toReal with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    refine (ENNReal.ofReal_le_ofReal hle₁).trans ?_
    have hdiv : ∫ x, φ₁ x ∂μ' - ∫ x, φ₁ x ∂μ =
        K₁ * (∫ x, φ₁ x / K₁ ∂μ' - ∫ x, φ₁ x / K₁ ∂μ) := by
      rw [integral_div, integral_div]; field_simp
    rw [hdiv, ENNReal.ofReal_mul hK₁pos.le, ENNReal.ofReal_coe_nnreal]
    gcongr
    exact ofReal_integral_sub_integral_le_wassersteinEDist_one (hlip_div hφ₁L)
      ((hφ₁i μ').div_const _) ((hφ₁i μ).div_const _)
  · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    refine (ENNReal.ofReal_le_ofReal hle₂).trans ?_
    have hdiv : ∫ x, φ₂ x ∂μ - ∫ x, φ₂ x ∂μ' =
        K₁ * (∫ x, -(φ₂ x / K₁) ∂μ' - ∫ x, -(φ₂ x / K₁) ∂μ) := by
      rw [integral_neg, integral_neg, integral_div, integral_div]; field_simp; ring
    rw [hdiv, ENNReal.ofReal_mul hK₁pos.le, ENNReal.ofReal_coe_nnreal]
    gcongr
    exact ofReal_integral_sub_integral_le_wassersteinEDist_one (hlip_div hφ₂L).neg
      ((hφ₂i μ').div_const _).neg ((hφ₂i μ).div_const _).neg

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
  · rw [← entropicTransportCost_comp_swap (c := c) (μ := μ) (ν := ν'),
      ← entropicTransportCost_comp_swap (c := c) (μ := μ) (ν := ν)]
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
      K₁ * (wassersteinEDist 1 μ' μ).toReal + K₂ * (wassersteinEDist 1 ν' ν).toReal := by
  have h₁ : (K₁ : ℝ≥0∞) * wassersteinEDist 1 μ' μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hw₁
  have h₂ : (K₂ : ℝ≥0∞) * wassersteinEDist 1 ν' ν ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hw₂
  have h := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.2 ⟨h₁, h₂⟩)).1
    (ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one hc hcB hL₁ hL₂ hε)
  rwa [ENNReal.toReal_add h₁ h₂, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.coe_toReal] at h

/-- For any `K₁`-Lipschitz function `φ : X → ℝ` with `0 ≤ φ ≤ B`, `|∫ φ dμ' - ∫ φ dμ|` is bounded
by `(K₁ + 1)` times the truncated optimal transport cost between `μ'` and `μ`. -/
private theorem abs_integral_sub_integral_le_transportCost_truncated_dist
    [PseudoMetricSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {φ : X → ℝ} (hL : LipschitzWith K₁ φ)
    (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ B) (hφi : ∀ ρ : Measure X, [IsFiniteMeasure ρ] → Integrable φ ρ) :
    |∫ x, φ x ∂μ' - ∫ x, φ x ∂μ| ≤
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal := by
  set K : ℝ≥0 := K₁ + 1
  have hK0 : K ≠ 0 := by simp [K]
  have hKpos : (0 : ℝ) < K := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK0)
  set R : ℝ := ((B : ℝ) + 1) / (2 * K)
  have h2R : 2 * R = ((B : ℝ) + 1) / (K₁ + 1 : ℝ) := by
    simp only [R, K, NNReal.coe_add, NNReal.coe_one]
    field_simp
  have htfin : transportCost (fun z : X × X ↦ ENNReal.ofReal (min (dist z.1 z.2) (2 * R)))
      μ' μ ≠ ∞ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * R)) ENNReal.ofReal_ne_top <|
      (lintegral_mono fun z : X × X ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_eq
        (by simp)) (transportCost_le_lintegral (isCoupling_prod μ' μ) _)
  have hgL : LipschitzWith 1 (fun x ↦ (φ x - (B : ℝ) / 2) / K) :=
    lipschitzWith_one_sub_div hK0 (hL.weaken (by simp [K])) _
  have hgB : ∀ x, ‖(φ x - (B : ℝ) / 2) / K‖ ≤ R := fun x ↦ by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hKpos]
    have hφB : |φ x - (B : ℝ) / 2| ≤ ((B : ℝ) + 1) / 2 :=
      abs_le.2 ⟨by linarith [(hb x).1], by linarith [(hb x).2]⟩
    simpa only [R, div_div, mul_comm (2 : ℝ)] using div_le_div_of_nonneg_right hφB hKpos.le
  have hshift : ∫ x, φ x ∂μ' - ∫ x, φ x ∂μ =
      (K : ℝ) * (∫ x, (φ x - (B : ℝ) / 2) / K ∂μ' - ∫ x, (φ x - (B : ℝ) / 2) / K ∂μ) := by
    rw [integral_div, integral_div, integral_sub (hφi μ') (integrable_const _),
      integral_sub (hφi μ) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    field_simp
    ring
  have htr₁ := (ENNReal.ofReal_le_iff_le_toReal htfin).1
    (ofReal_integral_sub_integral_le_transportCost_truncated_dist hgL hgB)
  have htr₂ := (ENNReal.ofReal_le_iff_le_toReal htfin).1
    (ofReal_integral_sub_integral_le_transportCost_truncated_dist hgL.neg
      (fun x ↦ by simpa using hgB x))
  simp only [Pi.neg_apply, integral_neg] at htr₂
  rw [← h2R]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩ <;> simp only [← NNReal.coe_one, ← NNReal.coe_add]
  · linarith [hshift, mul_le_mul_of_nonneg_left htr₁ hKpos.le]
  · linarith [hshift, mul_le_mul_of_nonneg_left htr₂ hKpos.le]

/-- Source-marginal stability of entropic optimal transport in terms of truncated optimal
transport, with no moment assumption. -/
private theorem abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
    [PseudoMetricSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    |(entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal| ≤
      (K₁ + 1 : ℝ) * (transportCost (fun z : X × X ↦
        ENNReal.ofReal (min (dist z.1 z.2) (((B : ℝ) + 1) / (K₁ + 1)))) μ' μ).toReal := by
  obtain ⟨φ₁, _, hφ₁L, hφ₁B, hφ₁i, hle₁⟩ :=
    exists_lipschitzWith_source_potential_diff_bound (μ := μ) (μ' := μ') (ν := ν) hc hcB hL₁ hε
  obtain ⟨φ₂, _, hφ₂L, hφ₂B, hφ₂i, hle₂⟩ :=
    exists_lipschitzWith_source_potential_diff_bound (μ := μ') (μ' := μ) (ν := ν) hc hcB hL₁ hε
  have hb₁ := (hle₁.trans (le_abs_self _)).trans
    (abs_integral_sub_integral_le_transportCost_truncated_dist (μ := μ) (μ' := μ') hφ₁L hφ₁B hφ₁i)
  have hb₂ := (hle₂.trans (le_abs_self _)).trans <| (abs_sub_comm _ _).trans_le
    (abs_integral_sub_integral_le_transportCost_truncated_dist (μ := μ) (μ' := μ') hφ₂L hφ₂B hφ₂i)
  exact abs_sub_le_iff.2 ⟨hb₁, hb₂⟩

end MarginalStability

section WeakContinuity

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
      (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  set R₁ : ℝ := ((B : ℝ) + 1) / (2 * (K₁ + 1 : ℝ))
  set R₂ : ℝ := ((B : ℝ) + 1) / (2 * (K₂ + 1 : ℝ))
  have hR₁ : 0 < R₁ := by positivity
  have hR₂ : 0 < R₂ := by positivity
  have h2R₁ : 2 * R₁ = ((B : ℝ) + 1) / (K₁ + 1 : ℝ) := by dsimp [R₁]; field_simp
  have h2R₂ : 2 * R₂ = ((B : ℝ) + 1) / (K₂ + 1 : ℝ) := by dsimp [R₂]; field_simp
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
  refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
  filter_upwards [hub.eventually (gt_mem_nhds hδ)] with q hq
  rw [Real.dist_eq]
  have hb₁ := abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
    (μ := q₀.1.toMeasure) (μ' := q.1.toMeasure) (ν := q.2.toMeasure) hc hcB hL₁ hε
  have hb₂ := abs_toReal_entropicTransportCost_sub_left_le_transportCost_truncated_dist
    (c := c ∘ Prod.swap) (μ := q₀.2.toMeasure) (μ' := q.2.toMeasure) (ν := q₀.1.toMeasure)
    (hc.comp measurable_swap) (fun w ↦ hcB w.swap) hL₂ hε
  rw [entropicTransportCost_comp_swap, entropicTransportCost_comp_swap] at hb₂
  rw [← h2R₁] at hb₁
  rw [← h2R₂] at hb₂
  exact ((abs_sub_le _ (entropicTransportCost c ε q₀.1.toMeasure q.2.toMeasure).toReal _).trans
    (add_le_add hb₁ hb₂)).trans_lt hq

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
    funext fun q ↦ (ENNReal.ofReal_toReal
      (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp
    (continuous_toReal_entropicTransportCost_of_lipschitzWith hc hcB hL₁ hL₂ hε)

/-- Uniform approximation of a continuous nonnegative function on a compact product of pseudometric
spaces by bounded slicewise-Lipschitz functions via infimal convolution. -/
private theorem exists_lipschitzWith_approx_of_continuous
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y] [CompactSpace Y]
    [Nonempty (X × Y)] {f : X × Y → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    {B : ℝ≥0} (hfB : ∀ z, f z ≤ B) {η : ℝ} (hη : 0 < η) :
    ∃ (g : X × Y → ℝ) (K : ℝ≥0), Continuous g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ B) ∧
      (∀ y, LipschitzWith K fun x ↦ g (x, y)) ∧ (∀ x, LipschitzWith K fun y ↦ g (x, y)) ∧
      ∀ z, |f z - g z| ≤ η := by
  obtain ⟨r, hr, huc⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hf) η hη
  set K : ℝ≥0 := Real.toNNReal ((B : ℝ) / r)
  set g : X × Y → ℝ := fun z ↦ ⨅ w : X × Y, (f w + K * (dist z.1 w.1 + dist z.2 w.2))
  have hbdd (z : X × Y) : BddBelow (range fun w : X × Y ↦
      f w + K * (dist z.1 w.1 + dist z.2 w.2)) :=
    ⟨0, forall_mem_range.2 fun w ↦ by positivity [hf0 w]⟩
  have hgf : ∀ z, g z ≤ f z := fun z ↦ (ciInf_le (hbdd z) z).trans_eq (by simp)
  have hgL₁ : ∀ y, LipschitzWith K fun x ↦ g (x, y) := fun y ↦
    LipschitzWith.of_le_add_mul K fun x x' ↦ sub_le_iff_le_add.1 <| le_ciInf fun w ↦ by
      have h := ciInf_le (hbdd (x, y)) w
      have hm := mul_le_mul_of_nonneg_left
        (add_le_add_right (dist_triangle x x' w.1) (dist y w.2)) K.coe_nonneg
      dsimp only at h ⊢; linarith
  have hgL₂ : ∀ x, LipschitzWith K fun y ↦ g (x, y) := fun x ↦
    LipschitzWith.of_le_add_mul K fun y y' ↦ sub_le_iff_le_add.1 <| le_ciInf fun w ↦ by
      have h := ciInf_le (hbdd (x, y)) w
      have hm := mul_le_mul_of_nonneg_left
        (add_le_add_left (dist_triangle y y' w.2) (dist x w.1)) K.coe_nonneg
      dsimp only at h ⊢; linarith
  have hgc : Continuous g := LipschitzWith.continuous (K := K + K) <|
    LipschitzWith.of_le_add_mul (K + K) fun z z' ↦ by
      simp only [NNReal.coe_add]
      nlinarith [(hgL₁ z.2).le_add_mul z.1 z'.1, (hgL₂ z'.1).le_add_mul z.2 z'.2,
        show dist z.1 z'.1 ≤ dist z z' from le_max_left _ _,
        show dist z.2 z'.2 ≤ dist z z' from le_max_right _ _, K.coe_nonneg]
  refine ⟨g, K, hgc, fun z ↦ ⟨le_ciInf fun w ↦ by positivity [hf0 w], (hgf z).trans (hfB z)⟩,
    hgL₁, hgL₂, fun z ↦ ?_⟩
  rw [abs_of_nonneg (sub_nonneg.2 (hgf z)), sub_le_iff_le_add', ← sub_le_iff_le_add]
  refine le_ciInf fun w ↦ ?_
  rcases lt_or_ge (dist z w) r with hlt | hge
  · have hfw := (abs_lt.1 (Real.dist_eq (f z) (f w) ▸ huc hlt)).2
    have : 0 ≤ (K : ℝ) * (dist z.1 w.1 + dist z.2 w.2) := by positivity
    linarith
  · have hdsum : r ≤ dist z.1 w.1 + dist z.2 w.2 :=
      (Prod.dist_eq (x := z) (y := w) ▸ hge).trans (max_le (le_add_of_nonneg_right dist_nonneg)
        (le_add_of_nonneg_left dist_nonneg))
    have hBK : (B : ℝ) ≤ K * (dist z.1 w.1 + dist z.2 w.2) :=
      ((div_le_iff₀ hr).1 (Real.le_coe_toNNReal _)).trans
        (mul_le_mul_of_nonneg_left hdsum K.coe_nonneg)
    linarith [hfB z, hf0 w]

private theorem exists_forall_le_of_continuous {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {c : α → ℝ≥0∞} (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) :
    ∃ B : ℝ≥0, ∀ z, (c z).toReal ≤ B ∧ c z ≤ B := by
  have hfc : Continuous fun z ↦ (c z).toReal := ENNReal.continuousOn_toReal.comp_continuous hc hfin
  obtain ⟨B₀, hB₀⟩ := (isCompact_range hfc).bddAbove
  refine ⟨Real.toNNReal B₀, fun z ↦ ?_⟩
  have hz : (c z).toReal ≤ Real.toNNReal B₀ :=
    (hB₀ (mem_range_self z)).trans (Real.le_coe_toNNReal B₀)
  refine ⟨hz, ?_⟩
  rw [← ENNReal.ofReal_toReal (hfin z), ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hz

/-- **Joint weak continuity of entropic optimal transport on compact pseudometrizable spaces.**
For compact pseudometrizable spaces `X` and `Y` whose open sets are measurable (in particular
compact metrizable spaces with their Borel σ-algebras), a continuous finite-valued cost `c` and a
positive temperature `ε`, the real-valued regularised transport cost is jointly continuous on
`ProbabilityMeasure X × ProbabilityMeasure Y`. -/
theorem continuous_toReal_entropicTransportCost
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace.PseudoMetrizableSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  let : PseudoMetricSpace Y := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Y
  rcases isEmpty_or_nonempty (X × Y) with hemp | _
  · have : IsEmpty (ProbabilityMeasure X × ProbabilityMeasure Y) :=
      ⟨fun q ↦ hemp.false (q.1.toMeasure.nonempty_of_neZero.some,
        q.2.toMeasure.nonempty_of_neZero.some)⟩
    exact continuous_of_discreteTopology
  set f : X × Y → ℝ := fun z ↦ (c z).toReal
  have hfc : Continuous f := ENNReal.continuousOn_toReal.comp_continuous hc hfin
  obtain ⟨B, hB⟩ := exists_forall_le_of_continuous hc hfin
  refine continuous_iff_continuousAt.2 fun q₀ ↦ Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
  have hη : 0 < δ / 3 := by positivity
  obtain ⟨g, K, hgc, hgB, hgL₁, hgL₂, hfg⟩ :=
    exists_lipschitzWith_approx_of_continuous hfc (fun _ ↦ ENNReal.toReal_nonneg)
      (fun z ↦ (hB z).1) hη
  set cg : X × Y → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (g z)
  have hcg_meas : Measurable cg := hgc.measurable.ennreal_ofReal
  have hcgB : ∀ z, cg z ≤ B := fun z ↦ by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hgB z).2
  have hcg_toReal : ∀ z, (cg z).toReal = g z := fun z ↦ ENNReal.toReal_ofReal (hgB z).1
  have hcgL₁ : ∀ y, LipschitzWith K fun x ↦ (cg (x, y)).toReal := by
    simp_rw [hcg_toReal]; exact hgL₁
  have hcgL₂ : ∀ x, LipschitzWith K fun y ↦ (cg (x, y)).toReal := by
    simp_rw [hcg_toReal]; exact hgL₂
  have hcont_g := continuous_toReal_entropicTransportCost_of_lipschitzWith
    (ε := ε) hcg_meas hcgB hcgL₁ hcgL₂ hε
  have hclose : ∀ q : ProbabilityMeasure X × ProbabilityMeasure Y,
      |(entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal -
        (entropicTransportCost cg ε q.1.toMeasure q.2.toMeasure).toReal| ≤ δ / 3 := fun q ↦
    abs_toReal_entropicTransportCost_sub_le hfin (fun _ ↦ ENNReal.ofReal_ne_top)
      (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcgB) ε)
      (fun z ↦ by rw [hcg_toReal]; exact hfg z)
  filter_upwards [(hcont_g.tendsto q₀).eventually (Metric.ball_mem_nhds _ hη)] with q hq
  rw [Real.dist_eq] at hq ⊢
  have h₁ := hclose q
  have h₂ := hclose q₀
  have htri : |(entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal -
      (entropicTransportCost c ε q₀.1.toMeasure q₀.2.toMeasure).toReal| ≤
      |(entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal -
        (entropicTransportCost cg ε q.1.toMeasure q.2.toMeasure).toReal| +
      |(entropicTransportCost cg ε q.1.toMeasure q.2.toMeasure).toReal -
        (entropicTransportCost cg ε q₀.1.toMeasure q₀.2.toMeasure).toReal| +
      |(entropicTransportCost cg ε q₀.1.toMeasure q₀.2.toMeasure).toReal -
        (entropicTransportCost c ε q₀.1.toMeasure q₀.2.toMeasure).toReal| :=
    (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
  rw [abs_sub_comm] at h₂
  linarith

/-- **Joint weak continuity of entropic optimal transport in `ℝ≥0∞` on compact pseudometrizable
spaces.** -/
theorem continuous_entropicTransportCost
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace.PseudoMetrizableSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure := by
  obtain ⟨B, hB⟩ := exists_forall_le_of_continuous hc hfin
  have heq : (fun q : ProbabilityMeasure X × ProbabilityMeasure Y ↦
      entropicTransportCost c ε q.1.toMeasure q.2.toMeasure) =
      fun q ↦ ENNReal.ofReal (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal :=
    funext fun q ↦ (ENNReal.ofReal_toReal
      (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ fun z ↦ (hB z).2) ε)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp (continuous_toReal_entropicTransportCost hc hfin hε)

end WeakContinuity

end TauCeti
