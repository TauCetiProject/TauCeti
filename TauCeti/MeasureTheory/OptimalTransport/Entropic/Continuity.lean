/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Duality
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.BoundedLipschitz
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein

/-!
# Quantitative stability and weak continuity of entropic optimal transport

On Polish spaces, the entropically regularised transport cost
`TauCeti.entropicTransportCost c ε μ ν` of a lower semicontinuous cost is jointly weakly lower
semicontinuous in its marginals (`TauCeti.lowerSemicontinuous_entropicTransportCost`). Weak
convergence of the marginals does not give the matching upper bound by primal compactness alone,
because the reference measure `μ ⊗ ν` of the relative entropy moves with the marginals.

At positive temperature `ε ≠ 0` and for a bounded cost `c ≤ B`, entropic duality supplies both
quantitative Lipschitz stability and joint weak continuity, following Feydy–Séjourné–Vialard–
Amari–Trouvé–Peyré, Propositions 1 and 2:

1. **Canonical Schrödinger potentials
   (`TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le`).**
   Applying Sinkhorn half-steps to an optimal dual pair produces measurable potentials `φ` on `X`
   and `ψ` on `Y` that satisfy both marginal equations
   `∫ y, exp ((φ x + ψ y - c(x, y)) / ε) dν(y) = 1` and
   `∫ x, exp ((φ x + ψ y - c(x, y)) / ε) dμ(x) = 1` *pointwise everywhere* on `X` and `Y`, together
   with the uniform bounds `0 ≤ φ ≤ B` and `|ψ| ≤ B`. When the cost slices are `K₁`- and
   `K₂`-Lipschitz, the softmin formulas pass those exact Lipschitz constants to `φ` and `ψ`,
   uniformly in the temperature
   (`TauCeti.exists_lipschitzWith_entropicDualValue_eq_toReal_entropicTransportCost`).
2. **Temperature-independent `W₁` stability
   (`TauCeti.ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one`).**
   Evaluating weak duality for `(μ, ν')` at the canonical potentials `(φ', ψ')` of `(μ', ν')`,
   the exponential penalty vanishes identically because `φ'` solves the `ν'`-marginal equation at
   every point of `X`, even off the support of `μ'`. Thus
   `OT_ε(μ', ν') - OT_ε(μ, ν') ≤ ∫ φ' d(μ' - μ) ≤ K₁ W₁(μ', μ)`, with no factor depending on `ε`
   or `B`. Combining with the symmetric target estimate yields
   `|OT_ε(μ', ν') - OT_ε(μ, ν)| ≤ K₁ W₁(μ', μ) + K₂ W₁(ν', ν)`.
3. **Joint weak continuity (`TauCeti.continuous_entropicTransportCost`).**
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
* `TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le`: existence of canonical
  Schrödinger potentials bounded by `B` and normalised pointwise everywhere on `X` and `Y`.
* `TauCeti.exists_lipschitzWith_entropicDualValue_eq_toReal_entropicTransportCost`: canonical
  Schrödinger potentials inherit the slice Lipschitz constants of the cost.
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
  AISTATS 2019, Propositions 1 and 2.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  §2, for uniform bounds and equicontinuity of Schrödinger potentials.
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

section Softmin

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure Y} {f : X × Y → ℝ} {ε : ℝ≥0} {u u' : Y → ℝ}

/-- The entropic softmin transform `-ε * log ∫ exp ((u y - f(x, y)) / ε) dν(y)` of a potential `u`
against a measure `ν`. -/
private def entropicSoftmin (f : X × Y → ℝ) (ε : ℝ≥0) (ν : Measure Y) (u : Y → ℝ) (x : X) : ℝ :=
  -(ε : ℝ) * Real.log (∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν)

private theorem integrable_exp_sub_div [IsFiniteMeasure ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu) (x : X) :
    Integrable (fun y ↦ Real.exp ((u y - f (x, y)) / ε)) ν := by
  refine Integrable.of_bound (by fun_prop) (Real.exp ((Cu + Bf) / ε)) (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  refine div_le_div_of_nonneg_right ?_ ε.coe_nonneg
  linarith [(abs_le.1 (huC y)).2, (abs_le.1 (hfB (x, y))).1]

private theorem measurable_entropicSoftmin [SFinite ν] (hf : Measurable f) (hu : Measurable u) :
    Measurable (entropicSoftmin f ε ν u) := by
  have h : StronglyMeasurable fun z : X × Y ↦ Real.exp ((u z.2 - f z) / ε) :=
    (by fun_prop : Measurable fun z : X × Y ↦ Real.exp ((u z.2 - f z) / ε)).stronglyMeasurable
  exact h.integral_prod_right'.measurable.log.const_mul _

omit [MeasurableSpace X] in
private theorem entropicSoftmin_congr_ae (hu : u =ᵐ[ν] u') :
    entropicSoftmin f ε ν u = entropicSoftmin f ε ν u' := by
  funext x
  unfold entropicSoftmin
  congr 2
  exact integral_congr_ae (hu.mono fun y hy ↦ by dsimp only; rw [hy])

private theorem entropicSoftmin_add_const [IsFiniteMeasure ν] [NeZero ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu)
    (hε : ε ≠ 0) (a : ℝ) (x : X) :
    entropicSoftmin f ε ν (fun y ↦ u y + a) x = entropicSoftmin f ε ν u x - a := by
  have : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x
  have hZ : 0 < ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ Real.exp ((u y + a - f (x, y)) / ε)) =
      fun y ↦ Real.exp (a / ε) * Real.exp ((u y - f (x, y)) / ε) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [entropicSoftmin, entropicSoftmin, hsplit, integral_const_mul,
    Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  field_simp
  ring

private theorem abs_entropicSoftmin_le [IsProbabilityMeasure ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu)
    (hε : ε ≠ 0) (x : X) :
    |entropicSoftmin f ε ν u x| ≤ Cu + Bf := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x
  have hlo : Real.exp (-(Cu + Bf) / ε) ≤ ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν := by
    simpa using integral_mono (integrable_const _) hint fun y ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right
        (by linarith [(abs_le.1 (huC y)).1, (abs_le.1 (hfB (x, y))).2]) ε.coe_nonneg
  have hhi : ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν ≤ Real.exp ((Cu + Bf) / ε) := by
    simpa using integral_mono hint (integrable_const _) fun y ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right
        (by linarith [(abs_le.1 (huC y)).2, (abs_le.1 (hfB (x, y))).1]) ε.coe_nonneg
  have h₁ := Real.log_le_log (Real.exp_pos _) hlo
  have h₂ := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hhi
  rw [Real.log_exp, div_le_iff₀ hε0] at h₁
  rw [Real.log_exp, le_div_iff₀ hε0] at h₂
  rw [entropicSoftmin, abs_le]
  constructor <;> linarith

private theorem integral_exp_entropicSoftmin [IsFiniteMeasure ν] [NeZero ν] (hf : Measurable f)
    {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u) (huC : ∀ y, |u y| ≤ Cu)
    (hε : ε ≠ 0) (x : X) :
    ∫ y, Real.exp ((entropicSoftmin f ε ν u x + u y - f (x, y)) / ε) ∂ν = 1 := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x
  have hZ : 0 < ∫ y, Real.exp ((u y - f (x, y)) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ Real.exp ((entropicSoftmin f ε ν u x + u y - f (x, y)) / ε)) =
      fun y ↦ Real.exp (entropicSoftmin f ε ν u x / ε) * Real.exp ((u y - f (x, y)) / ε) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, integral_const_mul, entropicSoftmin, neg_mul, neg_div,
    mul_div_cancel_left₀ _ hε0.ne', Real.exp_neg, Real.exp_log hZ, inv_mul_cancel₀ hZ.ne']

private theorem lipschitzWith_entropicSoftmin [PseudoEMetricSpace X] [IsFiniteMeasure ν] [NeZero ν]
    (hf : Measurable f) {Bf Cu : ℝ} (hfB : ∀ z, |f z| ≤ Bf) (hu : Measurable u)
    (huC : ∀ y, |u y| ≤ Cu) (hε : ε ≠ 0) {K : ℝ≥0}
    (hL : ∀ y, LipschitzWith K fun x ↦ f (x, y)) :
    LipschitzWith K (entropicSoftmin f ε ν u) := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  intro x x'
  rcases eq_or_ne K 0 with rfl | hK
  · have hfx : ∀ y, f (x, y) = f (x', y) := fun y ↦ by
      have := (hL y) x x'
      rwa [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at this
    have heq : entropicSoftmin f ε ν u x = entropicSoftmin f ε ν u x' := by
      simp only [entropicSoftmin, hfx]
    simp [heq]
  rcases eq_or_ne (edist x x') ∞ with htop | hfin
  · rw [htop, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hK)]
    exact le_top
  set d := (edist x x').toReal
  have hKd_ne_top : (K : ℝ≥0∞) * edist x x' ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hKd_toReal : ((K : ℝ≥0∞) * edist x x').toReal = K * d := by
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hf_diff : ∀ y, |f (x, y) - f (x', y)| ≤ K * d := fun y ↦ by
    have hy := (hL y) x x'
    rw [edist_dist, Real.dist_eq] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hKd_ne_top).1 hy |>.trans_eq hKd_toReal
  have hdir (x₁ x₂ : X) (hd : ∀ y, |f (x₁, y) - f (x₂, y)| ≤ K * d) :
      entropicSoftmin f ε ν u x₁ - entropicSoftmin f ε ν u x₂ ≤ K * d := by
    have hi₁ := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x₁
    have hi₂ := integrable_exp_sub_div (ν := ν) (ε := ε) hf hfB hu huC x₂
    have hZ₁ : 0 < ∫ y, Real.exp ((u y - f (x₁, y)) / ε) ∂ν := integral_exp_pos hi₁
    have hZ₂ : 0 < ∫ y, Real.exp ((u y - f (x₂, y)) / ε) ∂ν := integral_exp_pos hi₂
    have hle : ∫ y, Real.exp ((u y - f (x₂, y)) / ε) ∂ν ≤
        Real.exp (K * d / ε) * ∫ y, Real.exp ((u y - f (x₁, y)) / ε) ∂ν := by
      rw [← integral_const_mul]
      refine integral_mono hi₂ (hi₁.const_mul _) fun y ↦ ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      have hy := (abs_le.1 (hd y)).2
      calc (u y - f (x₂, y)) / ε
          = (f (x₁, y) - f (x₂, y)) / ε + (u y - f (x₁, y)) / ε := by ring
        _ ≤ K * d / ε + (u y - f (x₁, y)) / ε := by
            gcongr
    have hlog := Real.log_le_log hZ₂ hle
    rw [Real.log_mul (Real.exp_pos _).ne' hZ₁.ne', Real.log_exp] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hε0.le
    rw [mul_add, mul_div_cancel₀ _ hε0.ne'] at hmul
    unfold entropicSoftmin
    linarith
  have habs : |entropicSoftmin f ε ν u x - entropicSoftmin f ε ν u x'| ≤ K * d :=
    abs_sub_le_iff.2 ⟨hdir x x' hf_diff,
      hdir x' x fun y ↦ by rw [abs_sub_comm]; exact hf_diff y⟩
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_toReal hKd_ne_top, hKd_toReal]
  exact ENNReal.ofReal_le_ofReal habs

end Softmin

private theorem abs_toReal_le_of_le {α : Type*} {c : α → ℝ≥0∞} {B : ℝ≥0} (hcB : ∀ z, c z ≤ B)
    (z : α) : |(c z).toReal| ≤ B := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top (hcB z)).trans_eq (ENNReal.coe_toReal B)

section CanonicalPotentials

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε B : ℝ≥0} {μ : Measure X} {ν : Measure Y}

/-- If a Gibbs density couples two probability measures, the source potential agrees `μ`-almost
everywhere with the entropic softmin of the target potential. -/
private theorem ae_eq_entropicSoftmin_of_isCoupling [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {φ : X → ℝ} {ψ : Y → ℝ} {Cφ Cψ : ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (_ : ∀ x, |φ x| ≤ Cφ) (hψC : ∀ y, |ψ y| ≤ Cψ)
    (hπ : IsCoupling ((μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε))) μ ν) :
    φ =ᵐ[μ] entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hfB := abs_toReal_le_of_le hcB
  set g : X × Y → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε))
  have hg : Measurable g := by fun_prop
  have hrow : (fun x ↦ ∫⁻ y, g (x, y) ∂ν) =ᵐ[μ] fun _ ↦ (1 : ℝ≥0∞) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg.lintegral_prod_right' measurable_const
      fun s hs _ ↦ ?_
    calc ∫⁻ x in s, (∫⁻ y, g (x, y) ∂ν) ∂μ
        = ((μ.prod ν).withDensity g) (s ×ˢ univ) := by
          rw [withDensity_apply _ (hs.prod MeasurableSet.univ),
            setLIntegral_prod _ hg.aemeasurable]
          simp only [Measure.restrict_univ]
      _ = μ s := hπ.measure_prod_univ hs
      _ = ∫⁻ _ in s, 1 ∂μ := by simp
  filter_upwards [hrow] with x hx
  have hint := integrable_exp_sub_div (ν := ν) (ε := ε) hc.ennreal_toReal hfB hψ hψC x
  have hZ : 0 < ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint
  have hsplit : (fun y ↦ Real.exp ((φ x + ψ y - (c (x, y)).toReal) / ε)) =
      fun y ↦ Real.exp (φ x / ε) * Real.exp ((ψ y - (c (x, y)).toReal) / ε) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  have hl : ∫⁻ y, g (x, y) ∂ν =
      ENNReal.ofReal (Real.exp (φ x / ε) * ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hsplit ▸ hint.const_mul _)
      (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), hsplit, integral_const_mul]
  rw [hl] at hx
  have hmul_pos : 0 < Real.exp (φ x / ε) * ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν :=
    mul_pos (Real.exp_pos _) hZ
  have hprod : Real.exp (φ x / ε) * ∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν = 1 := by
    have := congrArg ENNReal.toReal hx
    rwa [ENNReal.toReal_ofReal hmul_pos.le, ENNReal.toReal_one] at this
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp, Real.log_one] at hlog
  have hφdiv : φ x / ε = -Real.log (∫ y, Real.exp ((ψ y - (c (x, y)).toReal) / ε) ∂ν) := by
    linarith
  rw [entropicSoftmin, (div_eq_iff hε0.ne').1 hφdiv]
  ring

/-- Two Sinkhorn half-steps turn an almost-everywhere optimal potential pair `(φ₀, ψ₀)` into a
measurable softmin fixed-point pair `(φ₁, ψ₁)` agreeing with `(φ₀, ψ₀)` modulo `μ` and `ν`. -/
private theorem exists_softmin_fixed_point_of_isCoupling [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {π : Measure (X × Y)} (hπ : IsCoupling π μ ν) {φ₀ : X → ℝ} {ψ₀ : Y → ℝ} {C₀ : ℝ}
    (hφ₀ : Measurable φ₀) (hψ₀ : Measurable ψ₀) (hφ₀C : ∀ x, |φ₀ x| ≤ C₀)
    (hψ₀C : ∀ y, |ψ₀ y| ≤ C₀)
    (hπeq : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ₀ z.1 + ψ₀ z.2 - (c z).toReal) / ε))) :
    ∃ (φ₁ : X → ℝ) (ψ₁ : Y → ℝ) (C₁ : ℝ), Measurable φ₁ ∧ Measurable ψ₁ ∧
      (∀ x, |φ₁ x| ≤ C₁) ∧ (∀ y, |ψ₁ y| ≤ C₁) ∧ φ₀ =ᵐ[μ] φ₁ ∧ ψ₀ =ᵐ[ν] ψ₁ ∧
      φ₁ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁ ∧
      ψ₁ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₁ := by
  have hfB := abs_toReal_le_of_le hcB
  have hswap : ⇑(MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X) = Prod.swap := rfl
  have hπswap_eq : π.map Prod.swap = (ν.prod μ).withDensity fun w ↦
      ENNReal.ofReal (Real.exp ((ψ₀ w.1 + φ₀ w.2 - (c w.swap).toReal) / ε)) := by
    rw [hπeq, ← hswap, MeasurableEquiv.map_withDensity, hswap, Measure.prod_swap]
    refine withDensity_congr_ae (ae_of_all _ fun w ↦ ?_)
    have hw : (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).symm w = w.swap := rfl
    simp only [hw, Prod.fst_swap, Prod.snd_swap]
    congr 2; ring
  have hψ₀₁ : ψ₀ =ᵐ[ν] entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₀ :=
    ae_eq_entropicSoftmin_of_isCoupling (hc.comp measurable_swap) (fun w ↦ hcB w.swap) hε
      hψ₀ hφ₀ hψ₀C hφ₀C (hπswap_eq ▸ hπ.swap)
  set ψ₁ := entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₀
  have hψ₁ : Measurable ψ₁ :=
    measurable_entropicSoftmin (hc.comp measurable_swap).ennreal_toReal hφ₀
  have hψ₁C : ∀ y, |ψ₁ y| ≤ C₀ + B :=
    abs_entropicSoftmin_le (hc.comp measurable_swap).ennreal_toReal (fun w ↦ hfB w.swap)
      hφ₀ hφ₀C hε
  have hπ₁ : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (Real.exp ((φ₀ z.1 + ψ₁ z.2 - (c z).toReal) / ε)) := by
    rw [hπeq]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp hψ₀₁] with z hz
    simp only [Function.comp_apply] at hz; rw [hz]
  have hφ₀₁ : φ₀ =ᵐ[μ] entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁ :=
    ae_eq_entropicSoftmin_of_isCoupling hc hcB hε hφ₀ hψ₁ hφ₀C hψ₁C (hπ₁ ▸ hπ)
  set φ₁ := entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁
  have hφ₁ : Measurable φ₁ := measurable_entropicSoftmin hc.ennreal_toReal hψ₁
  have hφ₁C : ∀ x, |φ₁ x| ≤ C₀ + B + B :=
    abs_entropicSoftmin_le hc.ennreal_toReal hfB hψ₁ hψ₁C hε
  refine ⟨φ₁, ψ₁, C₀ + B + B, hφ₁, hψ₁, hφ₁C,
    fun y ↦ (hψ₁C y).trans (le_add_of_nonneg_right B.coe_nonneg), hφ₀₁, hψ₀₁, rfl,
    entropicSoftmin_congr_ae hφ₀₁⟩

/-- If `0 ≤ f ≤ B` and `0 ≤ φ ≤ B`, then `|entropicSoftmin f ε μ φ y| ≤ B`. -/
private theorem abs_entropicSoftmin_le_of_nonneg_le [IsProbabilityMeasure μ] {f : Y × X → ℝ}
    (hf : Measurable f) (hf₀ : ∀ w, 0 ≤ f w) (hfB : ∀ w, f w ≤ B) {φ : X → ℝ}
    (hφ : Measurable φ) (hφB : ∀ x, 0 ≤ φ x ∧ φ x ≤ B) (hε : ε ≠ 0) (y : Y) :
    |entropicSoftmin f ε μ φ y| ≤ B := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hf_abs : ∀ w, |f w| ≤ B :=
    fun w ↦ abs_le.2 ⟨by linarith [hf₀ w, B.coe_nonneg], hfB w⟩
  have hφ_abs : ∀ x, |φ x| ≤ B :=
    fun x ↦ abs_le.2 ⟨by linarith [(hφB x).1, B.coe_nonneg], (hφB x).2⟩
  have hint_y := integrable_exp_sub_div (ν := μ) (ε := ε) hf hf_abs hφ hφ_abs y
  have hlo : Real.exp (-(B : ℝ) / ε) ≤ ∫ x, Real.exp ((φ x - f (y, x)) / ε) ∂μ := by
    simpa using integral_mono (integrable_const _) hint_y fun x ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right (by linarith [(hφB x).1, hfB (y, x)]) ε.coe_nonneg
  have hhi : ∫ x, Real.exp ((φ x - f (y, x)) / ε) ∂μ ≤ Real.exp ((B : ℝ) / ε) := by
    simpa using integral_mono hint_y (integrable_const _) fun x ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right (by linarith [(hφB x).2, hf₀ (y, x)]) ε.coe_nonneg
  have h₁ := Real.log_le_log (Real.exp_pos _) hlo
  have h₂ := Real.log_le_log (integral_exp_pos hint_y) hhi
  rw [Real.log_exp, div_le_iff₀ hε0] at h₁
  rw [Real.log_exp, le_div_iff₀ hε0] at h₂
  dsimp only [entropicSoftmin]
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Shifting a softmin fixed-point pair `(φ₁, ψ₁)` by `a = -ε * log ∫ exp (ψ₁ / ε) dν` produces
canonical bounds `0 ≤ φ ≤ B` and `|ψ| ≤ B` while preserving the softmin fixed-point equations. -/
private theorem entropicSoftmin_shift_bounds [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) {φ₁ : X → ℝ} {ψ₁ : Y → ℝ} {C₁ : ℝ}
    (hφ₁ : Measurable φ₁) (hψ₁ : Measurable ψ₁) (hφ₁C : ∀ x, |φ₁ x| ≤ C₁)
    (hψ₁C : ∀ y, |ψ₁ y| ≤ C₁) (hφ₁eq : φ₁ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ₁)
    (hψ₁eq : ψ₁ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ₁) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (a : ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, φ x = φ₁ x - a) ∧ (∀ y, ψ y = ψ₁ y + a) ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      φ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ ∧
      ψ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hfB := abs_toReal_le_of_le hcB
  have hint_a : Integrable (fun y ↦ Real.exp (ψ₁ y / ε)) ν := by
    simpa using integrable_exp_sub_div (X := Unit) (f := fun _ ↦ 0) (ν := ν) (ε := ε)
      measurable_const (Bf := 0) (fun _ ↦ by simp) hψ₁ hψ₁C ()
  have hZa : 0 < ∫ y, Real.exp (ψ₁ y / ε) ∂ν := integral_exp_pos hint_a
  set a : ℝ := -(ε : ℝ) * Real.log (∫ y, Real.exp (ψ₁ y / ε) ∂ν)
  set φ : X → ℝ := fun x ↦ φ₁ x - a
  set ψ : Y → ℝ := entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ
  have hψ_shift : ∀ y, ψ y = ψ₁ y + a := fun y ↦ by
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg, ← hψ₁eq] using
      entropicSoftmin_add_const (f := fun w : Y × X ↦ (c w.swap).toReal) (ν := μ) (ε := ε)
        (hc.comp measurable_swap).ennreal_toReal (fun w ↦ hfB w.swap) hφ₁ hφ₁C hε (-a) y
  have hφ_fixed : φ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ := funext fun x ↦ by
    simpa only [← hψ_shift, φ, hφ₁eq] using (entropicSoftmin_add_const
      (f := fun z : X × Y ↦ (c z).toReal) (ν := ν) (ε := ε) hc.ennreal_toReal hfB hψ₁ hψ₁C hε
      a x).symm
  have hφ_bounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ B := fun x ↦ by
    have hint_x := integrable_exp_sub_div (ν := ν) (ε := ε) hc.ennreal_toReal hfB hψ₁ hψ₁C x
    have hZx : 0 < ∫ y, Real.exp ((ψ₁ y - (c (x, y)).toReal) / ε) ∂ν := integral_exp_pos hint_x
    have hhi : ∫ y, Real.exp ((ψ₁ y - (c (x, y)).toReal) / ε) ∂ν ≤
        ∫ y, Real.exp (ψ₁ y / ε) ∂ν := integral_mono hint_x hint_a fun y ↦ Real.exp_le_exp.2 <|
      div_le_div_of_nonneg_right (sub_le_self _ ENNReal.toReal_nonneg) ε.coe_nonneg
    have hlo : Real.exp (-(B : ℝ) / ε) * ∫ y, Real.exp (ψ₁ y / ε) ∂ν ≤
        ∫ y, Real.exp ((ψ₁ y - (c (x, y)).toReal) / ε) ∂ν := by
      rw [← integral_const_mul]
      refine integral_mono (hint_a.const_mul _) hint_x fun y ↦ ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      calc (-(B : ℝ)) / ε + ψ₁ y / ε = (ψ₁ y - B) / ε := by ring
        _ ≤ (ψ₁ y - (c (x, y)).toReal) / ε :=
          div_le_div_of_nonneg_right (by linarith [(abs_le.1 (hfB (x, y))).2]) ε.coe_nonneg
    have hm₁ := mul_le_mul_of_nonneg_left (Real.log_le_log hZx hhi) hε0.le
    have hlog_lo := Real.log_le_log (mul_pos (Real.exp_pos _) hZa) hlo
    rw [Real.log_mul (Real.exp_pos _).ne' hZa.ne', Real.log_exp] at hlog_lo
    have hm₂ := mul_le_mul_of_nonneg_left hlog_lo hε0.le
    rw [mul_add, mul_div_cancel₀ _ hε0.ne'] at hm₂
    dsimp only [φ, a]
    rw [hφ₁eq, entropicSoftmin]
    exact ⟨by linarith, by linarith⟩
  have hφ : Measurable φ := hφ₁.sub_const _
  have hψ : Measurable ψ :=
    measurable_entropicSoftmin (hc.comp measurable_swap).ennreal_toReal hφ
  have hψ_bounds : ∀ y, |ψ y| ≤ B :=
    abs_entropicSoftmin_le_of_nonneg_le (hc.comp measurable_swap).ennreal_toReal
      (fun _ ↦ ENNReal.toReal_nonneg) (fun w ↦ (abs_le.1 (hfB w.swap)).2) hφ hφ_bounds hε
  exact ⟨φ, ψ, a, hφ, hψ, fun _ ↦ rfl, hψ_shift, hφ_bounds, hψ_bounds, hφ_fixed, rfl⟩

/-- Internal helper retaining the softmin fixed-point identities alongside the public properties of
canonical Schrödinger potentials. -/
private theorem exists_canonical_potentials [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      φ = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ ∧
      ψ = entropicSoftmin (fun w : Y × X ↦ (c w.swap).toReal) ε μ φ := by
  have hfin : ∀ z, c z ≠ ∞ := fun z ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  have hfB := abs_toReal_le_of_le hcB
  obtain ⟨π, hπ, hopt, φ₀, ψ₀, C₀, hφ₀, hψ₀, hφ₀C, hψ₀C, hπeq⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost (μ := μ) (ν := ν) hc hcB hε
  obtain ⟨φ₁, ψ₁, C₁, hφ₁, hψ₁, hφ₁C, hψ₁C, hφ₀₁, hψ₀₁, hφ₁eq, hψ₁eq⟩ :=
    exists_softmin_fixed_point_of_isCoupling hc hcB hε hπ hφ₀ hψ₀ hφ₀C hψ₀C hπeq
  obtain ⟨φ, ψ, a, hφ, hψ, hφ_shift, hψ_shift, hφ_bounds, hψ_bounds, hφ_fixed, hψ_fixed⟩ :=
    entropicSoftmin_shift_bounds (μ := μ) (ν := ν) hc hcB hε hφ₁ hψ₁ hφ₁C hψ₁C hφ₁eq hψ₁eq
  have hφ_abs : ∀ x, |φ x| ≤ B := fun x ↦
    abs_le.2 ⟨by linarith [(hφ_bounds x).1, B.coe_nonneg], (hφ_bounds x).2⟩
  have hrow_eq : ∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1 := fun x ↦ by
    simp_rw [entropicGibbsFactor_of_ne_top (hfin _)]
    conv_lhs => rw [hφ_fixed]
    exact integral_exp_entropicSoftmin hc.ennreal_toReal hfB hψ hψ_bounds hε x
  have hcol_eq : ∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1 := fun y ↦ by
    simp_rw [entropicGibbsFactor_of_ne_top (hfin _)]
    have heq : (fun x ↦ Real.exp ((φ x + ψ y - (c (x, y)).toReal) / ε)) =
        fun x ↦ Real.exp ((ψ y + φ x - (c (y, x).swap).toReal) / ε) :=
      funext fun x ↦ by simp only [Prod.swap_prod_mk, add_comm (φ x)]
    rw [heq, hψ_fixed]
    exact integral_exp_entropicSoftmin (hc.comp measurable_swap).ennreal_toReal
      (fun w ↦ hfB w.swap) hφ hφ_abs hε y
  have hφ_ae : φ =ᵐ[μ] fun x ↦ φ₀ x - a := hφ₀₁.symm.mono fun x hx ↦ by rw [hφ_shift x, hx]
  have hψ_ae : ψ =ᵐ[ν] fun y ↦ ψ₀ y + a := hψ₀₁.symm.mono fun y hy ↦ by rw [hψ_shift y, hy]
  have hπ_new : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) := by
    rw [hπeq, entropicGibbsFactor_eq_exp_of_forall_ne_top hfin]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hφ_ae,
      Measure.quasiMeasurePreserving_snd.ae_eq_comp hψ_ae] with z hz₁ hz₂
    simp only [Function.comp_apply] at hz₁ hz₂
    rw [hz₁, hz₂]; congr 3; ring
  have hφi : Integrable φ μ := .of_bound hφ.aestronglyMeasurable B (ae_of_all _ hφ_abs)
  have hψi : Integrable ψ ν := .of_bound hψ.aestronglyMeasurable B (ae_of_all _ hψ_bounds)
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ hψ
    (fun x ↦ (hφ_bounds x).2) (fun y ↦ le_of_abs_le (hψ_bounds y))
  have hent_val : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
    rw [← hopt]
    exact (hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc.aemeasurable hε hφi hψi
      hexp (hopt ▸ entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)).2 hπ_new
  have hkant_val : kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
    rw [← hπ.entropicDualValue_eq_of_eq_withDensity hπ_new hexp, hent_val]
  exact ⟨φ, ψ, hφ, hψ, hφ_bounds, hψ_bounds, hrow_eq, hcol_eq, hkant_val, hent_val, hφ_fixed,
    hψ_fixed⟩

/-- **Canonical Schrödinger potentials for a bounded cost.** For probability measures `μ` and `ν`,
a measurable cost bounded by `B` and a positive temperature `ε`, there exist measurable potentials
`φ` and `ψ` that satisfy `0 ≤ φ ≤ B` and `|ψ| ≤ B` everywhere, solve both Schrödinger marginal
equations pointwise everywhere on `X` and `Y`, and attain the regularised transport cost in both
the Kantorovich and entropic dual objectives.

This is the uniform `L^∞` part of Proposition 1 of Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré
(2019), together with the everywhere fixed-point equations. -/
theorem exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ), Measurable φ ∧ Measurable ψ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ B) ∧ (∀ y, |ψ y| ≤ B) ∧
      (∀ x, ∫ y, entropicGibbsFactor c ε φ ψ (x, y) ∂ν = 1) ∧
      (∀ y, ∫ x, entropicGibbsFactor c ε φ ψ (x, y) ∂μ = 1) ∧
      kantorovichDualValue μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal ∧
      entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent, -, -⟩ :=
    exists_canonical_potentials (μ := μ) (ν := ν) hc hcB hε
  exact ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent⟩

/-- **Regularity of canonical Schrödinger potentials (Feydy et al., Proposition 1).** On extended
pseudometric spaces, when the cost is bounded by `B` and its slices are `K₁`- and `K₂`-Lipschitz,
the canonical Schrödinger potentials of
`exists_entropicDualValue_eq_toReal_entropicTransportCost_and_le` are themselves `K₁`- and
`K₂`-Lipschitz, uniformly in the temperature `ε ≠ 0`. -/
theorem exists_lipschitzWith_entropicDualValue_eq_toReal_entropicTransportCost
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
  have hfB := abs_toReal_le_of_le hcB
  obtain ⟨φ, ψ, hφ, hψ, hφB, hψB, hrow, hcol, hkant, hent, hφeq, hψeq⟩ :=
    exists_canonical_potentials (μ := μ) (ν := ν) hc hcB hε
  have hφ_abs : ∀ x, |φ x| ≤ B := fun x ↦
    abs_le.2 ⟨by linarith [(hφB x).1, B.coe_nonneg], (hφB x).2⟩
  have hφL : LipschitzWith K₁ φ := by
    rw [hφeq]
    exact lipschitzWith_entropicSoftmin (ν := ν) hc.ennreal_toReal hfB hψ hψB hε hL₁
  have hψL : LipschitzWith K₂ ψ := by
    rw [hψeq]
    exact lipschitzWith_entropicSoftmin (f := fun w : Y × X ↦ (c w.swap).toReal) (ν := μ)
      (hc.comp measurable_swap).ennreal_toReal (fun w ↦ hfB w.swap) hφ hφ_abs hε hL₂
  exact ⟨φ, ψ, hφ, hψ, hφL, hψL, hφB, hψB, hrow, hcol, hkant, hent⟩

end CanonicalPotentials

section MarginalStability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0} {μ μ' : Measure X} {ν ν' : Measure Y}

/-- Varying only the source marginal from `μ'` to `μ` increases the regularised cost by at most
the difference of expectations of the canonical source potential of `(μ', ν)`. -/
private theorem exists_source_potential_diff_bound [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    ∃ φ' : X → ℝ, Measurable φ' ∧ (∀ x, 0 ≤ φ' x ∧ φ' x ≤ B) ∧
      (∃ ψ' : Y → ℝ, Measurable ψ' ∧ (∀ y, |ψ' y| ≤ B) ∧
        φ' = entropicSoftmin (fun z ↦ (c z).toReal) ε ν ψ') ∧
      (entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal ≤
        ∫ x, φ' x ∂μ' - ∫ x, φ' x ∂μ := by
  obtain ⟨φ', ψ', hφ', hψ', hφ'B, hψ'B, hrow, -, hkant, -, hφ'eq, -⟩ :=
    exists_canonical_potentials (μ := μ') (ν := ν) hc hcB hε
  have hφ'abs : ∀ x, |φ' x| ≤ B := fun x ↦
    abs_le.2 ⟨by linarith [(hφ'B x).1, B.coe_nonneg], (hφ'B x).2⟩
  have hφ'μ : Integrable φ' μ := .of_bound hφ'.aestronglyMeasurable B (ae_of_all _ hφ'abs)
  have hψ'ν : Integrable ψ' ν := .of_bound hψ'.aestronglyMeasurable B (ae_of_all _ hψ'B)
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hφ' hψ'
    (fun x ↦ (hφ'B x).2) (fun y ↦ le_of_abs_le (hψ'B y))
  have hint_one : ∫ z, entropicGibbsFactor c ε φ' ψ' z ∂μ.prod ν = 1 := by
    rw [integral_prod _ hexp]
    simp [hrow]
  have hdual := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε hφ'μ hψ'ν hexp
  rw [entropicDualValue_def, integral_sub hexp (integrable_const _), hint_one] at hdual
  simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero, sub_zero] at hdual
  rw [kantorovichDualValue_def] at hkant hdual
  exact ⟨φ', hφ', hφ'B, ⟨ψ', hψ', hψ'B, hφ'eq⟩, by linarith⟩

omit [MeasurableSpace X] in
private theorem lipschitzWith_one_sub_div [PseudoEMetricSpace X] {φ : X → ℝ} {K : ℝ≥0}
    (hK : K ≠ 0) (hL : LipschitzWith K φ) (a : ℝ) :
    LipschitzWith 1 (fun x ↦ (φ x - a) / K) := fun x x' ↦ by
  have hK0 : (0 : ℝ) < K := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK)
  have hsub : (φ x - a) / K - (φ x' - a) / K = (φ x - φ x') / K := by ring
  rw [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq, hsub, abs_div, abs_of_pos hK0,
    ENNReal.ofReal_div_of_pos hK0, ENNReal.ofReal_coe_nnreal, ← Real.dist_eq, ← edist_dist]
  exact ENNReal.div_le_of_le_mul' (hL x x')

private theorem exists_lipschitzWith_source_potential_diff_bound [PseudoEMetricSpace X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν] (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ∃ φ' : X → ℝ, Measurable φ' ∧ LipschitzWith K₁ φ' ∧ (∀ x, 0 ≤ φ' x ∧ φ' x ≤ B) ∧
      (∀ ρ : Measure X, [IsFiniteMeasure ρ] → Integrable φ' ρ) ∧
      (entropicTransportCost c ε μ' ν).toReal - (entropicTransportCost c ε μ ν).toReal ≤
        ∫ x, φ' x ∂μ' - ∫ x, φ' x ∂μ := by
  obtain ⟨φ', hφ', hφ'B, ⟨ψ', hψ', hψ'B, hφ'eq⟩, hle⟩ :=
    exists_source_potential_diff_bound (μ := μ) (μ' := μ') (ν := ν) hc hcB hε
  refine ⟨φ', hφ', hφ'eq ▸ lipschitzWith_entropicSoftmin (ν := ν) hc.ennreal_toReal
    (abs_toReal_le_of_le hcB) hψ' hψ'B hε hL₁, hφ'B, fun ρ _ ↦
    .of_bound hφ'.aestronglyMeasurable B (ae_of_all _ fun x ↦
      abs_le.2 ⟨by linarith [(hφ'B x).1, B.coe_nonneg], (hφ'B x).2⟩), hle⟩

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
