/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.MeanEmbedding
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Continuity
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Symmetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.InformationTheory.KullbackLeibler.Convex

/-!
# Sinkhorn divergences

The entropic transport cost `OT_ε(μ, ν) = TauCeti.entropicTransportCost c ε μ ν` is biased: in
general `OT_ε(μ, μ) ≠ 0`. The *Sinkhorn divergence*

`S_ε(μ, ν) = OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2`

removes this bias, so that `S_ε(μ, μ) = 0`. Equivalently, in terms of the *Sinkhorn negentropy*
`F_ε(μ) = -OT_ε(μ, μ) / 2` (`TauCeti.sinkhornNegentropy`),

`S_ε(μ, ν) = OT_ε(μ, ν) + F_ε(μ) + F_ε(ν)`.

This file develops the global theory of `S_ε` and `F_ε` at positive temperature `ε ≠ 0`, following
Feydy–Séjourné–Vialard–Amari–Trouvé–Peyré (AISTATS 2019), Theorem 1 and Propositions 2 and 3:

1. **Positivity and definiteness (`TauCeti.sinkhornDivergence_nonneg`,
   `TauCeti.sinkhornDivergence_eq_zero_iff`).** When the Gibbs kernel `k(x, y) = exp (-c(x, y) / ε)`
   is positive definite, evaluating the dual problem of `OT_ε(μ, ν)` at the symmetric
   self-potentials `p` of `μ` and `q` of `ν` (`TauCeti.exists_isCoupling_entropicGibbsFactor_self`)
   bounds `S_ε(μ, ν)` below by `(ε / 2) * ‖m a - m b‖ ^ 2`, where `a = e^{p/ε} μ` and
   `b = e^{q/ε} ν` have kernel energy `1` and `m` is the kernel mean embedding
   (`Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`). When `k` is also universal, `m` is
   injective (`Matrix.PosSemidef.kernelMeanEmbedding_inj`), and the marginal equation
   `μ = (∫ k(·, y) da(y)) • a` recovers `μ = ν` from `a = b`.
2. **Convexity of Sinkhorn negentropy and separate convexity of Sinkhorn divergences
   (`TauCeti.sinkhornNegentropy_smul_add_smul_le`, `TauCeti.sinkhornNegentropy_smul_add_smul_lt`,
   `TauCeti.sinkhornDivergence_smul_add_smul_left_le`,
   `TauCeti.sinkhornDivergence_smul_add_smul_left_lt`).** Writing `-∫ p dμ` in terms of
   `klDiv μ (e^{p/ε} μ)` and combining the joint convexity of `klDiv` with weak duality at the
   convex combination `w₀ • a₀ + w₁ • a₁` of the tilted measures yields the quantitative strong
   convexity bound
   `F_ε(w₀ μ₀ + w₁ μ₁) + (ε / 2) w₀ w₁ ‖m a₀ - m a₁‖ ^ 2 ≤ w₀ F_ε(μ₀) + w₁ F_ε(μ₁)`.
   Combining this with the separate convexity of `OT_ε` gives separate convexity of `S_ε`, which is
   strict whenever `k` is universal.
3. **`W₁`-Lipschitz stability, weak continuity, and metrization of weak convergence
   (`TauCeti.ofReal_abs_sinkhornDivergence_sub_le_wassersteinEDist_one`,
   `TauCeti.continuous_sinkhornDivergence_of_lipschitzWith`,
   `TauCeti.continuous_sinkhornDivergence`,
   `TauCeti.tendsto_sinkhornDivergence_zero_iff_tendsto`).** Temperature-independent `W₁` stability
   and joint weak continuity of `OT_ε` pass directly to `S_ε`. On a compact metrizable Borel space,
   compactness of `ProbabilityMeasure X` together with continuity, nonnegativity, and definiteness
   implies that `S_ε(μ_i, μ) → 0` if and only if `μ_i → μ` weakly.

The Sinkhorn divergence is real-valued, through `ENNReal.toReal` of the three entropic costs. It
is the intended value when these are finite, as they are for the bounded costs considered here.

## Main definitions

* `TauCeti.sinkhornDivergence c ε μ ν`: the debiased entropic transport cost
  `OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2`.
* `TauCeti.sinkhornNegentropy c ε μ`: the Sinkhorn negentropy `-OT_ε(μ, μ) / 2`.

## Main statements

* `TauCeti.sinkhornDivergence_self`, `TauCeti.sinkhornDivergence_const`,
  `TauCeti.sinkhornDivergence_dirac_dirac`, `TauCeti.sinkhornDivergence_comm`, and
  `TauCeti.sinkhornDivergence_comm_of_posSemidef`: diagonal vanishing, constant costs, evaluation on
  point masses, and symmetry.
* `TauCeti.sinkhornDivergence_nonneg` and `TauCeti.sinkhornDivergence_eq_zero_iff`: nonnegativity
  for positive-definite Gibbs kernels and definiteness when the Gibbs kernel is universal.
* `TauCeti.sinkhornNegentropy_smul_add_smul_le` and `TauCeti.sinkhornNegentropy_smul_add_smul_lt`:
  convexity and strict convexity of the Sinkhorn negentropy.
* `TauCeti.sinkhornDivergence_smul_add_smul_left_le`,
  `TauCeti.sinkhornDivergence_smul_add_smul_right_le`,
  `TauCeti.sinkhornDivergence_smul_add_smul_left_lt`, and
  `TauCeti.sinkhornDivergence_smul_add_smul_right_lt`: separate convexity and strict separate
  convexity of the Sinkhorn divergence in each marginal.
* `TauCeti.ofReal_abs_sinkhornDivergence_sub_le_wassersteinEDist_one` and
  `TauCeti.abs_sinkhornDivergence_sub_le_wassersteinEDist_one`: `W₁`-Lipschitz stability of the
  Sinkhorn divergence, uniformly in the temperature.
* `TauCeti.continuous_sinkhornDivergence_of_lipschitzWith`,
  `TauCeti.continuous_sinkhornDivergence`, and
  `TauCeti.tendsto_sinkhornDivergence_zero_iff_tendsto`: joint weak continuity (on separable
  pseudometric spaces for bounded slicewise-Lipschitz costs, and on compact pseudometrizable spaces
  for arbitrary continuous finite costs) and metrization of weak convergence on compact metrizable
  spaces.

For a continuous bounded cost the continuity hypothesis on the Gibbs kernel is supplied by
`TauCeti.continuous_entropicGibbsKernel`.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Theorem 1, Propositions 2 and 3, and their proofs in the supplementary material.
-/

public section

noncomputable section

open Filter InformationTheory MeasureTheory Function Set
open scoped ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {c : X × X → ℝ≥0∞} {ε B : ℝ≥0} {μ ν : Measure X}

/-! ### Definitions and elementary properties -/

/-- The *Sinkhorn divergence* `OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2`, the entropic
transport cost `TauCeti.entropicTransportCost c ε` debiased by the two self-transport costs. The
three costs are read through `ENNReal.toReal`, so this is the intended value when they are finite,
for instance for a bounded cost and probability measures. -/
def sinkhornDivergence (c : X × X → ℝ≥0∞) (ε : ℝ≥0) (μ ν : Measure X) : ℝ :=
  (entropicTransportCost c ε μ ν).toReal - (entropicTransportCost c ε μ μ).toReal / 2 -
    (entropicTransportCost c ε ν ν).toReal / 2

/-- The Sinkhorn divergence is the entropic transport cost minus half of the two self-transport
costs. The definition's body is not exposed, so this is the lemma downstream modules should
rewrite with. -/
theorem sinkhornDivergence_def :
    sinkhornDivergence c ε μ ν = (entropicTransportCost c ε μ ν).toReal -
      (entropicTransportCost c ε μ μ).toReal / 2 - (entropicTransportCost c ε ν ν).toReal / 2 :=
  (rfl)

/-- The *Sinkhorn negentropy* `-OT_ε(μ, μ) / 2`, half the negative entropic self-transport cost
(Feydy et al., §2.3). Debiasing `OT_ε(μ, ν)` adds the Sinkhorn negentropies of both marginals. -/
def sinkhornNegentropy (c : X × X → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) : ℝ :=
  -(entropicTransportCost c ε μ μ).toReal / 2

/-- Unfolding lemma for `TauCeti.sinkhornNegentropy`. -/
theorem sinkhornNegentropy_def :
    sinkhornNegentropy c ε μ = -(entropicTransportCost c ε μ μ).toReal / 2 :=
  (rfl)

/-- Decomposition of the Sinkhorn divergence into the entropic transport cost plus the Sinkhorn
negentropies of the two marginals. -/
theorem sinkhornDivergence_eq_add_sinkhornNegentropy :
    sinkhornDivergence c ε μ ν =
      (entropicTransportCost c ε μ ν).toReal + sinkhornNegentropy c ε μ +
        sinkhornNegentropy c ε ν := by
  rw [sinkhornDivergence_def, sinkhornNegentropy_def, sinkhornNegentropy_def]
  ring

/-- The Sinkhorn divergence vanishes on the diagonal. -/
@[simp]
theorem sinkhornDivergence_self (c : X × X → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) :
    sinkhornDivergence c ε μ μ = 0 := by
  rw [sinkhornDivergence_def]
  ring

/-- For a constant cost, debiasing cancels the constant completely on probability measures. -/
@[simp]
theorem sinkhornDivergence_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : ℝ≥0∞)
    (ε : ℝ≥0) : sinkhornDivergence (fun _ ↦ a) ε μ ν = 0 := by
  simp [sinkhornDivergence_def]
  ring

/-- For a constant cost, the Sinkhorn negentropy of a probability measure is `-a.toReal / 2`. -/
@[simp]
theorem sinkhornNegentropy_const [IsProbabilityMeasure μ] (a : ℝ≥0∞) (ε : ℝ≥0) :
    sinkhornNegentropy (fun _ ↦ a) ε μ = -a.toReal / 2 := by
  simp [sinkhornNegentropy_def]

/-- On a Dirac mass, the Sinkhorn negentropy equals `-(c (x, x)).toReal / 2` at every
temperature. -/
theorem sinkhornNegentropy_dirac (hc : Measurable c) (x : X) :
    sinkhornNegentropy c ε (Measure.dirac x) = -(c (x, x)).toReal / 2 := by
  rw [sinkhornNegentropy_def, entropicTransportCost_dirac_dirac hc]

/-- Between two Dirac masses, the Sinkhorn divergence reduces to the debiased ground cost
`c(x, y) - c(x, x) / 2 - c(y, y) / 2` at every temperature. -/
theorem sinkhornDivergence_dirac_dirac (hc : Measurable c) (x y : X) :
    sinkhornDivergence c ε (Measure.dirac x) (Measure.dirac y) =
      (c (x, y)).toReal - (c (x, x)).toReal / 2 - (c (y, y)).toReal / 2 := by
  rw [sinkhornDivergence_def, entropicTransportCost_dirac_dirac hc,
    entropicTransportCost_dirac_dirac hc, entropicTransportCost_dirac_dirac hc]

/-- A symmetric cost gives a symmetric Sinkhorn divergence between finite measures. -/
theorem sinkhornDivergence_comm [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hcs : c ∘ Prod.swap = c) :
    sinkhornDivergence c ε μ ν = sinkhornDivergence c ε ν μ := by
  rw [sinkhornDivergence_def, sinkhornDivergence_def, entropicTransportCost_comm hcs]
  ring

/-! ### Tilted measures and the self-potential equations -/

/-- The measure `e^{p/ε} μ`, tilted by the exponential of a potential `p`. -/
private def tilt (μ : Measure X) (ε : ℝ≥0) (p : X → ℝ) : Measure X :=
  μ.withDensity fun x ↦ ENNReal.ofReal (Real.exp (p x / ε))

private theorem measurable_tiltDensity {p : X → ℝ} (hp : Measurable p) :
    Measurable fun x ↦ ENNReal.ofReal (Real.exp (p x / ε)) :=
  ((hp.div_const _).exp).ennreal_ofReal

private theorem isFiniteMeasure_tilt [IsFiniteMeasure μ] {p : X → ℝ} {C : ℝ} (hp : Measurable p)
    (hpC : ∀ x, |p x| ≤ C) : IsFiniteMeasure (tilt μ ε p) := by
  refine isFiniteMeasure_withDensity_ofReal (Integrable.hasFiniteIntegral ?_)
  refine .of_bound (hp.div_const _).exp.aestronglyMeasurable (Real.exp (C / ε))
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact div_le_div_of_nonneg_right (le_of_abs_le (hpC x)) ε.coe_nonneg

/-- The integral of a Gibbs factor against `μ ⊗ ν` is the double integral of the Gibbs kernel
against the two tilted measures. -/
private theorem integral_entropicGibbsFactor_eq [SFinite μ] [SFinite ν] {p q : X → ℝ}
    (hp : Measurable p) (hq : Measurable q)
    (hexp : Integrable (entropicGibbsFactor c ε p q) (μ.prod ν)) :
    ∫ z, entropicGibbsFactor c ε p q z ∂μ.prod ν =
      ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂tilt μ ε p ∂tilt ν ε q := by
  rw [integral_prod_symm _ hexp, tilt, integral_withDensity_eq_integral_toReal_smul
    (measurable_tiltDensity hq) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [tilt, integral_withDensity_eq_integral_toReal_smul (measurable_tiltDensity hp)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top), smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), entropicGibbsFactor_apply]
  ring

/-- **The marginal equation of a Gibbs self-coupling.** If the Gibbs density of a potential `p`
couples `μ` with itself, then `μ` is recovered from the tilted measure `a = e^{p/ε} μ` as
`(∫ k(·, y) da(y)) • a`, where `k` is the Gibbs kernel. -/
private theorem eq_withDensity_tilt [SFinite μ] {p : X → ℝ} (hc : Measurable c)
    (hp : Measurable p)
    (hπ : IsCoupling ((μ.prod μ).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε p p z)) μ μ) :
    μ = (tilt μ ε p).withDensity fun x ↦
      ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ ε p := by
  have hK : Measurable (uncurry fun x y ↦ ENNReal.ofReal (entropicGibbsKernel c ε x y)) :=
    (measurable_entropicGibbsKernel hc).ennreal_ofReal
  have : SFinite (tilt μ ε p) := by unfold tilt; infer_instance
  have hH : Measurable fun x ↦
      ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ ε p :=
    hK.lintegral_prod_right'
  rw [tilt] at hH ⊢
  rw [← withDensity_mul _ (measurable_tiltDensity hp) hH]
  ext s hs
  rw [← hπ.measure_prod_univ hs, withDensity_apply _ (hs.prod MeasurableSet.univ),
    setLIntegral_prod _ ((measurable_entropicGibbsFactor hc hp hp).ennreal_ofReal.aemeasurable),
    withDensity_apply _ hs]
  refine setLIntegral_congr_fun hs fun x _ ↦ ?_
  rw [Measure.restrict_univ, Pi.mul_apply,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_tiltDensity hp) hK.of_uncurry_left,
    ← lintegral_const_mul _ ((measurable_tiltDensity hp).mul hK.of_uncurry_left)]
  refine lintegral_congr fun y ↦ ?_
  rw [entropicGibbsFactor_apply, Pi.mul_apply,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (entropicGibbsKernel_nonneg x y)),
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ring

/-- The self-potential of a probability measure, with the three equations used below: it gives
half of the self-transport cost, its tilted measure has kernel energy `1`, and it satisfies the
marginal equation. -/
private theorem exists_selfPotential [IsProbabilityMeasure μ] (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hcs : c ∘ Prod.swap = c) (hε : ε ≠ 0) :
    ∃ (p : X → ℝ) (C : ℝ), Measurable p ∧ (∀ x, |p x| ≤ C) ∧
      (entropicTransportCost c ε μ μ).toReal = 2 * ∫ x, p x ∂μ ∧
      ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂tilt μ ε p ∂tilt μ ε p = 1 ∧
      μ = (tilt μ ε p).withDensity fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ ε p := by
  obtain ⟨p, C, hp, hpC, hπ, -, hval⟩ :=
    exists_isCoupling_entropicGibbsFactor_self (μ := μ) hc hcB hcs hε
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := μ) (ε := ε) hc hp hp
    (fun x ↦ le_of_abs_le (hpC x)) (fun x ↦ le_of_abs_le (hpC x))
  refine ⟨p, C, hp, hpC, hval, ?_, eq_withDensity_tilt hc hp hπ⟩
  rw [← integral_entropicGibbsFactor_eq hp hp hexp]
  exact hπ.integral_entropicGibbsFactor_eq_one rfl hexp

/-- **Weak duality at the self-potentials.** Evaluating the dual problem of `OT_ε(μ, ν)` at the
self-potentials `p` of `μ` and `q` of `ν` bounds the Sinkhorn divergence below by `ε` times one
minus the kernel interaction of the tilted measures. -/
private theorem mul_one_sub_le_sinkhornDivergence [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    {p q : X → ℝ} {Cp Cq : ℝ} (hp : Measurable p) (hq : Measurable q) (hpC : ∀ x, |p x| ≤ Cp)
    (hqC : ∀ x, |q x| ≤ Cq) (hμ : (entropicTransportCost c ε μ μ).toReal = 2 * ∫ x, p x ∂μ)
    (hν : (entropicTransportCost c ε ν ν).toReal = 2 * ∫ x, q x ∂ν) :
    ε * (1 - ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂tilt μ ε p ∂tilt ν ε q) ≤
      sinkhornDivergence c ε μ ν := by
  have hexp := integrable_entropicGibbsFactor_of_le (μ := μ) (ν := ν) (ε := ε) hc hp hq
    (fun x ↦ le_of_abs_le (hpC x)) (fun x ↦ le_of_abs_le (hqC x))
  have hdual := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε
    (.of_bound hp.aestronglyMeasurable Cp (ae_of_all _ hpC))
    (.of_bound hq.aestronglyMeasurable Cq (ae_of_all _ hqC)) hexp
  rw [entropicDualValue_def, kantorovichDualValue_def, integral_sub hexp (integrable_const _),
    integral_entropicGibbsFactor_eq hp hq hexp] at hdual
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hdual
  rw [sinkhornDivergence_def, hμ, hν]
  linarith

/-! ### Nonnegativity and definiteness -/

omit [MeasurableSpace X] in
/-- A positive-definite Gibbs kernel of a bounded cost forces the cost to be symmetric. -/
private theorem comp_swap_eq_of_posSemidef (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε)) : c ∘ Prod.swap = c := by
  funext z
  have hfin : ∀ z, c z ≠ ∞ := fun z ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)
  have h := hk.isHermitian.apply z.1 z.2
  rw [star_trivial, entropicGibbsKernel_of_ne_top (hfin _),
    entropicGibbsKernel_of_ne_top (hfin _), Real.exp_eq_exp,
    div_left_inj₀ (NNReal.coe_ne_zero.2 hε), neg_inj] at h
  exact (ENNReal.toReal_eq_toReal_iff' (hfin _) (hfin _)).1 h

variable [TopologicalSpace X] [CompactSpace X]

/-- **The kernel lower bound for the Sinkhorn divergence.** The Sinkhorn divergence is at least
`ε / 2` times the squared distance between the kernel mean embeddings of the tilted measures
`e^{p/ε} μ` and `e^{q/ε} ν` of the self-potentials, each of which recovers its measure through the
marginal equation. -/
private theorem exists_sq_norm_le_sinkhornDivergence [OpensMeasurableSpace X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    ∃ (p q : X → ℝ) (Cp Cq : ℝ), Measurable p ∧ Measurable q ∧ (∀ x, |p x| ≤ Cp) ∧
      (∀ x, |q x| ≤ Cq) ∧
      μ = (tilt μ ε p).withDensity (fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ ε p) ∧
      ν = (tilt ν ε q).withDensity (fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt ν ε q) ∧
      ε / 2 * ‖hk.kernelMeanEmbedding (tilt μ ε p) - hk.kernelMeanEmbedding (tilt ν ε q)‖ ^ 2 ≤
        sinkhornDivergence c ε μ ν := by
  have hcs := comp_swap_eq_of_posSemidef hcB hε hk
  obtain ⟨p, Cp, hp, hpC, hμ, hEp, hμp⟩ := exists_selfPotential (μ := μ) hc hcB hcs hε
  obtain ⟨q, Cq, hq, hqC, hν, hEq, hνq⟩ := exists_selfPotential (μ := ν) hc hcB hcs hε
  have := isFiniteMeasure_tilt (μ := μ) (ε := ε) hp hpC
  have := isFiniteMeasure_tilt (μ := ν) (ε := ε) hq hqC
  refine ⟨p, q, Cp, Cq, hp, hq, hpC, hqC, hμp, hνq, ?_⟩
  rw [hk.norm_kernelMeanEmbedding_sub_sq (hk.integrable_kolmogorovFeature hkc _)
    (hk.integrable_kolmogorovFeature hkc _), hEp, hEq]
  have := mul_one_sub_le_sinkhornDivergence hc hcB hε hp hq hpC hqC hμ hν
  linarith

/-- **Nonnegativity of the Sinkhorn divergence.** On a compact space, for a bounded measurable cost
whose Gibbs kernel `exp (-c / ε)` is continuous and positive definite, and a positive temperature,
the Sinkhorn divergence of two probability measures is nonnegative. -/
theorem sinkhornDivergence_nonneg [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    0 ≤ sinkhornDivergence c ε μ ν := by
  obtain ⟨p, q, -, -, -, -, -, -, -, -, h⟩ :=
    exists_sq_norm_le_sinkhornDivergence (μ := μ) (ν := ν) hc hcB hε hk hkc
  exact (mul_nonneg (div_nonneg ε.coe_nonneg zero_le_two) (sq_nonneg _)).trans h

/-- **Definiteness of the Sinkhorn divergence.** On a compact space with `HasOuterApproxClosed`
(for instance a compact metrizable space) and its Borel σ-algebra, for a bounded measurable cost
whose Gibbs kernel `exp (-c / ε)` is continuous, positive definite and universal, and a positive
temperature, the Sinkhorn divergence of two probability measures vanishes exactly when they are
equal. -/
theorem sinkhornDivergence_eq_zero_iff [BorelSpace X] [HasOuterApproxClosed X]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ sinkhornDivergence_self c ε μ⟩
  obtain ⟨p, q, Cp, Cq, hp, hq, hpC, hqC, hμp, hνq, hle⟩ :=
    exists_sq_norm_le_sinkhornDivergence (μ := μ) (ν := ν) hc hcB hε hk hkc
  have := isFiniteMeasure_tilt (μ := μ) (ε := ε) hp hpC
  have := isFiniteMeasure_tilt (μ := ν) (ε := ε) hq hqC
  have hε2 : 0 < (ε : ℝ) / 2 := half_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε))
  have hsq : ‖hk.kernelMeanEmbedding (tilt μ ε p) - hk.kernelMeanEmbedding (tilt ν ε q)‖ ^ 2
      = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (h ▸ hle) hε2) (sq_nonneg _)
  have htilt : tilt μ ε p = tilt ν ε q :=
    (hk.kernelMeanEmbedding_inj hkc hku).1 (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff
      two_ne_zero |>.1 hsq)))
  rw [hμp, hνq, htilt]

omit [TopologicalSpace X] [CompactSpace X] in
/-- When the Gibbs kernel of a bounded cost is positive definite, the cost is symmetric and hence
so is the Sinkhorn divergence between finite measures. -/
theorem sinkhornDivergence_comm_of_posSemidef [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε μ ν = sinkhornDivergence c ε ν μ :=
  sinkhornDivergence_comm (comp_swap_eq_of_posSemidef hcB hε hk)

/-! ### Convexity of Sinkhorn negentropy and separate convexity -/

omit [TopologicalSpace X] [CompactSpace X] in
/-- Relative entropy of a probability measure `μ` against its tilted measure `e^{p/ε} μ` is finite
and equals `-(∫ p dμ) / ε + (tilt μ ε p).real univ - 1`. -/
private theorem klDiv_tilt_ne_top_and_toReal [IsProbabilityMeasure μ] {p : X → ℝ}
    {C : ℝ} (hp : Measurable p) (hpC : ∀ x, |p x| ≤ C) :
    klDiv μ (tilt μ ε p) ≠ ∞ ∧
      (klDiv μ (tilt μ ε p)).toReal = -(∫ x, p x ∂μ) / ε + (tilt μ ε p).real univ - 1 := by
  have := isFiniteMeasure_tilt (μ := μ) (ε := ε) hp hpC
  set f : X → ℝ := fun x ↦ -p x / ε
  have hf : Measurable f := hp.neg.div_const _
  have hpi : Integrable p μ := .of_bound hp.aestronglyMeasurable C (ae_of_all _ hpC)
  have hfi : Integrable f μ := hpi.neg.div_const _
  have hμeq : μ = (tilt μ ε p).withDensity fun x ↦ ENNReal.ofReal (Real.exp (f x)) := by
    rw [tilt, ← withDensity_mul _ (measurable_tiltDensity hp) hf.exp.ennreal_ofReal]
    refine (withDensity_one (μ := μ)).symm.trans (withDensity_congr_ae (ae_of_all _ fun x ↦ ?_))
    rw [Pi.one_apply, Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    dsimp only [f]
    rw [neg_div, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one]
  have hμa : μ ≪ tilt μ ε p := fun s hs ↦ by
    rw [hμeq]
    exact withDensity_absolutelyContinuous _ _ hs
  have hrn : μ.rnDeriv (tilt μ ε p) =ᵐ[μ] fun x ↦ ENNReal.ofReal (Real.exp (f x)) :=
    hμa.ae_le ((Measure.rnDeriv_withDensity (tilt μ ε p) hf.exp.ennreal_ofReal).mono fun x hx ↦
      (congrArg (fun ν : Measure X ↦ ν.rnDeriv (tilt μ ε p) x) hμeq).trans hx)
  have hllr : llr μ (tilt μ ε p) =ᵐ[μ] f := hrn.mono fun x hx ↦ by
    rw [llr_def]
    dsimp only
    rw [hx, ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]
  have hllri : Integrable (llr μ (tilt μ ε p)) μ := hfi.congr hllr.symm
  refine ⟨klDiv_ne_top hμa hllri, ?_⟩
  rw [toReal_klDiv hμa hllri, integral_congr_ae hllr]
  simp only [f, div_eq_mul_inv, integral_mul_const, integral_neg, probReal_univ]

omit [TopologicalSpace X] [CompactSpace X] in
/-- Radon–Nikodym sandwich bounds for a convex combination `w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁`
against `w₀ • μ₀ + w₁ • μ₁` when `|p₀|, |p₁| ≤ C`. -/
private theorem rnDeriv_smul_tilt_add_smul_tilt_bounds (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] {w₀ w₁ : ℝ≥0} {p₀ p₁ : X → ℝ} {C : ℝ} (hp₀ : Measurable p₀)
    (hp₁ : Measurable p₁) (hp₀C : ∀ x, |p₀ x| ≤ C) (hp₁C : ∀ x, |p₁ x| ≤ C) :
    (w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁) ≪ (w₀ • μ₀ + w₁ • μ₁) ∧
      (fun _ ↦ ENNReal.ofReal (Real.exp (-C / ε))) ≤ᵐ[w₀ • μ₀ + w₁ • μ₁]
        (w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁).rnDeriv (w₀ • μ₀ + w₁ • μ₁) ∧
      (w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁).rnDeriv (w₀ • μ₀ + w₁ • μ₁) ≤ᵐ[w₀ • μ₀ + w₁ • μ₁]
        fun _ ↦ ENNReal.ofReal (Real.exp (C / ε)) := by
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀C
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁C
  have : SigmaFinite (w₀ • μ₀ + w₁ • μ₁) := inferInstance
  set μw : Measure X := w₀ • μ₀ + w₁ • μ₁
  set aw : Measure X := w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁
  set lo : ℝ := Real.exp (-C / ε)
  set hi : ℝ := Real.exp (C / ε)
  have htilt_sandwich {ρ : Measure X} {q : X → ℝ} (hq : Measurable q) (hqC : ∀ x, |q x| ≤ C) :
      ENNReal.ofReal lo • ρ ≤ tilt ρ ε q ∧ tilt ρ ε q ≤ ENNReal.ofReal hi • ρ := by
    refine ⟨Measure.le_iff.2 fun s hs ↦ ?_, Measure.le_iff.2 fun s hs ↦ ?_⟩
    · rw [smul_apply, smul_eq_mul, ← setLIntegral_const, tilt, withDensity_apply _ hs]
      refine setLIntegral_mono (measurable_tiltDensity hq) fun x _ ↦ ENNReal.ofReal_le_ofReal ?_
      exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [(abs_le.1 (hqC x)).1])
        ε.coe_nonneg)
    · rw [smul_apply, smul_eq_mul, ← setLIntegral_const, tilt, withDensity_apply _ hs]
      refine setLIntegral_mono measurable_const fun x _ ↦ ENNReal.ofReal_le_ofReal ?_
      exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [(abs_le.1 (hqC x)).2])
        ε.coe_nonneg)
  obtain ⟨h₀lo, h₀hi⟩ := htilt_sandwich (ρ := μ₀) hp₀ hp₀C
  obtain ⟨h₁lo, h₁hi⟩ := htilt_sandwich (ρ := μ₁) hp₁ hp₁C
  have haw_lo : ENNReal.ofReal lo • μw ≤ aw := Measure.le_iff.2 fun s _ ↦ by
    have h₀ := h₀lo s
    have h₁ := h₁lo s
    simp only [μw, aw, add_apply, smul_apply, smul_eq_mul] at h₀ h₁ ⊢
    calc ENNReal.ofReal lo * (w₀ * μ₀ s + w₁ * μ₁ s)
        = w₀ * (ENNReal.ofReal lo * μ₀ s) + w₁ * (ENNReal.ofReal lo * μ₁ s) := by ring
      _ ≤ w₀ * tilt μ₀ ε p₀ s + w₁ * tilt μ₁ ε p₁ s := by gcongr
  have haw_hi : aw ≤ ENNReal.ofReal hi • μw := Measure.le_iff.2 fun s _ ↦ by
    have h₀ := h₀hi s
    have h₁ := h₁hi s
    simp only [μw, aw, add_apply, smul_apply, smul_eq_mul] at h₀ h₁ ⊢
    calc w₀ * tilt μ₀ ε p₀ s + w₁ * tilt μ₁ ε p₁ s
        ≤ w₀ * (ENNReal.ofReal hi * μ₀ s) + w₁ * (ENNReal.ofReal hi * μ₁ s) := by gcongr
      _ = ENNReal.ofReal hi * (w₀ * μ₀ s + w₁ * μ₁ s) := by ring
  have hac : aw ≪ μw := Measure.absolutelyContinuous_of_le_smul haw_hi
  refine ⟨hac, ?_, ?_⟩
  · refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const fun s _ _ ↦ ?_
    rw [setLIntegral_const, Measure.setLIntegral_rnDeriv hac s]
    simpa [smul_apply, smul_eq_mul] using haw_lo s
  · refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (aw.measurable_rnDeriv μw) fun s _ _ ↦ ?_
    simpa [smul_apply, smul_eq_mul] using (Measure.setLIntegral_rnDeriv_le s).trans (haw_hi s)

omit [TopologicalSpace X] [CompactSpace X] in
/-- A convex combination of two tilted probability measures `e^{p₀/ε} μ₀` and `e^{p₁/ε} μ₁` with
bounded potentials is itself a tilt `e^{p/ε} (w₀ • μ₀ + w₁ • μ₁)` by a bounded measurable
potential `p`. -/
private theorem exists_tilt_eq_smul_add_smul (μ₀ μ₁ : Measure X) [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1) (hε : ε ≠ 0) {p₀ p₁ : X → ℝ}
    {C₀ C₁ : ℝ} (hp₀ : Measurable p₀) (hp₁ : Measurable p₁) (hp₀C : ∀ x, |p₀ x| ≤ C₀)
    (hp₁C : ∀ x, |p₁ x| ≤ C₁) :
    ∃ (p : X → ℝ) (C : ℝ), Measurable p ∧ (∀ x, |p x| ≤ C) ∧
      tilt (w₀ • μ₀ + w₁ • μ₁) ε p = w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁ := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  set C : ℝ := max 0 (max C₀ C₁)
  have hp₀' : ∀ x, |p₀ x| ≤ C :=
    fun x ↦ (hp₀C x).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hp₁' : ∀ x, |p₁ x| ≤ C :=
    fun x ↦ (hp₁C x).trans ((le_max_right _ _).trans (le_max_right _ _))
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀'
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁'
  have : IsProbabilityMeasure (w₀ • μ₀ + w₁ • μ₁) := ⟨by simp [← ENNReal.coe_add, hw]⟩
  obtain ⟨hac, hrn_lo, hrn_hi⟩ :=
    rnDeriv_smul_tilt_add_smul_tilt_bounds (ε := ε) μ₀ μ₁ (w₀ := w₀) (w₁ := w₁) hp₀ hp₁ hp₀' hp₁'
  set μw : Measure X := w₀ • μ₀ + w₁ • μ₁
  set aw : Measure X := w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁
  set lo : ℝ := Real.exp (-C / ε)
  set hi : ℝ := Real.exp (C / ε)
  have hlo_pos : 0 < lo := Real.exp_pos _
  have hlo_hi : lo ≤ hi := Real.exp_le_exp.2
    (div_le_div_of_nonneg_right (by linarith [le_max_left 0 (max C₀ C₁)]) ε.coe_nonneg)
  set r : X → ℝ := fun x ↦ max lo (min hi (aw.rnDeriv μw x).toReal)
  set p : X → ℝ := fun x ↦ ε * Real.log (r x)
  have hr_meas : Measurable r :=
    measurable_const.max (measurable_const.min (aw.measurable_rnDeriv μw).ennreal_toReal)
  have hr_pos : ∀ x, 0 < r x := fun x ↦ hlo_pos.trans_le (le_max_left _ _)
  have hp_abs : ∀ x, |p x| ≤ C := fun x ↦ by
    have h₁ := Real.log_le_log hlo_pos (le_max_left lo (min hi (aw.rnDeriv μw x).toReal))
    have h₂ := Real.log_le_log (hr_pos x) (max_le hlo_hi (min_le_left _ _))
    rw [Real.log_exp, div_le_iff₀ hε0] at h₁
    rw [Real.log_exp, le_div_iff₀ hε0] at h₂
    dsimp only [p]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨p, C, hr_meas.log.const_mul _, hp_abs, ?_⟩
  rw [tilt, ← Measure.withDensity_rnDeriv_eq aw μw hac]
  refine withDensity_congr_ae ?_
  filter_upwards [hrn_lo, hrn_hi, aw.rnDeriv_lt_top μw] with x hxlo hxhi hxtop
  have hto_lo : lo ≤ (aw.rnDeriv μw x).toReal :=
    (ENNReal.toReal_ofReal hlo_pos.le).symm.trans_le (ENNReal.toReal_mono hxtop.ne hxlo)
  have hto_hi : (aw.rnDeriv μw x).toReal ≤ hi :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hxhi).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  have hrx : r x = (aw.rnDeriv μw x).toReal := by
    simp only [r, min_eq_right hto_hi, max_eq_right hto_lo]
  dsimp only [p]
  rw [mul_div_cancel_left₀ _ hε0.ne', Real.exp_log (hr_pos x), hrx, ENNReal.ofReal_toReal hxtop.ne]

omit [TopologicalSpace X] [CompactSpace X] in
/-- Joint convexity of `klDiv` translates the tilt identity
`tilt (w₀ • μ₀ + w₁ • μ₁) ε pw = w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁` into convexity of the
linear potential term `-∫ p dμ`. -/
private theorem neg_integral_le_of_tilt_eq_smul_add_smul {μ₀ μ₁ : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1)
    (hε : ε ≠ 0) {p₀ p₁ pw : X → ℝ} {C₀ C₁ Cw : ℝ} (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    (hpw : Measurable pw) (hp₀C : ∀ x, |p₀ x| ≤ C₀) (hp₁C : ∀ x, |p₁ x| ≤ C₁)
    (hpwC : ∀ x, |pw x| ≤ Cw)
    (htilt : tilt (w₀ • μ₀ + w₁ • μ₁) ε pw = w₀ • tilt μ₀ ε p₀ + w₁ • tilt μ₁ ε p₁) :
    -∫ x, pw x ∂(w₀ • μ₀ + w₁ • μ₁) ≤
      w₀ * (-∫ x, p₀ x ∂μ₀) + w₁ * (-∫ x, p₁ x ∂μ₁) := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  set μw : Measure X := w₀ • μ₀ + w₁ • μ₁
  have : IsProbabilityMeasure μw := ⟨by simp [μw, ← ENNReal.coe_add, hw]⟩
  set a₀ := tilt μ₀ ε p₀
  set a₁ := tilt μ₁ ε p₁
  set aw := tilt μw ε pw
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀C
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁C
  obtain ⟨hkl₀_fin, hkl₀⟩ := klDiv_tilt_ne_top_and_toReal (μ := μ₀) (ε := ε) hp₀ hp₀C
  obtain ⟨hkl₁_fin, hkl₁⟩ := klDiv_tilt_ne_top_and_toReal (μ := μ₁) (ε := ε) hp₁ hp₁C
  obtain ⟨_, hklw⟩ := klDiv_tilt_ne_top_and_toReal (μ := μw) (ε := ε) hpw hpwC
  have htw_sum : (w₀ : ℝ) + w₁ = 1 := by exact_mod_cast hw
  have hkl_conv : (klDiv μw aw).toReal ≤
      w₀ * (klDiv μ₀ a₀).toReal + w₁ * (klDiv μ₁ a₁).toReal := by
    have hle : klDiv μw aw ≤ w₀ * klDiv μ₀ a₀ + w₁ * klDiv μ₁ a₁ := by
      rw [show aw = w₀ • a₀ + w₁ • a₁ from htilt]
      exact klDiv_smul_add_smul_smul_add_smul_le w₀ w₁
    have h₀ : (w₀ : ℝ≥0∞) * klDiv μ₀ a₀ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hkl₀_fin
    have h₁ : (w₁ : ℝ≥0∞) * klDiv μ₁ a₁ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hkl₁_fin
    have hto := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h₀, h₁⟩) hle
    rwa [ENNReal.toReal_add h₀ h₁, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.coe_toReal] at hto
  have haw_mass : aw.real univ = w₀ * a₀.real univ + w₁ * a₁.real univ := by
    rw [show aw = w₀ • a₀ + w₁ • a₁ from htilt, measureReal_add_apply,
      measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  rw [hklw, hkl₀, hkl₁, haw_mass] at hkl_conv
  have hmul := mul_le_mul_of_nonneg_left hkl_conv hε0.le
  have hring : (ε : ℝ) * (-(∫ x, pw x ∂μw) / ε +
      (w₀ * a₀.real univ + w₁ * a₁.real univ) - 1) =
      -(∫ x, pw x ∂μw) + ε * (w₀ * a₀.real univ + w₁ * a₁.real univ - (w₀ + w₁)) := by
    rw [htw_sum]
    field_simp
    ring
  have hring' : (ε : ℝ) * (w₀ * (-(∫ x, p₀ x ∂μ₀) / ε + a₀.real univ - 1) +
      w₁ * (-(∫ x, p₁ x ∂μ₁) / ε + a₁.real univ - 1)) =
      w₀ * (-∫ x, p₀ x ∂μ₀) + w₁ * (-∫ x, p₁ x ∂μ₁) +
        ε * (w₀ * a₀.real univ + w₁ * a₁.real univ - (w₀ + w₁)) := by
    field_simp
    ring
  linarith

/-- Hilbert-space unit-sphere identity for the kernel mean embeddings of `a₀`, `a₁`, and
`aw = w₀ • a₀ + w₁ • a₁`. -/
private theorem integral_entropicGibbsKernel_smul_add_smul_sub_one [OpensMeasurableSpace X]
    {a₀ a₁ aw : Measure X} [IsFiniteMeasure a₀] [IsFiniteMeasure a₁] [IsFiniteMeasure aw]
    {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) (haw : aw = w₀ • a₀ + w₁ • a₁)
    (hE₀ : ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂a₀ ∂a₀ = 1)
    (hE₁ : ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂a₁ ∂a₁ = 1) :
    ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂aw ∂aw - 1 =
      -((w₀ : ℝ) * w₁ * ‖hk.kernelMeanEmbedding a₀ - hk.kernelMeanEmbedding a₁‖ ^ 2) := by
  have htw_sum : (w₀ : ℝ) + w₁ = 1 := by exact_mod_cast hw
  have hi₀ := hk.integrable_kolmogorovFeature hkc a₀
  have hi₁ := hk.integrable_kolmogorovFeature hkc a₁
  have hiw := hk.integrable_kolmogorovFeature hkc aw
  have hu₀ : ‖hk.kernelMeanEmbedding a₀‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hk.inner_kernelMeanEmbedding hi₀ hi₀, hE₀]
  have hu₁ : ‖hk.kernelMeanEmbedding a₁‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hk.inner_kernelMeanEmbedding hi₁ hi₁, hE₁]
  have hmaw : hk.kernelMeanEmbedding aw =
      (w₀ : ℝ) • hk.kernelMeanEmbedding a₀ + (w₁ : ℝ) • hk.kernelMeanEmbedding a₁ := by
    rw [haw, hk.kernelMeanEmbedding_add_measure (hk.integrable_kolmogorovFeature hkc _)
      (hk.integrable_kolmogorovFeature hkc _), ← Measure.coe_nnreal_smul,
      ← Measure.coe_nnreal_smul, hk.kernelMeanEmbedding_smul_measure,
      hk.kernelMeanEmbedding_smul_measure, ENNReal.coe_toReal, ENNReal.coe_toReal]
  rw [← hk.inner_kernelMeanEmbedding hiw hiw, real_inner_self_eq_norm_sq, hmaw]
  calc ‖(w₀ : ℝ) • hk.kernelMeanEmbedding a₀ +
          (w₁ : ℝ) • hk.kernelMeanEmbedding a₁‖ ^ 2 - 1
      = ((w₀ : ℝ) + w₁) ^ 2 - 1 - (w₀ : ℝ) * w₁ *
          (1 - 2 * ⟪hk.kernelMeanEmbedding a₀, hk.kernelMeanEmbedding a₁⟫_ℝ + 1) := by
        rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
          Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, hu₀, hu₁]
        ring
    _ = -((w₀ : ℝ) * w₁ * ‖hk.kernelMeanEmbedding a₀ - hk.kernelMeanEmbedding a₁‖ ^ 2) := by
        rw [htw_sum, one_pow, sub_self, zero_sub, norm_sub_sq_real, hu₀, hu₁]

/-- **Quantitative RKHS strong-convexity bound for the Sinkhorn negentropy.** Along a convex
combination `w₀ • μ₀ + w₁ • μ₁` of probability measures, the Sinkhorn negentropy drops below the
convex combination of negentropies by at least `(ε / 2) * w₀ * w₁` times the squared RKHS distance
of the tilted self-potential measures. -/
private theorem exists_sq_norm_add_sinkhornNegentropy_smul_add_smul_le [OpensMeasurableSpace X]
    {μ₀ μ₁ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {w₀ w₁ : ℝ≥0}
    (hw : w₀ + w₁ = 1) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    ∃ (p₀ p₁ : X → ℝ) (C₀ C₁ : ℝ), Measurable p₀ ∧ Measurable p₁ ∧
      (∀ x, |p₀ x| ≤ C₀) ∧ (∀ x, |p₁ x| ≤ C₁) ∧
      μ₀ = (tilt μ₀ ε p₀).withDensity (fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ₀ ε p₀) ∧
      μ₁ = (tilt μ₁ ε p₁).withDensity (fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ₁ ε p₁) ∧
      sinkhornNegentropy c ε (w₀ • μ₀ + w₁ • μ₁) +
        (ε : ℝ) / 2 * w₀ * w₁ *
          ‖hk.kernelMeanEmbedding (tilt μ₀ ε p₀) -
            hk.kernelMeanEmbedding (tilt μ₁ ε p₁)‖ ^ 2 ≤
        w₀ * sinkhornNegentropy c ε μ₀ + w₁ * sinkhornNegentropy c ε μ₁ := by
  have hcs := comp_swap_eq_of_posSemidef hcB hε hk
  obtain ⟨p₀, C₀, hp₀, hp₀C, hval₀, hE₀, hμ₀⟩ := exists_selfPotential (μ := μ₀) hc hcB hcs hε
  obtain ⟨p₁, C₁, hp₁, hp₁C, hval₁, hE₁, hμ₁⟩ := exists_selfPotential (μ := μ₁) hc hcB hcs hε
  obtain ⟨pw, Cw, hpw, hpwC, htilt_w⟩ :=
    exists_tilt_eq_smul_add_smul μ₀ μ₁ hw hε hp₀ hp₁ hp₀C hp₁C
  set μw : Measure X := w₀ • μ₀ + w₁ • μ₁
  have : IsProbabilityMeasure μw := ⟨by simp [μw, ← ENNReal.coe_add, hw]⟩
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀C
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁C
  have := isFiniteMeasure_tilt (μ := μw) (ε := ε) hpw hpwC
  have hint_pw_le := neg_integral_le_of_tilt_eq_smul_add_smul hw hε hp₀ hp₁ hpw hp₀C hp₁C hpwC
    htilt_w
  have hexp_w := integrable_entropicGibbsFactor_of_le (μ := μw) (ν := μw) (ε := ε) hc hpw hpw
    (fun x ↦ le_of_abs_le (hpwC x)) (fun x ↦ le_of_abs_le (hpwC x))
  have hpwi : Integrable pw μw := .of_bound hpw.aestronglyMeasurable Cw (ae_of_all _ hpwC)
  have hdual_w := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε hpwi hpwi hexp_w
  rw [entropicDualValue_def, kantorovichDualValue_def, integral_sub hexp_w (integrable_const _),
    integral_entropicGibbsFactor_eq hpw hpw hexp_w] at hdual_w
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hdual_w
  have hEw := integral_entropicGibbsKernel_smul_add_smul_sub_one hw hk hkc htilt_w hE₀ hE₁
  refine ⟨p₀, p₁, C₀, C₁, hp₀, hp₁, hp₀C, hp₁C, hμ₀, hμ₁, ?_⟩
  rw [sinkhornNegentropy_def, sinkhornNegentropy_def, sinkhornNegentropy_def, hval₀, hval₁]
  rw [hEw] at hdual_w
  linarith

/-- **Convexity of the Sinkhorn negentropy (Feydy et al., Theorem 1 and Proposition 3).** On a
compact space, for a bounded measurable cost whose Gibbs kernel `exp (-c / ε)` is continuous and
positive definite, and a positive temperature `ε`, the Sinkhorn negentropy `-OT_ε(μ, μ) / 2` is
convex on probability measures. -/
theorem sinkhornNegentropy_smul_add_smul_le [OpensMeasurableSpace X] {μ₀ μ₁ : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1)
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    sinkhornNegentropy c ε (w₀ • μ₀ + w₁ • μ₁) ≤
      w₀ * sinkhornNegentropy c ε μ₀ + w₁ * sinkhornNegentropy c ε μ₁ := by
  obtain ⟨p₀, p₁, -, -, -, -, -, -, -, -, h⟩ :=
    exists_sq_norm_add_sinkhornNegentropy_smul_add_smul_le hw hc hcB hε hk hkc (μ₀ := μ₀) (μ₁ := μ₁)
  have hnn : 0 ≤ (ε : ℝ) / 2 * w₀ * w₁ *
      ‖hk.kernelMeanEmbedding (tilt μ₀ ε p₀) - hk.kernelMeanEmbedding (tilt μ₁ ε p₁)‖ ^ 2 := by
    positivity
  linarith

/-- **Strict convexity of the Sinkhorn negentropy (Feydy et al., Theorem 1 and Proposition 3).**
On a compact Borel space with `HasOuterApproxClosed` (in particular a compact metrizable space),
when the Gibbs kernel `exp (-c / ε)` is continuous, positive definite, and universal, the Sinkhorn
negentropy is strictly convex on probability measures. -/
theorem sinkhornNegentropy_smul_add_smul_lt [BorelSpace X] [HasOuterApproxClosed X]
    {μ₀ μ₁ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {w₀ w₁ : ℝ≥0}
    (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (hw : w₀ + w₁ = 1) (hne : μ₀ ≠ μ₁)
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornNegentropy c ε (w₀ • μ₀ + w₁ • μ₁) <
      w₀ * sinkhornNegentropy c ε μ₀ + w₁ * sinkhornNegentropy c ε μ₁ := by
  obtain ⟨p₀, p₁, C₀, C₁, hp₀, hp₁, hp₀C, hp₁C, hμ₀, hμ₁, h⟩ :=
    exists_sq_norm_add_sinkhornNegentropy_smul_add_smul_le hw hc hcB hε hk hkc (μ₀ := μ₀) (μ₁ := μ₁)
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀C
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁C
  have hsub_ne : hk.kernelMeanEmbedding (tilt μ₀ ε p₀) -
      hk.kernelMeanEmbedding (tilt μ₁ ε p₁) ≠ 0 := by
    intro h0
    have htilt : tilt μ₀ ε p₀ = tilt μ₁ ε p₁ :=
      (hk.kernelMeanEmbedding_inj hkc hku).1 (sub_eq_zero.1 h0)
    exact hne (by rw [hμ₀, hμ₁, htilt])
  have hgap : 0 < (ε : ℝ) / 2 * w₀ * w₁ *
      ‖hk.kernelMeanEmbedding (tilt μ₀ ε p₀) - hk.kernelMeanEmbedding (tilt μ₁ ε p₁)‖ ^ 2 := by
    have := norm_pos_iff.2 hsub_ne
    positivity
  linarith

omit [TopologicalSpace X] [CompactSpace X] in
private theorem toReal_entropicTransportCost_smul_add_smul_left_le {μ₀ μ₁ : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν]
    {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1) (hcB : ∀ z, c z ≤ B) :
    (entropicTransportCost c ε (w₀ • μ₀ + w₁ • μ₁) ν).toReal ≤
      w₀ * (entropicTransportCost c ε μ₀ ν).toReal +
        w₁ * (entropicTransportCost c ε μ₁ ν).toReal := by
  have hf₀ : (w₀ : ℝ≥0∞) * entropicTransportCost c ε μ₀ ν ≠ ∞ := ENNReal.mul_ne_top
    ENNReal.coe_ne_top (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)
  have hf₁ : (w₁ : ℝ≥0∞) * entropicTransportCost c ε μ₁ ν ≠ ∞ := ENNReal.mul_ne_top
    ENNReal.coe_ne_top (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε)
  have hto := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf₀, hf₁⟩)
    (entropicTransportCost_smul_add_smul_left_le (c := c) (ε := ε) (μ₁ := μ₀) (μ₂ := μ₁)
      (ν := ν) hw)
  rwa [ENNReal.toReal_add hf₀ hf₁, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.coe_toReal] at hto

/-- **Convexity of the Sinkhorn divergence in its first argument (Feydy et al., Theorem 1).** -/
theorem sinkhornDivergence_smul_add_smul_left_le [OpensMeasurableSpace X]
    {μ₀ μ₁ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure ν] {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1) (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    sinkhornDivergence c ε (w₀ • μ₀ + w₁ • μ₁) ν ≤
      w₀ * sinkhornDivergence c ε μ₀ ν + w₁ * sinkhornDivergence c ε μ₁ ν := by
  have htw_sum : (w₀ : ℝ) + w₁ = 1 := by exact_mod_cast hw
  have hot := toReal_entropicTransportCost_smul_add_smul_left_le (c := c) (ε := ε)
    (μ₀ := μ₀) (μ₁ := μ₁) (ν := ν) hw hcB
  have hneg := sinkhornNegentropy_smul_add_smul_le (μ₀ := μ₀) (μ₁ := μ₁) hw hc hcB hε hk hkc
  rw [sinkhornDivergence_eq_add_sinkhornNegentropy, sinkhornDivergence_eq_add_sinkhornNegentropy,
    sinkhornDivergence_eq_add_sinkhornNegentropy]
  have hν_eq : sinkhornNegentropy c ε ν = ((w₀ : ℝ) + w₁) * sinkhornNegentropy c ε ν := by
    rw [htw_sum, one_mul]
  linarith

/-- **Convexity of the Sinkhorn divergence in its second argument (Feydy et al., Theorem 1).** -/
theorem sinkhornDivergence_smul_add_smul_right_le [OpensMeasurableSpace X]
    [IsProbabilityMeasure μ] {ν₀ ν₁ : Measure X} [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] {w₀ w₁ : ℝ≥0} (hw : w₀ + w₁ = 1) (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    sinkhornDivergence c ε μ (w₀ • ν₀ + w₁ • ν₁) ≤
      w₀ * sinkhornDivergence c ε μ ν₀ + w₁ * sinkhornDivergence c ε μ ν₁ := by
  rw [sinkhornDivergence_comm_of_posSemidef hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₀) hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₁) hcB hε hk]
  exact sinkhornDivergence_smul_add_smul_left_le hw hc hcB hε hk hkc

/-- **Strict convexity of the Sinkhorn divergence in its first argument
(Feydy et al., Theorem 1).** -/
theorem sinkhornDivergence_smul_add_smul_left_lt [BorelSpace X] [HasOuterApproxClosed X]
    {μ₀ μ₁ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure ν] {w₀ w₁ : ℝ≥0} (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (hw : w₀ + w₁ = 1)
    (hne : μ₀ ≠ μ₁) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε (w₀ • μ₀ + w₁ • μ₁) ν <
      w₀ * sinkhornDivergence c ε μ₀ ν + w₁ * sinkhornDivergence c ε μ₁ ν := by
  have htw_sum : (w₀ : ℝ) + w₁ = 1 := by exact_mod_cast hw
  have hot := toReal_entropicTransportCost_smul_add_smul_left_le (c := c) (ε := ε)
    (μ₀ := μ₀) (μ₁ := μ₁) (ν := ν) hw hcB
  have hneg := sinkhornNegentropy_smul_add_smul_lt (μ₀ := μ₀) (μ₁ := μ₁) hw₀ hw₁ hw hne hc hcB hε
    hk hkc hku
  rw [sinkhornDivergence_eq_add_sinkhornNegentropy, sinkhornDivergence_eq_add_sinkhornNegentropy,
    sinkhornDivergence_eq_add_sinkhornNegentropy]
  have hν_eq : sinkhornNegentropy c ε ν = ((w₀ : ℝ) + w₁) * sinkhornNegentropy c ε ν := by
    rw [htw_sum, one_mul]
  linarith

/-- **Strict convexity of the Sinkhorn divergence in its second argument
(Feydy et al., Theorem 1).** -/
theorem sinkhornDivergence_smul_add_smul_right_lt [BorelSpace X] [HasOuterApproxClosed X]
    [IsProbabilityMeasure μ] {ν₀ ν₁ : Measure X} [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] {w₀ w₁ : ℝ≥0} (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (hw : w₀ + w₁ = 1)
    (hne : ν₀ ≠ ν₁) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε μ (w₀ • ν₀ + w₁ • ν₁) <
      w₀ * sinkhornDivergence c ε μ ν₀ + w₁ * sinkhornDivergence c ε μ ν₁ := by
  rw [sinkhornDivergence_comm_of_posSemidef hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₀) hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₁) hcB hε hk]
  exact sinkhornDivergence_smul_add_smul_left_lt hw₀ hw₁ hw hne hc hcB hε hk hkc hku

/-! ### Quantitative stability, weak continuity, and metrization of weak convergence -/

omit [TopologicalSpace X] [CompactSpace X] in
private theorem abs_sinkhornDivergence_sub_le {X : Type*} [MeasurableSpace X] {c : X × X → ℝ≥0∞}
    {ε : ℝ≥0} (μ μ' ν ν' : Measure X) :
    |sinkhornDivergence c ε μ' ν' - sinkhornDivergence c ε μ ν| ≤
      |(entropicTransportCost c ε μ' ν').toReal - (entropicTransportCost c ε μ ν).toReal| +
      |(entropicTransportCost c ε μ' μ').toReal - (entropicTransportCost c ε μ μ).toReal| / 2 +
      |(entropicTransportCost c ε ν' ν').toReal - (entropicTransportCost c ε ν ν).toReal| / 2 := by
  have hdecomp : sinkhornDivergence c ε μ' ν' - sinkhornDivergence c ε μ ν =
      ((entropicTransportCost c ε μ' ν').toReal - (entropicTransportCost c ε μ ν).toReal) -
      ((entropicTransportCost c ε μ' μ').toReal - (entropicTransportCost c ε μ μ).toReal) / 2 -
      ((entropicTransportCost c ε ν' ν').toReal - (entropicTransportCost c ε ν ν).toReal) / 2 := by
    rw [sinkhornDivergence_def, sinkhornDivergence_def]
    ring
  rw [hdecomp]
  have h₁ := abs_sub (((entropicTransportCost c ε μ' ν').toReal -
      (entropicTransportCost c ε μ ν).toReal) -
      ((entropicTransportCost c ε μ' μ').toReal - (entropicTransportCost c ε μ μ).toReal) / 2)
    (((entropicTransportCost c ε ν' ν').toReal - (entropicTransportCost c ε ν ν).toReal) / 2)
  have h₂ := abs_sub ((entropicTransportCost c ε μ' ν').toReal -
      (entropicTransportCost c ε μ ν).toReal)
    (((entropicTransportCost c ε μ' μ').toReal - (entropicTransportCost c ε μ μ).toReal) / 2)
  have hdiv (r : ℝ) : |r / 2| = |r| / 2 := by rw [abs_div, abs_of_pos (zero_lt_two' ℝ)]
  rw [hdiv] at h₁ h₂
  linarith

omit [TopologicalSpace X] [CompactSpace X] in
/-- **`W₁`-Lipschitz stability of the Sinkhorn divergence, in `ℝ≥0∞`
(Feydy et al., Proposition 2).** On an extended pseudometric space, for a measurable cost bounded
by `B` whose slices are `K`-Lipschitz in each argument and a positive temperature `ε`, the Sinkhorn
divergence is `2 * K`-Lipschitz in each marginal with respect to `wassersteinEDist 1`, uniformly in
`ε` and `B`. -/
theorem ofReal_abs_sinkhornDivergence_sub_le_wassersteinEDist_one {X : Type*}
    [PseudoEMetricSpace X] [MeasurableSpace X] {c : X × X → ℝ≥0∞} {ε B K : ℝ≥0}
    {μ μ' ν ν' : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    ENNReal.ofReal |sinkhornDivergence c ε μ' ν' - sinkhornDivergence c ε μ ν| ≤
      (2 * K : ℝ≥0) * wassersteinEDist 1 μ' μ + (2 * K : ℝ≥0) * wassersteinEDist 1 ν' ν := by
  have hb_cross := ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one
    (μ := μ) (μ' := μ') (ν := ν) (ν' := ν') hc hcB hL₁ hL₂ hε
  have hb_μ := ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one
    (μ := μ) (μ' := μ') (ν := μ) (ν' := μ') hc hcB hL₁ hL₂ hε
  have hb_ν := ofReal_abs_toReal_entropicTransportCost_sub_le_wassersteinEDist_one
    (μ := ν) (μ' := ν') (ν := ν) (ν' := ν') hc hcB hL₁ hL₂ hε
  have hhalf {t : ℝ} {w : ℝ≥0∞} (h : ENNReal.ofReal t ≤ K * w + K * w) :
      ENNReal.ofReal (t / 2) ≤ K * w := by
    rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
    refine (ENNReal.div_le_div_right h 2).trans_eq ?_
    rw [← mul_two, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]
  have hb_μ' := hhalf hb_μ
  have hb_ν' := hhalf hb_ν
  calc ENNReal.ofReal |sinkhornDivergence c ε μ' ν' - sinkhornDivergence c ε μ ν|
      ≤ ENNReal.ofReal (|(entropicTransportCost c ε μ' ν').toReal -
          (entropicTransportCost c ε μ ν).toReal| +
          |(entropicTransportCost c ε μ' μ').toReal -
            (entropicTransportCost c ε μ μ).toReal| / 2 +
          |(entropicTransportCost c ε ν' ν').toReal -
            (entropicTransportCost c ε ν ν).toReal| / 2) :=
        ENNReal.ofReal_le_ofReal (abs_sinkhornDivergence_sub_le μ μ' ν ν')
    _ ≤ ENNReal.ofReal |(entropicTransportCost c ε μ' ν').toReal -
          (entropicTransportCost c ε μ ν).toReal| +
        ENNReal.ofReal (|(entropicTransportCost c ε μ' μ').toReal -
          (entropicTransportCost c ε μ μ).toReal| / 2) +
        ENNReal.ofReal (|(entropicTransportCost c ε ν' ν').toReal -
          (entropicTransportCost c ε ν ν).toReal| / 2) :=
        ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ ≤ (K * wassersteinEDist 1 μ' μ + K * wassersteinEDist 1 ν' ν) +
          K * wassersteinEDist 1 μ' μ + K * wassersteinEDist 1 ν' ν := by
        gcongr
    _ = (2 * K : ℝ≥0) * wassersteinEDist 1 μ' μ + (2 * K : ℝ≥0) * wassersteinEDist 1 ν' ν := by
        push_cast
        ring

omit [TopologicalSpace X] [CompactSpace X] in
/-- **`W₁`-Lipschitz stability of the Sinkhorn divergence, in real form
(Feydy et al., Proposition 2).** -/
theorem abs_sinkhornDivergence_sub_le_wassersteinEDist_one {X : Type*}
    [PseudoEMetricSpace X] [MeasurableSpace X] {c : X × X → ℝ≥0∞} {ε B K : ℝ≥0}
    {μ μ' ν ν' : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0)
    (hw₁ : wassersteinEDist 1 μ' μ ≠ ∞) (hw₂ : wassersteinEDist 1 ν' ν ≠ ∞) :
    |sinkhornDivergence c ε μ' ν' - sinkhornDivergence c ε μ ν| ≤
      2 * K * (wassersteinEDist 1 μ' μ).toReal + 2 * K * (wassersteinEDist 1 ν' ν).toReal := by
  have h₁ : ((2 * K : ℝ≥0) : ℝ≥0∞) * wassersteinEDist 1 μ' μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hw₁
  have h₂ : ((2 * K : ℝ≥0) : ℝ≥0∞) * wassersteinEDist 1 ν' ν ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hw₂
  have h := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.2 ⟨h₁, h₂⟩)).1
    (ofReal_abs_sinkhornDivergence_sub_le_wassersteinEDist_one hc hcB hL₁ hL₂ hε)
  rwa [ENNReal.toReal_add h₁ h₂, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    NNReal.coe_mul, NNReal.coe_ofNat] at h

omit [CompactSpace X] in
private theorem continuous_sinkhornDivergence_of_continuous_toReal [OpensMeasurableSpace X]
    (hcont : Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      (entropicTransportCost c ε q.1.toMeasure q.2.toMeasure).toReal) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      sinkhornDivergence c ε q.1.toMeasure q.2.toMeasure := by
  have h₁ : Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      (entropicTransportCost c ε q.1.toMeasure q.1.toMeasure).toReal :=
    hcont.comp (continuous_fst.prodMk continuous_fst)
  have h₂ : Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      (entropicTransportCost c ε q.2.toMeasure q.2.toMeasure).toReal :=
    hcont.comp (continuous_snd.prodMk continuous_snd)
  simp only [sinkhornDivergence_def]
  exact continuous_iff_continuousAt.2 fun q ↦
    ((hcont.tendsto q).sub ((h₁.tendsto q).div_const 2)).sub ((h₂.tendsto q).div_const 2)

omit [TopologicalSpace X] [CompactSpace X] in
/-- **Joint weak continuity of the Sinkhorn divergence for bounded slicewise-Lipschitz costs.** On a
separable pseudometric space whose open sets are measurable (for instance any Polish metric space
with its Borel σ-algebra), for a measurable cost bounded by `B` with `K₁`- and `K₂`-Lipschitz
slices and a positive temperature `ε`, the Sinkhorn divergence is jointly continuous on
`ProbabilityMeasure X × ProbabilityMeasure X`, with no compactness or moment assumption. -/
theorem continuous_sinkhornDivergence_of_lipschitzWith {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {c : X × X → ℝ≥0∞} {ε B K₁ K₂ : ℝ≥0} (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hL₁ : ∀ y, LipschitzWith K₁ fun x ↦ (c (x, y)).toReal)
    (hL₂ : ∀ x, LipschitzWith K₂ fun y ↦ (c (x, y)).toReal) (hε : ε ≠ 0) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      sinkhornDivergence c ε q.1.toMeasure q.2.toMeasure :=
  continuous_sinkhornDivergence_of_continuous_toReal
    (continuous_toReal_entropicTransportCost_of_lipschitzWith hc hcB hL₁ hL₂ hε)

/-- **Joint weak continuity of the Sinkhorn divergence on compact pseudometrizable spaces.** -/
theorem continuous_sinkhornDivergence [TopologicalSpace.PseudoMetrizableSpace X]
    [OpensMeasurableSpace X] (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) :
    Continuous fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      sinkhornDivergence c ε q.1.toMeasure q.2.toMeasure :=
  continuous_sinkhornDivergence_of_continuous_toReal
    (continuous_toReal_entropicTransportCost hc hfin hε)

/-- **Sinkhorn divergences metrise weak convergence on compact metrizable spaces
(Feydy et al., Theorem 1).** For a compact metrizable space `X` with its Borel σ-algebra, a
continuous finite-valued cost `c` whose Gibbs kernel `exp (-c / ε)` is positive definite and
universal, and a positive temperature `ε`, a family of probability measures `μs` converges weakly
to `μ` along a filter `l` if and only if `sinkhornDivergence c ε (μs i) μ` tends to `0` along
`l`. -/
theorem tendsto_sinkhornDivergence_zero_iff_tendsto [TopologicalSpace.MetrizableSpace X]
    [BorelSpace X] {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    Tendsto (fun i ↦ sinkhornDivergence c ε (μs i).toMeasure μ.toMeasure) l (𝓝 0) ↔
      Tendsto μs l (𝓝 μ) := by
  have hcont_f : Continuous fun ν : ProbabilityMeasure X ↦
      sinkhornDivergence c ε ν.toMeasure μ.toMeasure :=
    (continuous_sinkhornDivergence hc hfin hε).comp (continuous_id.prodMk continuous_const)
  refine ⟨fun hS ↦ ?_, fun hμs ↦ ?_⟩
  · have hfc : Continuous fun z : X × X ↦ (c z).toReal :=
      ENNReal.continuousOn_toReal.comp_continuous hc hfin
    obtain ⟨B₀, hB₀⟩ := (isCompact_range hfc).bddAbove
    set B : ℝ≥0 := Real.toNNReal B₀
    have hcB : ∀ z, c z ≤ B := fun z ↦ by
      rw [← ENNReal.ofReal_toReal (hfin z), ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal ((hB₀ (mem_range_self z)).trans (Real.le_coe_toNNReal B₀))
    have hkc := continuous_entropicGibbsKernel (ε := ε) hc hfin
    refine tendsto_nhds_of_unique_mapClusterPt fun ν hν ↦ ?_
    have hcl : ClusterPt (sinkhornDivergence c ε ν.toMeasure μ.toMeasure) (𝓝 0) :=
      (hν.continuousAt_comp hcont_f.continuousAt).clusterPt.mono hS
    have h0 : sinkhornDivergence c ε ν.toMeasure μ.toMeasure = 0 := eq_of_nhds_neBot hcl.neBot
    exact ProbabilityMeasure.toMeasure_injective
      ((sinkhornDivergence_eq_zero_iff hc.measurable hcB hε hk hkc hku).1 h0)
  · simpa only [Function.comp_def, sinkhornDivergence_self] using (hcont_f.tendsto μ).comp hμs

end TauCeti
