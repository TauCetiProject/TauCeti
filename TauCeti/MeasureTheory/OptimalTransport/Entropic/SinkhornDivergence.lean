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
import TauCeti.Analysis.InnerProductSpace.CompleteSquare

/-!
# Sinkhorn divergences

The entropic transport cost `OT_ε(μ, ν) = TauCeti.entropicTransportCost c ε μ ν` is biased: in
general `OT_ε(μ, μ) ≠ 0`. Introducing the *Sinkhorn negentropy*
`H_ε(μ) = -(OT_ε(μ, μ)).toReal / 2` (`TauCeti.sinkhornNegentropy`), the *Sinkhorn divergence*

`S_ε(μ, ν) = OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2 = OT_ε(μ, ν) + H_ε(μ) + H_ε(ν)`

removes this bias, so that `S_ε(μ, μ) = 0`. This file defines `sinkhornDivergence` and
`sinkhornNegentropy` and establishes the structural properties of Feydy--Séjourné--Vialard--Amari--
Trouvé--Peyré, Theorem 1 and Proposition 2:

1. **Nonnegativity and definiteness.** When the Gibbs kernel `k(x, y) = exp (-c(x, y) / ε)` is
   continuous and positive definite on a compact space, evaluating weak duality of `OT_ε(μ, ν)` at
   the symmetric self-potentials `p` of `μ` and `q` of `ν` bounds `S_ε(μ, ν)` below by
   `(ε / 2) * ‖m(e^{p/ε} μ) - m(e^{q/ε} ν)‖ ^ 2`, where `m` is the kernel mean embedding
   (`Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`). If moreover `k` is universal on a Borel
   space with `HasOuterApproxClosed`, injectivity of `m`
   (`Matrix.PosSemidef.kernelMeanEmbedding_inj`) and the marginal recovery formula
   `μ = (∫ k(·, y) da(y)) • a` force `S_ε(μ, ν) = 0 ↔ μ = ν`.
2. **Convexity of Sinkhorn negentropy and separate strict convexity of Sinkhorn divergence.**
   While `μ ↦ OT_ε(μ, μ)` is concave rather than convex in general, when `k` is continuous and
   positive definite the Sinkhorn negentropy `H_ε(μ) = -(OT_ε(μ, μ)).toReal / 2` is convex on
   probability measures: tilting a convex combination `μ = a • μ₀ + b • μ₁` by the logarithmic
   density-weighted mean potential interpolates the tilted measures `a • ρ₀ + b • ρ₁` linearly,
   and completing the square in the Kolmogorov Hilbert space leaves a quantitative quadratic gap
   `(ε / 2) * a * b * ‖m ρ₀ - m ρ₁‖ ^ 2`. Combining this with separate convexity of `OT_ε` makes
   `S_ε` separately convex in each marginal, and strictly so when `k` is universal.
3. **Weak continuity and metrization of weak convergence.** Inheriting joint weak continuity from
   `OT_ε` (`TauCeti.continuous_toReal_entropicTransportCost`), on a compact Hausdorff Borel space
   with `HasOuterApproxClosed` and a continuous finite cost whose Gibbs kernel is positive definite
   and universal, `S_ε(μs i, μ) → 0` is equivalent to weak convergence `μs i → μ` in
   `ProbabilityMeasure X` (`TauCeti.tendsto_sinkhornDivergence_zero_iff_tendsto`).

The Sinkhorn divergence is real-valued, through `ENNReal.toReal` of the three entropic costs. It
is the intended value when these are finite, as they are for the bounded costs considered here.

## Main definitions

* `TauCeti.sinkhornDivergence c ε μ ν`: the debiased entropic transport cost
  `OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2`.
* `TauCeti.sinkhornNegentropy c ε μ`: the Sinkhorn negentropy `-(OT_ε(μ, μ)).toReal / 2`.

## Main statements

* `TauCeti.sinkhornDivergence_self`, `TauCeti.sinkhornDivergence_const`,
  `TauCeti.sinkhornDivergence_comp_swap`, `TauCeti.sinkhornDivergence_comm`, and
  `TauCeti.sinkhornDivergence_dirac_dirac`: diagonal vanishing, invariance under constant costs,
  marginal symmetry, and evaluation on Dirac masses.
* `TauCeti.sinkhornDivergence_nonneg` and `TauCeti.sinkhornDivergence_eq_zero_iff`: nonnegativity
  and definiteness under a positive-definite (and universal) Gibbs kernel.
* `TauCeti.sinkhornNegentropy_smul_add_smul_le` and
  `TauCeti.sinkhornNegentropy_smul_add_smul_lt`: convexity and strict convexity of Sinkhorn
  negentropy.
* `TauCeti.sinkhornDivergence_smul_add_smul_left_le`,
  `TauCeti.sinkhornDivergence_smul_add_smul_right_le`,
  `TauCeti.sinkhornDivergence_smul_add_smul_left_lt`, and
  `TauCeti.sinkhornDivergence_smul_add_smul_right_lt`: separate convexity and strict separate
  convexity of `sinkhornDivergence` in each marginal.
* `TauCeti.continuous_sinkhornNegentropy`, `TauCeti.continuous_sinkhornDivergence`, and
  `TauCeti.tendsto_sinkhornDivergence_zero_iff_tendsto`: weak continuity and weak-convergence
  metrization on compact spaces.

For a continuous bounded cost the continuity hypothesis on the Gibbs kernel is supplied by
`TauCeti.continuous_entropicGibbsKernel`.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Proposition 2, Theorem 1, and their proofs in the supplementary material.
-/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section Basic

variable {X : Type*} [MeasurableSpace X] {c : X × X → ℝ≥0∞} {ε B : ℝ≥0} {μ ν : Measure X}

/-! ### Definitions and basic identities -/

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

/-- The *Sinkhorn negentropy* `-(OT_ε(μ, μ)).toReal / 2`, the debiasing self-interaction term in
`TauCeti.sinkhornDivergence`. When the Gibbs kernel `exp (-c / ε)` is continuous and positive
definite on a compact space, `sinkhornNegentropy c ε` is convex on probability measures. -/
def sinkhornNegentropy (c : X × X → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) : ℝ :=
  -(entropicTransportCost c ε μ μ).toReal / 2

/-- The Sinkhorn negentropy is minus half of the real-valued entropic self-transport cost. -/
theorem sinkhornNegentropy_def :
    sinkhornNegentropy c ε μ = -(entropicTransportCost c ε μ μ).toReal / 2 :=
  (rfl)

/-- Decomposition of the Sinkhorn divergence into the entropic transport cost plus the two
Sinkhorn negentropies. -/
theorem sinkhornDivergence_eq_add_sinkhornNegentropy :
    sinkhornDivergence c ε μ ν =
      (entropicTransportCost c ε μ ν).toReal +
        sinkhornNegentropy c ε μ + sinkhornNegentropy c ε ν := by
  rw [sinkhornDivergence_def, sinkhornNegentropy_def, sinkhornNegentropy_def]
  ring

/-- The Sinkhorn divergence vanishes on the diagonal. -/
@[simp]
theorem sinkhornDivergence_self (c : X × X → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) :
    sinkhornDivergence c ε μ μ = 0 := by
  rw [sinkhornDivergence_def]
  ring

/-- For a constant cost `a`, the Sinkhorn negentropy of a probability measure is `-a.toReal / 2`. -/
@[simp]
theorem sinkhornNegentropy_const [IsProbabilityMeasure μ] (a : ℝ≥0∞) (ε : ℝ≥0) :
    sinkhornNegentropy (fun _ ↦ a) ε μ = -a.toReal / 2 := by
  rw [sinkhornNegentropy_def, entropicTransportCost_const]

/-- For a constant cost, the Sinkhorn divergence between two probability measures vanishes. -/
@[simp]
theorem sinkhornDivergence_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : ℝ≥0∞)
    (ε : ℝ≥0) : sinkhornDivergence (fun _ ↦ a) ε μ ν = 0 := by
  rw [sinkhornDivergence_def, entropicTransportCost_const, entropicTransportCost_const,
    entropicTransportCost_const]
  ring

/-- Exchanging the two arguments of the Sinkhorn divergence transports the cost along
`Prod.swap`. -/
theorem sinkhornDivergence_comp_swap [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : X × X → ℝ≥0∞)
    (ε : ℝ≥0) : sinkhornDivergence (c ∘ Prod.swap) ε ν μ = sinkhornDivergence c ε μ ν := by
  rw [sinkhornDivergence_def, sinkhornDivergence_def, entropicTransportCost_comp_swap c ε ν,
    entropicTransportCost_comp_swap c ε ν, entropicTransportCost_comp_swap c ε μ]
  ring

/-- For a symmetric cost, the Sinkhorn divergence of two finite measures is symmetric. -/
theorem sinkhornDivergence_comm [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hcs : c ∘ Prod.swap = c)
    (ε : ℝ≥0) : sinkhornDivergence c ε μ ν = sinkhornDivergence c ε ν μ := by
  rw [← sinkhornDivergence_comp_swap c ε, hcs]

/-- On a Dirac mass, the Sinkhorn negentropy of a measurable cost `c` is `-(c (x, x)).toReal / 2`,
independently of the regularisation parameter `ε`. -/
theorem sinkhornNegentropy_dirac (hc : Measurable c) (ε : ℝ≥0) (x : X) :
    sinkhornNegentropy c ε (Measure.dirac x) = -(c (x, x)).toReal / 2 := by
  rw [sinkhornNegentropy_def, entropicTransportCost_dirac_dirac hc]

/-- Between two Dirac masses, the Sinkhorn divergence of a measurable cost `c` is the debiased
ground cost `(c (x, y)).toReal - (c (x, x)).toReal / 2 - (c (y, y)).toReal / 2`, independently of
`ε`; in particular it equals `(c (x, y)).toReal` whenever `c` vanishes on the diagonal. -/
theorem sinkhornDivergence_dirac_dirac (hc : Measurable c) (ε : ℝ≥0) (x y : X) :
    sinkhornDivergence c ε (Measure.dirac x) (Measure.dirac y) =
      (c (x, y)).toReal - (c (x, x)).toReal / 2 - (c (y, y)).toReal / 2 := by
  rw [sinkhornDivergence_def, entropicTransportCost_dirac_dirac hc,
    entropicTransportCost_dirac_dirac hc, entropicTransportCost_dirac_dirac hc]

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

/-- When the Gibbs kernel of a bounded cost is positive definite at positive temperature, the
Sinkhorn divergence of two finite measures is symmetric without an explicit symmetry assumption on
`c`. -/
theorem sinkhornDivergence_comm_of_posSemidef [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε μ ν = sinkhornDivergence c ε ν μ :=
  sinkhornDivergence_comm (comp_swap_eq_of_posSemidef hcB hε hk) ε

end Basic

/-! ### Nonnegativity, definiteness, convexity, and weak-convergence metrization -/

section Compact

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
  {c : X × X → ℝ≥0∞} {ε B : ℝ≥0} {μ ν : Measure X}

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

/-- **Quantitative convexity of Sinkhorn negentropy.** Tilting `a • μ₀ + b • μ₁` by the
logarithmic Radon--Nikodym-weighted mean of the self-potentials `p₀` and `p₁` interpolates the
tilted measures `a • tilt μ₀ ε p₀ + b • tilt μ₁ ε p₁` linearly; weak duality and completing the
square in the Kolmogorov space then yield convexity of `sinkhornNegentropy` with explicit deficit
`(ε / 2) * a * b * ‖m(tilt μ₀ ε p₀) - m(tilt μ₁ ε p₁)‖ ^ 2`. -/
private theorem exists_sq_norm_sinkhornNegentropy_smul_add_smul_le [OpensMeasurableSpace X]
    {μ₀ μ₁ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {a b : ℝ≥0}
    (hab : a + b = 1) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    ∃ (p₀ p₁ : X → ℝ) (C₀ C₁ : ℝ), Measurable p₀ ∧ Measurable p₁ ∧
      (∀ x, |p₀ x| ≤ C₀) ∧ (∀ x, |p₁ x| ≤ C₁) ∧
      μ₀ = (tilt μ₀ ε p₀).withDensity (fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ₀ ε p₀) ∧
      μ₁ = (tilt μ₁ ε p₁).withDensity (fun x ↦
        ∫⁻ y, ENNReal.ofReal (entropicGibbsKernel c ε x y) ∂tilt μ₁ ε p₁) ∧
      sinkhornNegentropy c ε (a • μ₀ + b • μ₁) +
          ε / 2 * a * b *
            ‖hk.kernelMeanEmbedding (tilt μ₀ ε p₀) -
              hk.kernelMeanEmbedding (tilt μ₁ ε p₁)‖ ^ 2 ≤
        a * sinkhornNegentropy c ε μ₀ + b * sinkhornNegentropy c ε μ₁ := by
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
  have habR : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hcs := comp_swap_eq_of_posSemidef hcB hε hk
  obtain ⟨p₀, C₀, hp₀, hp₀C, hμ₀, hEp₀, hμ₀p⟩ := exists_selfPotential (μ := μ₀) hc hcB hcs hε
  obtain ⟨p₁, C₁, hp₁, hp₁C, hμ₁, hEp₁, hμ₁p⟩ := exists_selfPotential (μ := μ₁) hc hcB hcs hε
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀C
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁C
  set μm := a • μ₀ + b • μ₁
  have : IsProbabilityMeasure μm := ⟨by simp [μm, hab']⟩
  set lam := μ₀ + μ₁
  have h₀lam : μ₀ ≪ lam := Measure.AbsolutelyContinuous.rfl.add_right μ₁
  have h₁lam : μ₁ ≪ lam := Measure.AbsolutelyContinuous.rfl.add_right' μ₀
  let w₀ : X → ℝ := fun x ↦ (μ₀.rnDeriv lam x).toReal
  let w₁ : X → ℝ := fun x ↦ (μ₁.rnDeriv lam x).toReal
  have hw₀m : Measurable w₀ := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hw₁m : Measurable w₁ := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  let C : ℝ := max (max C₀ C₁) 0
  have hC₀ : ∀ x, |p₀ x| ≤ C := fun x ↦ (hp₀C x).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hC₁ : ∀ x, |p₁ x| ≤ C := fun x ↦ (hp₁C x).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hCnonneg : 0 ≤ C := le_max_right _ _
  let p : X → ℝ := fun x ↦ (ε : ℝ) * Real.log
    (((a : ℝ) * w₀ x * Real.exp (p₀ x / ε) + (b : ℝ) * w₁ x * Real.exp (p₁ x / ε)) /
      ((a : ℝ) * w₀ x + (b : ℝ) * w₁ x))
  have hpm : Measurable p := by fun_prop
  have hpC : ∀ x, |p x| ≤ C := fun x ↦ by
    set u := (a : ℝ) * w₀ x
    set v := (b : ℝ) * w₁ x
    have hu : 0 ≤ u := mul_nonneg a.coe_nonneg ENNReal.toReal_nonneg
    have hv : 0 ≤ v := mul_nonneg b.coe_nonneg ENNReal.toReal_nonneg
    change |(ε : ℝ) * Real.log ((u * Real.exp (p₀ x / ε) + v * Real.exp (p₁ x / ε)) / (u + v))| ≤ C
    rcases eq_or_lt_of_le (add_nonneg hu hv) with huv0 | huv_pos
    · rw [← huv0, div_zero, Real.log_zero, mul_zero, abs_zero]
      exact hCnonneg
    · set num := u * Real.exp (p₀ x / ε) + v * Real.exp (p₁ x / ε)
      have hnum_pos : 0 < num := by
        have he₀ : 0 < Real.exp (p₀ x / ε) := Real.exp_pos _
        have he₁ : 0 < Real.exp (p₁ x / ε) := Real.exp_pos _
        rcases eq_or_lt_of_le hu with hu0 | hu'
        · have hv' : 0 < v := by linarith
          exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos hv' he₁)
        · exact add_pos_of_pos_of_nonneg (mul_pos hu' he₀) (by positivity)
      have hle_u : num / (u + v) ≤ Real.exp (C / ε) := by
        rw [div_le_iff₀ huv_pos]
        have h0 : Real.exp (p₀ x / ε) ≤ Real.exp (C / ε) :=
          Real.exp_le_exp.2 (div_le_div_of_nonneg_right (le_of_abs_le (hC₀ x)) hεpos.le)
        have h1 : Real.exp (p₁ x / ε) ≤ Real.exp (C / ε) :=
          Real.exp_le_exp.2 (div_le_div_of_nonneg_right (le_of_abs_le (hC₁ x)) hεpos.le)
        calc num ≤ u * Real.exp (C / ε) + v * Real.exp (C / ε) :=
              add_le_add (mul_le_mul_of_nonneg_left h0 hu) (mul_le_mul_of_nonneg_left h1 hv)
          _ = Real.exp (C / ε) * (u + v) := by ring
      have hle_l : Real.exp (-C / ε) ≤ num / (u + v) := by
        rw [le_div_iff₀ huv_pos]
        have h0 : Real.exp (-C / ε) ≤ Real.exp (p₀ x / ε) :=
          Real.exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_of_abs_le (hC₀ x)) hεpos.le)
        have h1 : Real.exp (-C / ε) ≤ Real.exp (p₁ x / ε) :=
          Real.exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_of_abs_le (hC₁ x)) hεpos.le)
        calc Real.exp (-C / ε) * (u + v) = u * Real.exp (-C / ε) + v * Real.exp (-C / ε) := by ring
          _ ≤ num := add_le_add (mul_le_mul_of_nonneg_left h0 hu) (mul_le_mul_of_nonneg_left h1 hv)
      have hlog_u := (Real.log_le_log (div_pos hnum_pos huv_pos) hle_u).trans_eq (Real.log_exp _)
      have hlog_l := (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hle_l)
      rw [abs_le]
      constructor
      · have := mul_le_mul_of_nonneg_left hlog_l hεpos.le
        rw [neg_div, mul_neg, mul_div_cancel₀ _ hεpos.ne'] at this
        linarith
      · have := mul_le_mul_of_nonneg_left hlog_u hεpos.le
        rw [mul_div_cancel₀ _ hεpos.ne'] at this
        linarith
  have hpoint (x : X) :
      ((a : ℝ) * w₀ x + (b : ℝ) * w₁ x) * Real.exp (p x / ε) =
        (a : ℝ) * w₀ x * Real.exp (p₀ x / ε) + (b : ℝ) * w₁ x * Real.exp (p₁ x / ε) := by
    set u := (a : ℝ) * w₀ x
    set v := (b : ℝ) * w₁ x
    have hu : 0 ≤ u := mul_nonneg a.coe_nonneg ENNReal.toReal_nonneg
    have hv : 0 ≤ v := mul_nonneg b.coe_nonneg ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le (add_nonneg hu hv) with huv0 | huv_pos
    · have hu0 : u = 0 := by linarith
      have hv0 : v = 0 := by linarith
      simp [hu0, hv0]
    · set num := u * Real.exp (p₀ x / ε) + v * Real.exp (p₁ x / ε)
      have hnum_pos : 0 < num := by
        have he₀ : 0 < Real.exp (p₀ x / ε) := Real.exp_pos _
        have he₁ : 0 < Real.exp (p₁ x / ε) := Real.exp_pos _
        rcases eq_or_lt_of_le hu with hu0 | hu'
        · have hv' : 0 < v := by linarith
          exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos hv' he₁)
        · exact add_pos_of_pos_of_nonneg (mul_pos hu' he₀) (by positivity)
      have hpdiv : p x / ε = Real.log (num / (u + v)) :=
        mul_div_cancel_left₀ _ hεpos.ne'
      rw [hpdiv, Real.exp_log (div_pos hnum_pos huv_pos), mul_div_cancel₀ _ huv_pos.ne']
  have htilt_rn (ν' : Measure X) [IsFiniteMeasure ν'] (hν' : ν' ≪ lam) {q : X → ℝ}
      (hq : Measurable q) :
      tilt ν' ε q = lam.withDensity fun x ↦
        ENNReal.ofReal ((ν'.rnDeriv lam x).toReal * Real.exp (q x / ε)) := by
    conv_lhs =>
      rw [tilt, ← Measure.withDensity_rnDeriv_eq ν' lam hν',
        ← withDensity_mul lam (Measure.measurable_rnDeriv ν' lam) (measurable_tiltDensity hq)]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν' lam] with x hx
    conv_lhs =>
      rw [Pi.mul_apply, ← ENNReal.ofReal_toReal hx.ne,
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  have htilt_comb : tilt μm ε p = (a : ℝ≥0∞) • tilt μ₀ ε p₀ + (b : ℝ≥0∞) • tilt μ₁ ε p₁ := by
    have hlhs : tilt μm ε p = (a : ℝ≥0∞) • tilt μ₀ ε p + (b : ℝ≥0∞) • tilt μ₁ ε p := by
      simp only [μm, tilt, withDensity_add_measure, ← Measure.coe_nnreal_smul,
        withDensity_smul_measure]
    rw [hlhs, htilt_rn μ₀ h₀lam hpm, htilt_rn μ₁ h₁lam hpm,
      htilt_rn μ₀ h₀lam hp₀, htilt_rn μ₁ h₁lam hp₁,
      ← withDensity_smul _ (by fun_prop), ← withDensity_smul _ (by fun_prop),
      ← withDensity_smul _ (by fun_prop), ← withDensity_smul _ (by fun_prop),
      ← withDensity_add_left (by fun_prop), ← withDensity_add_left (by fun_prop)]
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    have : 0 ≤ w₀ x := ENNReal.toReal_nonneg
    have : 0 ≤ w₁ x := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_mul a.coe_nonneg, ← ENNReal.ofReal_mul b.coe_nonneg,
      ← ENNReal.ofReal_mul a.coe_nonneg, ← ENNReal.ofReal_mul b.coe_nonneg,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simpa only [w₀, w₁, add_mul, mul_assoc] using hpoint x
  have hint_le : (a : ℝ) * ∫ x, p₀ x ∂μ₀ + (b : ℝ) * ∫ x, p₁ x ∂μ₁ ≤ ∫ x, p x ∂μm := by
    have hp_μ₀ : Integrable p μ₀ := .of_bound hpm.aestronglyMeasurable C (ae_of_all _ hpC)
    have hp_μ₁ : Integrable p μ₁ := .of_bound hpm.aestronglyMeasurable C (ae_of_all _ hpC)
    have hp₀_μ₀ : Integrable p₀ μ₀ := .of_bound hp₀.aestronglyMeasurable C₀ (ae_of_all _ hp₀C)
    have hp₁_μ₁ : Integrable p₁ μ₁ := .of_bound hp₁.aestronglyMeasurable C₁ (ae_of_all _ hp₁C)
    have hrhs : ∫ x, p x ∂μm = (a : ℝ) * ∫ x, p x ∂μ₀ + (b : ℝ) * ∫ x, p x ∂μ₁ := by
      rw [show μm = (a : ℝ≥0∞) • μ₀ + (b : ℝ≥0∞) • μ₁ by
        simp [μm, Measure.coe_nnreal_smul],
        integral_add_measure (hp_μ₀.smul_measure ENNReal.coe_ne_top)
          (hp_μ₁.smul_measure ENNReal.coe_ne_top),
        integral_smul_measure, integral_smul_measure, ENNReal.coe_toReal, ENNReal.coe_toReal,
        smul_eq_mul, smul_eq_mul]
    rw [hrhs, ← integral_toReal_rnDeriv_mul h₀lam (f := p₀),
      ← integral_toReal_rnDeriv_mul h₁lam (f := p₁),
      ← integral_toReal_rnDeriv_mul h₀lam (f := p),
      ← integral_toReal_rnDeriv_mul h₁lam (f := p),
      ← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (((integrable_toReal_rnDeriv_mul_iff h₀lam).2 hp₀_μ₀).const_mul _)
        (((integrable_toReal_rnDeriv_mul_iff h₁lam).2 hp₁_μ₁).const_mul _),
      ← integral_add (((integrable_toReal_rnDeriv_mul_iff h₀lam).2 hp_μ₀).const_mul _)
        (((integrable_toReal_rnDeriv_mul_iff h₁lam).2 hp_μ₁).const_mul _)]
    refine integral_mono
      ((((integrable_toReal_rnDeriv_mul_iff h₀lam).2 hp₀_μ₀).const_mul _).add
        (((integrable_toReal_rnDeriv_mul_iff h₁lam).2 hp₁_μ₁).const_mul _))
      ((((integrable_toReal_rnDeriv_mul_iff h₀lam).2 hp_μ₀).const_mul _).add
        (((integrable_toReal_rnDeriv_mul_iff h₁lam).2 hp_μ₁).const_mul _))
      fun x ↦ ?_
    dsimp only
    set u := (a : ℝ) * w₀ x
    set v := (b : ℝ) * w₁ x
    have hu : 0 ≤ u := mul_nonneg a.coe_nonneg ENNReal.toReal_nonneg
    have hv : 0 ≤ v := mul_nonneg b.coe_nonneg ENNReal.toReal_nonneg
    have hpt_x : u * p₀ x + v * p₁ x ≤ u * p x + v * p x := by
      have hexp_id : u * Real.exp ((p₀ x - p x) / ε) + v * Real.exp ((p₁ x - p x) / ε) =
          u + v := by
        have hmul := congrArg (· * Real.exp (-(p x / ε))) (hpoint x).symm
        have hrw (r : ℝ) : Real.exp (r / ε) * Real.exp (-(p x / ε)) =
            Real.exp ((r - p x) / ε) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc u * Real.exp ((p₀ x - p x) / ε) + v * Real.exp ((p₁ x - p x) / ε)
            = (u * Real.exp (p₀ x / ε) + v * Real.exp (p₁ x / ε)) * Real.exp (-(p x / ε)) := by
              rw [← hrw (p₀ x), ← hrw (p₁ x)]
              ring
          _ = (u + v) * (Real.exp (p x / ε) * Real.exp (-(p x / ε))) := by
              rw [hmul, mul_assoc]
          _ = u + v := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have hlin₀ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((p₀ x - p x) / ε)) hu
      have hlin₁ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((p₁ x - p x) / ε)) hv
      have : u * ((p₀ x - p x) / ε + 1) + v * ((p₁ x - p x) / ε + 1) ≤ u + v :=
        (add_le_add hlin₀ hlin₁).trans_eq hexp_id
      have hdiv_nonpos : (u * (p₀ x - p x) + v * (p₁ x - p x)) / ε ≤ 0 := by
        have : u * ((p₀ x - p x) / ε + 1) + v * ((p₁ x - p x) / ε + 1) =
            (u + v) + (u * (p₀ x - p x) + v * (p₁ x - p x)) / ε := by ring
        linarith
      have := mul_nonpos_of_nonpos_of_nonneg hdiv_nonpos hεpos.le
      rw [div_mul_cancel₀ _ hεpos.ne'] at this
      linarith
    simpa only [u, v, mul_assoc] using hpt_x
  have := isFiniteMeasure_tilt (μ := μm) (ε := ε) hpm hpC
  have hexp_m := integrable_entropicGibbsFactor_of_le (μ := μm) (ν := μm) (ε := ε) hc hpm hpm
    (fun x ↦ le_of_abs_le (hpC x)) (fun x ↦ le_of_abs_le (hpC x))
  have hdual := entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_ae_le (ae_of_all _ hcB) ε) hc.aemeasurable hε
    (.of_bound hpm.aestronglyMeasurable C (ae_of_all _ hpC))
    (.of_bound hpm.aestronglyMeasurable C (ae_of_all _ hpC)) hexp_m
  rw [entropicDualValue_def, kantorovichDualValue_def, integral_sub hexp_m (integrable_const _),
    integral_entropicGibbsFactor_eq hpm hpm hexp_m] at hdual
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hdual
  set z₀ := hk.kernelMeanEmbedding (tilt μ₀ ε p₀)
  set z₁ := hk.kernelMeanEmbedding (tilt μ₁ ε p₁)
  have hz₀ : ‖z₀‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq,
      hk.inner_kernelMeanEmbedding (hk.integrable_kolmogorovFeature hkc _)
        (hk.integrable_kolmogorovFeature hkc _), hEp₀]
  have hz₁ : ‖z₁‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq,
      hk.inner_kernelMeanEmbedding (hk.integrable_kolmogorovFeature hkc _)
        (hk.integrable_kolmogorovFeature hkc _), hEp₁]
  have hEm : ∫ y, ∫ x, entropicGibbsKernel c ε x y ∂tilt μm ε p ∂tilt μm ε p =
      1 - (a : ℝ) * b * ‖z₀ - z₁‖ ^ 2 := by
    rw [← hk.inner_kernelMeanEmbedding (hk.integrable_kolmogorovFeature hkc _)
      (hk.integrable_kolmogorovFeature hkc _), real_inner_self_eq_norm_sq, htilt_comb,
      hk.kernelMeanEmbedding_add_measure
        ((hk.integrable_kolmogorovFeature hkc _).smul_measure ENNReal.coe_ne_top)
        ((hk.integrable_kolmogorovFeature hkc _).smul_measure ENNReal.coe_ne_top),
      hk.kernelMeanEmbedding_smul_measure, hk.kernelMeanEmbedding_smul_measure,
      ENNReal.coe_toReal, ENNReal.coe_toReal]
    have hcomb : z₀ - ((b : ℝ) / ((a : ℝ) + b)) • (z₀ - z₁) = (a : ℝ) • z₀ + (b : ℝ) • z₁ := by
      rw [habR, div_one]
      have ha1 : (a : ℝ) = 1 - b := by linarith
      rw [ha1]
      module
    have hsub : z₀ - z₁ - z₀ = -z₁ := by abel
    have hsq := mul_norm_sq_add_mul_norm_sub_sq (a := (a : ℝ)) (b := (b : ℝ))
      (by rw [habR]; exact one_ne_zero) (z₀ - z₁) z₀
    rw [hsub, norm_neg, hcomb, habR, one_mul, div_one, hz₀, hz₁] at hsq
    linarith
  refine ⟨p₀, p₁, C₀, C₁, hp₀, hp₁, hp₀C, hp₁C, hμ₀p, hμ₁p, ?_⟩
  rw [sinkhornNegentropy_def, sinkhornNegentropy_def, sinkhornNegentropy_def, hμ₀, hμ₁]
  rw [hEm] at hdual
  linarith

/-- **Convexity of Sinkhorn negentropy.** On a compact space, for a bounded measurable cost whose
Gibbs kernel `exp (-c / ε)` is continuous and positive definite, and a positive temperature `ε`,
`μ ↦ sinkhornNegentropy c ε μ` is convex on probability measures. -/
theorem sinkhornNegentropy_smul_add_smul_le [OpensMeasurableSpace X] {μ₀ μ₁ : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {a b : ℝ≥0} (hab : a + b = 1)
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    sinkhornNegentropy c ε (a • μ₀ + b • μ₁) ≤
      a * sinkhornNegentropy c ε μ₀ + b * sinkhornNegentropy c ε μ₁ := by
  obtain ⟨p₀, p₁, -, -, -, -, -, -, -, -, h⟩ :=
    exists_sq_norm_sinkhornNegentropy_smul_add_smul_le (μ₀ := μ₀) (μ₁ := μ₁) hab hc hcB hε hk hkc
  have hnn : 0 ≤ (ε : ℝ) / 2 * a * b *
      ‖hk.kernelMeanEmbedding (tilt μ₀ ε p₀) - hk.kernelMeanEmbedding (tilt μ₁ ε p₁)‖ ^ 2 := by
    positivity
  linarith

/-- **Strict convexity of Sinkhorn negentropy.** On a compact Borel space with
`HasOuterApproxClosed`, if the Gibbs kernel `exp (-c / ε)` is continuous, positive definite, and
universal at positive temperature `ε`, then `sinkhornNegentropy c ε` is strictly convex on
probability measures. -/
theorem sinkhornNegentropy_smul_add_smul_lt [BorelSpace X] [HasOuterApproxClosed X]
    {μ₀ μ₁ : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {a b : ℝ≥0}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1) (hne : μ₀ ≠ μ₁) (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornNegentropy c ε (a • μ₀ + b • μ₁) <
      a * sinkhornNegentropy c ε μ₀ + b * sinkhornNegentropy c ε μ₁ := by
  obtain ⟨p₀, p₁, C₀, C₁, hp₀, hp₁, hp₀C, hp₁C, hμ₀p, hμ₁p, h⟩ :=
    exists_sq_norm_sinkhornNegentropy_smul_add_smul_le (μ₀ := μ₀) (μ₁ := μ₁) hab hc hcB hε hk hkc
  have := isFiniteMeasure_tilt (μ := μ₀) (ε := ε) hp₀ hp₀C
  have := isFiniteMeasure_tilt (μ := μ₁) (ε := ε) hp₁ hp₁C
  have hdiff_ne : hk.kernelMeanEmbedding (tilt μ₀ ε p₀) -
      hk.kernelMeanEmbedding (tilt μ₁ ε p₁) ≠ 0 := by
    intro h0
    have htilt : tilt μ₀ ε p₀ = tilt μ₁ ε p₁ :=
      (hk.kernelMeanEmbedding_inj hkc hku).1 (sub_eq_zero.1 h0)
    apply hne
    rw [hμ₀p, hμ₁p, htilt]
  have hgap : 0 < (ε : ℝ) / 2 * a * b *
      ‖hk.kernelMeanEmbedding (tilt μ₀ ε p₀) - hk.kernelMeanEmbedding (tilt μ₁ ε p₁)‖ ^ 2 := by
    positivity
  linarith

/-- **Convexity of the Sinkhorn divergence in the first marginal** (Feydy et al., Proposition 2).
On a compact space, for a bounded measurable cost whose Gibbs kernel is continuous and positive
definite at positive temperature `ε`, `μ ↦ sinkhornDivergence c ε μ ν` is convex on probability
measures. -/
theorem sinkhornDivergence_smul_add_smul_left_le [OpensMeasurableSpace X] {μ₀ μ₁ ν : Measure X}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν] {a b : ℝ≥0}
    (hab : a + b = 1) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    sinkhornDivergence c ε (a • μ₀ + b • μ₁) ν ≤
      a * sinkhornDivergence c ε μ₀ ν + b * sinkhornDivergence c ε μ₁ ν := by
  have habR : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hOT := toReal_entropicTransportCost_smul_add_smul_left_le hab
    (entropicTransportCost_ne_top_of_ae_le (μ := μ₀) (ν := ν) (ae_of_all _ hcB) ε)
    (entropicTransportCost_ne_top_of_ae_le (μ := μ₁) (ν := ν) (ae_of_all _ hcB) ε)
  have hH := sinkhornNegentropy_smul_add_smul_le (μ₀ := μ₀) (μ₁ := μ₁) hab hc hcB hε hk hkc
  have hν_eq : sinkhornNegentropy c ε ν =
      (a : ℝ) * sinkhornNegentropy c ε ν + b * sinkhornNegentropy c ε ν := by
    rw [← add_mul, habR, one_mul]
  rw [sinkhornDivergence_eq_add_sinkhornNegentropy, sinkhornDivergence_eq_add_sinkhornNegentropy,
    sinkhornDivergence_eq_add_sinkhornNegentropy]
  linarith

/-- **Convexity of the Sinkhorn divergence in the second marginal.** -/
theorem sinkhornDivergence_smul_add_smul_right_le [OpensMeasurableSpace X] {μ ν₀ ν₁ : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] {a b : ℝ≥0}
    (hab : a + b = 1) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε))) :
    sinkhornDivergence c ε μ (a • ν₀ + b • ν₁) ≤
      a * sinkhornDivergence c ε μ ν₀ + b * sinkhornDivergence c ε μ ν₁ := by
  have : IsProbabilityMeasure (a • ν₀ + b • ν₁) := by
    have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
    exact ⟨by simp [hab']⟩
  rw [sinkhornDivergence_comm_of_posSemidef hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₀) hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₁) hcB hε hk]
  exact sinkhornDivergence_smul_add_smul_left_le hab hc hcB hε hk hkc

/-- **Strict convexity of the Sinkhorn divergence in the first marginal** (Feydy et al.,
Theorem 1). When the Gibbs kernel is moreover universal on a compact Borel space with
`HasOuterApproxClosed`, `μ ↦ sinkhornDivergence c ε μ ν` is strictly convex on probability
measures, so `ν` is its unique global and local minimiser. -/
theorem sinkhornDivergence_smul_add_smul_left_lt [BorelSpace X] [HasOuterApproxClosed X]
    {μ₀ μ₁ ν : Measure X} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure ν] {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1)
    (hne : μ₀ ≠ μ₁) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε (a • μ₀ + b • μ₁) ν <
      a * sinkhornDivergence c ε μ₀ ν + b * sinkhornDivergence c ε μ₁ ν := by
  have habR : (a : ℝ) + b = 1 := by exact_mod_cast hab
  have hOT := toReal_entropicTransportCost_smul_add_smul_left_le hab
    (entropicTransportCost_ne_top_of_ae_le (μ := μ₀) (ν := ν) (ae_of_all _ hcB) ε)
    (entropicTransportCost_ne_top_of_ae_le (μ := μ₁) (ν := ν) (ae_of_all _ hcB) ε)
  have hH := sinkhornNegentropy_smul_add_smul_lt ha hb hab hne hc hcB hε hk hkc hku
  have hν_eq : sinkhornNegentropy c ε ν =
      (a : ℝ) * sinkhornNegentropy c ε ν + b * sinkhornNegentropy c ε ν := by
    rw [← add_mul, habR, one_mul]
  rw [sinkhornDivergence_eq_add_sinkhornNegentropy, sinkhornDivergence_eq_add_sinkhornNegentropy,
    sinkhornDivergence_eq_add_sinkhornNegentropy]
  linarith

/-- **Strict convexity of the Sinkhorn divergence in the second marginal.** -/
theorem sinkhornDivergence_smul_add_smul_right_lt [BorelSpace X] [HasOuterApproxClosed X]
    {μ ν₀ ν₁ : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1)
    (hne : ν₀ ≠ ν₁) (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0)
    (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hkc : Continuous (uncurry (entropicGibbsKernel c ε)))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    sinkhornDivergence c ε μ (a • ν₀ + b • ν₁) <
      a * sinkhornDivergence c ε μ ν₀ + b * sinkhornDivergence c ε μ ν₁ := by
  have : IsProbabilityMeasure (a • ν₀ + b • ν₁) := by
    have hab' : (a : ℝ≥0∞) + b = 1 := by exact_mod_cast hab
    exact ⟨by simp [hab']⟩
  rw [sinkhornDivergence_comm_of_posSemidef hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₀) hcB hε hk,
    sinkhornDivergence_comm_of_posSemidef (μ := μ) (ν := ν₁) hcB hε hk]
  exact sinkhornDivergence_smul_add_smul_left_lt ha hb hab hne hc hcB hε hk hkc hku

/-- **Weak continuity of Sinkhorn negentropy on compact spaces.** For a continuous finite-valued
cost on a compact space and a positive temperature `ε`, `μ ↦ sinkhornNegentropy c ε μ` is
continuous on `ProbabilityMeasure X`. -/
theorem continuous_sinkhornNegentropy [OpensMeasurableSpace X] [OpensMeasurableSpace (X × X)]
    (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) :
    Continuous fun μ : ProbabilityMeasure X ↦ sinkhornNegentropy c ε (μ : Measure X) := by
  simp_rw [sinkhornNegentropy_def]
  exact ((continuous_toReal_entropicTransportCost hc hfin hε).comp
    (continuous_id.prodMk continuous_id)).neg.div_const 2

/-- **Joint weak continuity of the Sinkhorn divergence on compact spaces.** For a continuous
finite-valued cost on a compact space and a positive temperature `ε`, the map
`(μ, ν) ↦ sinkhornDivergence c ε μ ν` is jointly continuous on
`ProbabilityMeasure X × ProbabilityMeasure X`. -/
theorem continuous_sinkhornDivergence [OpensMeasurableSpace X] [OpensMeasurableSpace (X × X)]
    (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) :
    Continuous fun p : ProbabilityMeasure X × ProbabilityMeasure X ↦
      sinkhornDivergence c ε (p.1 : Measure X) (p.2 : Measure X) := by
  simp_rw [sinkhornDivergence_eq_add_sinkhornNegentropy]
  exact ((continuous_toReal_entropicTransportCost hc hfin hε).add
    ((continuous_sinkhornNegentropy hc hfin hε).comp continuous_fst)).add
    ((continuous_sinkhornNegentropy hc hfin hε).comp continuous_snd)

/-- **The Sinkhorn divergence metrizes weak convergence** (Feydy--Séjourné--Vialard--Amari--
Trouvé--Peyré, Theorem 1). On a compact Hausdorff space with `HasOuterApproxClosed` and its Borel
σ-algebra (for instance any compact metric space), for a continuous finite-valued cost whose Gibbs
kernel `exp (-c / ε)` is positive definite and universal at positive temperature `ε`, a family of
probability measures `μs` converges weakly to `μ` along a filter `l` if and only if
`sinkhornDivergence c ε (μs i) μ` tends to `0` along `l`. -/
theorem tendsto_sinkhornDivergence_zero_iff_tendsto [T2Space X] [BorelSpace X]
    [HasOuterApproxClosed X] [OpensMeasurableSpace (X × X)] {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X} (hc : Continuous c)
    (hfin : ∀ z, c z ≠ ∞) (hε : ε ≠ 0) (hk : Matrix.PosSemidef (entropicGibbsKernel c ε))
    (hku : IsUniversalKernel (entropicGibbsKernel c ε)) :
    Tendsto (fun i ↦ sinkhornDivergence c ε (μs i : Measure X) (μ : Measure X)) l (𝓝 0) ↔
      Tendsto μs l (𝓝 μ) := by
  have hcont : Continuous fun ν : ProbabilityMeasure X ↦
      sinkhornDivergence c ε (ν : Measure X) (μ : Measure X) :=
    (continuous_sinkhornDivergence hc hfin hε).comp (continuous_id.prodMk continuous_const)
  refine ⟨fun h ↦ tendsto_nhds_of_unique_mapClusterPt fun ν hν ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨U, hUl, hUν⟩ := mapClusterPt_iff_ultrafilter.1 hν
    have hlim₀ : Tendsto (fun i ↦ sinkhornDivergence c ε (μs i : Measure X) (μ : Measure X))
        U (𝓝 0) := h.mono_left hUl
    have hlimν : Tendsto (fun i ↦ sinkhornDivergence c ε (μs i : Measure X) (μ : Measure X))
        U (𝓝 (sinkhornDivergence c ε (ν : Measure X) (μ : Measure X))) :=
      (hcont.tendsto ν).comp hUν
    have hzero : sinkhornDivergence c ε (ν : Measure X) (μ : Measure X) = 0 :=
      tendsto_nhds_unique hlimν hlim₀
    have hcR : Continuous fun z : X × X ↦ (c z).toReal :=
      ENNReal.continuousOn_toReal.comp_continuous hc hfin
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcR.continuousOn
    have hcB : ∀ z, c z ≤ Real.toNNReal M := fun z ↦ by
      rw [← ENNReal.ofReal_toReal (hfin z), ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      exact ((le_abs_self _).trans (by simpa using hM z (mem_univ z))).trans
        (Real.le_coe_toNNReal M)
    exact ProbabilityMeasure.toMeasure_injective
      ((sinkhornDivergence_eq_zero_iff hc.measurable hcB hε hk
        (continuous_entropicGibbsKernel hc hfin) hku).1 hzero)
  · simpa only [Function.comp_def, sinkhornDivergence_self] using (hcont.tendsto μ).comp h

end Compact

end TauCeti
