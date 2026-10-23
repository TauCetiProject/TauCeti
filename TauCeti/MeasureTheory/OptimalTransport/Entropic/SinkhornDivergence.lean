/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.MeanEmbedding
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Symmetric

/-!
# Sinkhorn divergences

The entropic transport cost `OT_ε(μ, ν) = TauCeti.entropicTransportCost c ε μ ν` is biased: in
general `OT_ε(μ, μ) ≠ 0`. The *Sinkhorn divergence*

`S_ε(μ, ν) = OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2`

removes this bias, so that `S_ε(μ, μ) = 0`. This file defines it and proves that it is
nonnegative and definite when the Gibbs kernel `k(x, y) = exp (-c(x, y) / ε)` is positive
definite (and, for definiteness, universal), following Feydy--Séjourné--Vialard--Amari--Trouvé--
Peyré, Theorem 1. Pointwise positivity of the kernel is not enough: positive-definiteness is what
the proof uses.

The argument compares the three entropic problems through their symmetric self-potentials. For a
bounded symmetric cost, the self-transport problem of `μ` has a bounded potential `p` with
`OT_ε(μ, μ) = 2 ∫ p dμ` whose Gibbs density is a coupling of `μ` with itself
(`TauCeti.exists_isCoupling_entropicGibbsFactor_self`); let `q` be the corresponding potential of
`ν`. Evaluating the dual problem of `OT_ε(μ, ν)` at the pair `(p, q)` gives, by weak duality,

`S_ε(μ, ν) ≥ ε * (1 - ∫∫ k d(e^{p/ε} μ) d(e^{q/ε} ν))`.

The marginal equations of the two self-couplings say that the tilted measures `a = e^{p/ε} μ` and
`b = e^{q/ε} ν` have kernel energy `∫∫ k da da = ∫∫ k db db = 1`, so the right-hand side is half
of `ε` times the kernel energy of `a - b`, which is `‖m a - m b‖ ^ 2` for the kernel mean
embedding `m` (`Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`), hence nonnegative. If the
divergence vanishes, the mean embeddings of `a` and `b` agree, so `a = b` for a universal kernel
(`Matrix.PosSemidef.kernelMeanEmbedding_inj`). The marginal equations also recover `μ` and `ν`
from `a` and `b` by the same formula, `μ = (∫ k(·, y) da(y)) • a`, so `μ = ν`.

The Sinkhorn divergence is real-valued, through `ENNReal.toReal` of the three entropic costs. It
is the intended value when these are finite, as they are for the bounded costs considered here.

## Main definitions

* `TauCeti.sinkhornDivergence c ε μ ν`: the debiased entropic transport cost
  `OT_ε(μ, ν) - OT_ε(μ, μ) / 2 - OT_ε(ν, ν) / 2`.

## Main statements

* `TauCeti.sinkhornDivergence_self`: the Sinkhorn divergence vanishes on the diagonal.
* `TauCeti.sinkhornDivergence_nonneg`: for a bounded measurable cost on a compact space whose
  Gibbs kernel is continuous and positive definite, the Sinkhorn divergence of two probability
  measures is nonnegative.
* `TauCeti.sinkhornDivergence_eq_zero_iff`: if moreover the space is Borel with
  `HasOuterApproxClosed`, for instance compact metrizable, and the Gibbs kernel is universal, the
  Sinkhorn divergence of two probability measures vanishes exactly when they are equal.

For a continuous bounded cost the continuity hypothesis on the Gibbs kernel is supplied by
`TauCeti.continuous_entropicGibbsKernel`.

## References

* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré,
  *Interpolating between optimal transport and MMD using Sinkhorn divergences*,
  AISTATS 2019, Theorem 1 and its proof in the supplementary material.
-/

public section

noncomputable section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {c : X × X → ℝ≥0∞} {ε B : ℝ≥0} {μ ν : Measure X}

/-! ### The definition -/

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

/-- The Sinkhorn divergence vanishes on the diagonal. -/
@[simp]
theorem sinkhornDivergence_self (c : X × X → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) :
    sinkhornDivergence c ε μ μ = 0 := by
  rw [sinkhornDivergence_def]
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
    (entropicTransportCost_ne_top_of_forall_le hcB ε) hc.aemeasurable hε
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
    div_left_inj' (NNReal.coe_ne_zero.2 hε), neg_inj] at h
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

end TauCeti
