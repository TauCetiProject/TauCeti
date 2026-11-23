/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Sobolev functions with a Lipschitz representative

A function `G` that is locally Lipschitz on `Ω` is differentiable almost everywhere on `Ω` by
Rademacher's theorem, and its derivative is its weak derivative. Hence:

* `TauCeti.W1p.exists_value_gradient_ae_eq_of_locallyLipschitzOn`: if `G` and its gradient `∇G`
  lie in `Lᵖ(Ω)`, then `G` is represented by an element of `W^{1,p}(Ω)` with weak gradient `∇G`.
* `TauCeti.W1p.exists_value_gradient_ae_eq_of_lipschitzOnWith`: in particular a bounded Lipschitz
  function on a set `Ω` of finite measure is represented by an element of `W^{1,p}(Ω)`.
* `TauCeti.W1p.gradient_ae_eq_of_locallyLipschitzOn`: conversely, if the value of
  `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function `G` that is locally Lipschitz
  on `Ω`, then the weak gradient of `u` is the classical gradient `∇G`.
* `TauCeti.W1p.ae_norm_gradient_le_of_lipschitzOnWith`: if `G` is `K`-Lipschitz on `Ω`, this weak
  gradient is bounded by `K`.

This is the Lipschitz counterpart of `TauCeti.W1p.exists_value_gradient_ae_eq_of_contDiffOn` and
`TauCeti.W1p.gradient_ae_eq_of_contDiffOn`. It applies, for instance, to boundary data of the
Dirichlet problem given by a Lipschitz function, whose weak gradient then lies in `L^∞(Ω)`.
-/
public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A locally Lipschitz function with integrable gradient is a Sobolev function.** If `G` is
locally Lipschitz on `Ω` and both `G` and its gradient `∇G`, which exists almost everywhere on `Ω`
by Rademacher's theorem, lie in `Lᵖ(Ω)`, then `G` is represented by an element of `W^{1,p}(Ω)`
whose weak gradient is `∇G`. -/
theorem W1p.exists_value_gradient_ae_eq_of_locallyLipschitzOn {G : E → ℝ}
    (hG : LocallyLipschitzOn Omega G) (hv : MemLp G p (mu.restrict Omega))
    (hg : MemLp (∇ G) p (mu.restrict Omega)) :
    ∃ u : W1p mu Omega p, W1p.value u =ᵐ[mu.restrict Omega] G ∧
      W1p.gradient u =ᵐ[mu.restrict Omega] ∇ G :=
  W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hv
    (((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
      hg).ae_eq (ae_of_all _ fun _ => toDual_gradient)) hG.hasWeakFDerivOn_fderiv

/-- **A bounded Lipschitz function is a Sobolev function.** If `Ω` has finite measure and `G` is
bounded and Lipschitz on `Ω`, then `G` is represented by an element of `W^{1,p}(Ω)` whose weak
gradient is the classical gradient `∇G`. -/
theorem W1p.exists_value_gradient_ae_eq_of_lipschitzOnWith {G : E → ℝ} {K : ℝ≥0} {K₀ : ℝ}
    (hG : LipschitzOnWith K G Omega) (hG0 : ∀ x ∈ Omega, |G x| ≤ K₀)
    (hfin : mu Omega ≠ ∞) :
    ∃ u : W1p mu Omega p, W1p.value u =ᵐ[mu.restrict Omega] G ∧
      W1p.gradient u =ᵐ[mu.restrict Omega] ∇ G := by
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hfin
  have hΩ := ae_restrict_mem (μ := mu) Omega.isOpen.measurableSet
  have hgm : Measurable (∇ G) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ G)
  refine W1p.exists_value_gradient_ae_eq_of_locallyLipschitzOn hG.locallyLipschitzOn
    (MemLp.of_bound (hG.continuousOn.aestronglyMeasurable Omega.isOpen.measurableSet) K₀
      (hΩ.mono fun x hx => (Real.norm_eq_abs _).trans_le (hG0 x hx)))
    (MemLp.of_bound hgm.aestronglyMeasurable K (hΩ.mono fun x hx => ?_))
  rw [_root_.gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hx) hG

/-- **The weak gradient of a locally Lipschitz representative is its classical gradient.** If the
value of `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function `G` that is locally
Lipschitz on `Ω`, then the weak gradient of `u` is `∇G` almost everywhere on `Ω`. -/
theorem W1p.gradient_ae_eq_of_locallyLipschitzOn (u : W1p mu Omega p) {G : E → ℝ}
    (huG : W1p.value u =ᵐ[mu.restrict Omega] G) (hG : LocallyLipschitzOn Omega G) :
    W1p.gradient u =ᵐ[mu.restrict Omega] ∇ G := by
  have h := ((W1p.hasWeakFDerivOn u).congr_ae huG).ae_eq hG.hasWeakFDerivOn_fderiv
  filter_upwards [h] with x hx
  exact innerSL_inj.mp (hx.trans toDual_gradient.symm)

/-- **The weak gradient of a Lipschitz representative is bounded by the Lipschitz constant.** If
the value of `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function that is
`K`-Lipschitz on `Ω`, then `‖∇u‖ ≤ K` almost everywhere on `Ω`. -/
theorem W1p.ae_norm_gradient_le_of_lipschitzOnWith (u : W1p mu Omega p) {G : E → ℝ} {K : ℝ≥0}
    (huG : W1p.value u =ᵐ[mu.restrict Omega] G) (hG : LipschitzOnWith K G Omega) :
    ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient u x‖ ≤ K := by
  filter_upwards [W1p.gradient_ae_eq_of_locallyLipschitzOn u huG hG.locallyLipschitzOn,
    ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
  have hdual : innerSL ℝ (∇ G x) = fderiv ℝ G x := toDual_gradient
  rw [hx, ← innerSL_apply_norm ℝ, hdual]
  exact norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hxΩ) hG

end TauCeti
