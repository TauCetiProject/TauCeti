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

If the value of `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function `G` that is
Lipschitz on `Ω`, then the weak gradient of `u` is the classical gradient `∇G`, which exists almost
everywhere by Rademacher's theorem (`TauCeti.W1p.gradient_ae_eq_of_lipschitzOnWith`), and it is
bounded by the Lipschitz constant of `G` (`TauCeti.W1p.ae_norm_gradient_le_of_lipschitzOnWith`).
This is the Lipschitz counterpart of `TauCeti.W1p.gradient_ae_eq_of_contDiffOn`. It applies, for
instance, to boundary data of the Dirichlet problem given by a Lipschitz function, whose weak
gradient then lies in `L^∞(Ω)`.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The weak gradient of a Lipschitz representative is its classical gradient.** If the value of
`u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function `G` that is Lipschitz on `Ω`, then
the weak gradient of `u` is `∇G` almost everywhere on `Ω`. -/
theorem W1p.gradient_ae_eq_of_lipschitzOnWith (u : W1p mu Omega p) {G : E → ℝ} {K : ℝ≥0}
    (huG : W1p.value u =ᵐ[mu.restrict Omega] G) (hG : LipschitzOnWith K G Omega) :
    W1p.gradient u =ᵐ[mu.restrict Omega] ∇ G := by
  have h := ((W1p.hasWeakFDerivOn u).congr_ae huG).ae_eq
    hG.locallyLipschitzOn.hasWeakFDerivOn_fderiv
  filter_upwards [h] with x hx
  exact innerSL_inj.mp (hx.trans toDual_gradient.symm)

/-- **The weak gradient of a Lipschitz representative is bounded by the Lipschitz constant.** If
the value of `u ∈ W^{1,p}(Ω)` agrees almost everywhere on `Ω` with a function that is
`K`-Lipschitz on `Ω`, then `‖∇u‖ ≤ K` almost everywhere on `Ω`. -/
theorem W1p.ae_norm_gradient_le_of_lipschitzOnWith (u : W1p mu Omega p) {G : E → ℝ} {K : ℝ≥0}
    (huG : W1p.value u =ᵐ[mu.restrict Omega] G) (hG : LipschitzOnWith K G Omega) :
    ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient u x‖ ≤ K := by
  filter_upwards [W1p.gradient_ae_eq_of_lipschitzOnWith u huG hG,
    ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
  have hdual : innerSL ℝ (∇ G x) = fderiv ℝ G x := toDual_gradient
  rw [hx, ← innerSL_apply_norm ℝ, hdual]
  exact norm_fderiv_le_of_lipschitzOn ℝ (Omega.isOpen.mem_nhds hxΩ) hG

end TauCeti
