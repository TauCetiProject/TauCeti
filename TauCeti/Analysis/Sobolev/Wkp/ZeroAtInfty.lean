/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.ZeroAtInftyRepresentative
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Continuous representatives of whole-space Sobolev functions

This file contains the part of the Sobolev embeddings `W^{k,p}(E) → C₀(E)` that does not depend
on `k`, `p` or the dimension. Suppose every `u ∈ W^{k,p}(E)` agrees almost everywhere with some
continuous function vanishing at infinity. Since two continuous functions that agree almost
everywhere are equal, this representative is unique, so it depends linearly on `u`. Its graph is
closed, because a sequence converging in `W^{k,p}` converges almost everywhere along a subsequence,
while convergence in `C₀` is uniform. By the closed graph theorem the representative is therefore
a continuous linear map `W^{k,p}(E) →L[ℝ] C₀(E)`, and it is injective.

## Main declarations

* `TauCeti.Wkp.zeroAtInfty_eq_of_value_ae_eq`: a Sobolev function has at most one representative
  in `C₀`.
* `TauCeti.Wkp.value_ae_eq_of_tendsto`: if `uₙ → w` in `W^{k,p}` and the representatives of the
  `uₙ` in `C₀` converge to `g`, then `g` represents `w`.
* `TauCeti.Wkp.toZeroAtInftyOfExists`: the continuous representative, as a continuous linear map
  `W^{k,p}(E) →L[ℝ] C₀(E)`, given that every Sobolev function has one.
-/

public section

noncomputable section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ZeroAtInfty ENNReal

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- Two continuous representatives of the same Sobolev function coincide. -/
theorem zeroAtInfty_eq_of_value_ae_eq {u : Wkp mu ⊤ p k} {g g' : C₀(E, ℝ)}
    (hg : value k u =ᵐ[mu] g) (hg' : value k u =ᵐ[mu] g') : g = g' :=
  ZeroAtInftyContinuousMap.eq_of_ae_eq (hg.symm.trans hg')

/-- If `uₙ → w` in `W^{k,p}` and continuous representatives `gₙ` of the `uₙ` converge in `C₀` to
`g`, then `g` represents `w`: the values converge almost everywhere along a subsequence, while the
representatives converge uniformly. -/
theorem value_ae_eq_of_tendsto {u : ℕ → Wkp mu ⊤ p k} {w : Wkp mu ⊤ p k}
    {g : ℕ → C₀(E, ℝ)} {g₀ : C₀(E, ℝ)} (hu : Tendsto u atTop (𝓝 w))
    (hug : ∀ n, value k (u n) =ᵐ[mu] g n) (hg : Tendsto g atTop (𝓝 g₀)) :
    value k w =ᵐ[mu] g₀ := by
  have hval : Tendsto (fun n => value k (u n)) atTop (𝓝 (value k w)) := tendsto_value hu
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  rw [Measure.ae_restrict_coe_opens_top] at hns
  filter_upwards [hns, ae_all_iff.mpr fun i => hug (ns i)] with x hx hxrep
  -- Convergence in `C₀` is uniform, so it implies convergence at `x`.
  have heval : Tendsto (fun i => g (ns i) x) atTop (𝓝 (g₀ x)) :=
    (((continuous_apply x).comp (BoundedContinuousFunction.continuous_coe.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous)).tendsto g₀).comp
        (hg.comp hmono.tendsto_atTop)
  exact tendsto_nhds_unique (hx.congr hxrep) heval

/-- The continuous representative of a Sobolev function, as a linear map. -/
private def toZeroAtInftyOfExistsₗ (h : ∀ u : Wkp mu ⊤ p k, ∃ g : C₀(E, ℝ), value k u =ᵐ[mu] g) :
    Wkp mu ⊤ p k →ₗ[ℝ] C₀(E, ℝ) :=
  zeroAtInftyRepresentativeₗ h
    (fun u v => (Measure.ae_restrict_coe_opens_top mu).ge (value_add_ae k u v))
    (fun c u => (Measure.ae_restrict_coe_opens_top mu).ge (value_smul_ae k c u))

private theorem value_ae_eq_toZeroAtInftyOfExistsₗ
    (h : ∀ u : Wkp mu ⊤ p k, ∃ g : C₀(E, ℝ), value k u =ᵐ[mu] g) (u : Wkp mu ⊤ p k) :
    value k u =ᵐ[mu] toZeroAtInftyOfExistsₗ h u :=
  ae_eq_zeroAtInftyRepresentativeₗ h _ _ u

/-- **The continuous representative of a whole-space Sobolev function.** If every function in
`W^{k,p}(E)` agrees almost everywhere with a continuous function vanishing at infinity, the map
sending a Sobolev function to this unique representative is a continuous linear map
`W^{k,p}(E) →L[ℝ] C₀(E)`, by the closed graph theorem. -/
def toZeroAtInftyOfExists (h : ∀ u : Wkp mu ⊤ p k, ∃ g : C₀(E, ℝ), value k u =ᵐ[mu] g) :
    Wkp mu ⊤ p k →L[ℝ] C₀(E, ℝ) :=
  .ofSeqClosedGraph (g := toZeroAtInftyOfExistsₗ h) fun _ _ _ hu hg =>
    zeroAtInfty_eq_of_value_ae_eq
      (value_ae_eq_of_tendsto hu (fun _ => value_ae_eq_toZeroAtInftyOfExistsₗ h _) hg)
      (value_ae_eq_toZeroAtInftyOfExistsₗ h _)

/-- The continuous representative represents the value of a Sobolev function. -/
theorem value_ae_eq_toZeroAtInftyOfExists
    (h : ∀ u : Wkp mu ⊤ p k, ∃ g : C₀(E, ℝ), value k u =ᵐ[mu] g) (u : Wkp mu ⊤ p k) :
    value k u =ᵐ[mu] toZeroAtInftyOfExists h u :=
  value_ae_eq_toZeroAtInftyOfExistsₗ h u

/-- The continuous representative of `u` is the only function in `C₀` representing the value
of `u`. -/
theorem toZeroAtInftyOfExists_eq_iff
    (h : ∀ u : Wkp mu ⊤ p k, ∃ g : C₀(E, ℝ), value k u =ᵐ[mu] g) (u : Wkp mu ⊤ p k)
    (g : C₀(E, ℝ)) :
    toZeroAtInftyOfExists h u = g ↔ value k u =ᵐ[mu] g :=
  ⟨fun hg => hg ▸ value_ae_eq_toZeroAtInftyOfExists h u,
    fun hg => zeroAtInfty_eq_of_value_ae_eq (value_ae_eq_toZeroAtInftyOfExists h u) hg⟩

/-- The continuous representative determines the Sobolev function. -/
theorem toZeroAtInftyOfExists_injective
    (h : ∀ u : Wkp mu ⊤ p k, ∃ g : C₀(E, ℝ), value k u =ᵐ[mu] g) :
    Function.Injective (toZeroAtInftyOfExists h) := by
  intro u v huv
  refine ext_ae ?_
  filter_upwards [value_ae_eq_toZeroAtInftyOfExists h u,
    value_ae_eq_toZeroAtInftyOfExists h v] with x hu hv
  rw [hu, hv, huv]

end Wkp

end TauCeti
