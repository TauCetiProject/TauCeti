/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Continuity of linear maps into Bessel-potential spaces

An element `u` of Mathlib's Bessel-potential space `H^{s,p}(E, F)` is determined by its tempered
distribution `u.toDistr`, and the map `u ↦ u.toDistr` is continuous, being `u ↦ J^{-s} u.toLp`
for the Bessel potential `J^{-s}`. By the closed graph theorem, a linear map from a Banach space
into `H^{s,p}(E, F)` is therefore bounded as soon as the tempered distributions of its values
depend continuously on the argument.

This is how mapping properties stated for tempered distributions become bounded operators. A
differential operator `P` whose coefficients have temperate growth (smooth, with polynomially
bounded derivatives) acts continuously on `𝓢'(E, F)`; if it maps `H^{s,p}` into `H^{r,p}`, then
the induced linear map `H^{s,p} → H^{r,p}` is bounded, with no estimate to prove beyond the
membership statement.

## Main results

* `BesselPotentialSpace.continuous_toDistr`: the tempered distribution depends continuously on
  `u ∈ H^{s,p}(E, F)`.
* `LinearMap.continuous_of_continuous_toDistr`: a linear map `T` from a Banach space into
  `H^{s,p}(E, F)` is continuous when `x ↦ (T x).toDistr` is.
-/

public section

open TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The tempered distribution of an element of `H^{s,p}(E, F)` depends continuously on it: it is
the image of the `Lᵖ` part under the Bessel potential `J^{-s}`. -/
theorem continuous_toDistr :
    Continuous (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) := by
  have h : (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) = fun u ↦
      besselPotential E F (-s) (MeasureTheory.Lp.toTemperedDistributionCLM F
        (MeasureTheory.volume : MeasureTheory.Measure E) p (toLpₗᵢ E F s p u)) := by
    ext1 u
    simp
  rw [h]
  exact (besselPotential E F (-s)).continuous.comp
    ((MeasureTheory.Lp.toTemperedDistributionCLM F _ p).continuous.comp
      (toLpₗᵢ E F s p).continuous)

end BesselPotentialSpace

namespace LinearMap

open BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Closed graph criterion for maps into `H^{s,p}`.** A linear map `T` from a Banach space into
the Bessel-potential space `H^{s,p}(E, F)` is continuous as soon as the tempered distributions
`(T x).toDistr` depend continuously on `x`. -/
theorem continuous_of_continuous_toDistr {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (T : X →ₗ[ℂ] H^{s, p}(E, F)) (hT : Continuous fun x ↦ (T x).toDistr) :
    Continuous T := by
  refine T.continuous_of_isClosed_graph ?_
  have hgraph : (T.graph : Set (X × H^{s, p}(E, F))) =
      {q | q.2.toDistr = (T q.1).toDistr} := by
    ext ⟨x, u⟩
    simp only [LinearMap.mem_graph_iff, SetLike.mem_coe, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ BesselPotentialSpace.ext h⟩
  rw [hgraph]
  exact isClosed_eq (continuous_toDistr.comp continuous_snd) (hT.comp continuous_fst)

end LinearMap
