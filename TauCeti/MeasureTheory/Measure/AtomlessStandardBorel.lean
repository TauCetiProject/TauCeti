/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Atom
public import TauCeti.Probability.Quantile

/-!
# Atomless standard-Borel transport to the unit interval

This file proves that an atomless standard-Borel probability space is measure-preservingly
isomorphic modulo null sets to the unit interval with Lebesgue measure. The real-line
construction uses the cumulative distribution function and the generalized inverse already
provided by `MeasureTheory.Measure.quantile`, then transports a standard-Borel space to `ℝ`
by `embeddingReal`.

The CDF/quantile route is adapted from Cameron Freer's independent implementation in
`Graphon/MeasureIso.lean` at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>.
The graphon-specific packaging was removed. The original work is copyright Cameron Freer
and licensed under Apache 2.0. The underlying measure-preserving equivalence is also the
standard-Borel transport theorem in S. Janson, *Graphons, cut norm and distance, couplings
and rearrangements*, Theorem A.7.

Here `NullSingletonClass μ` is the formal hypothesis. On a standard-Borel space it gives the
atomlessness used by the CDF argument; the class itself only asserts that every singleton is
null. The mod-zero isomorphism machinery it composes is
`TauCeti.MeasureTheory.Measure.Mod0MeasureIso`; this module composes the two transports and
exports the resulting theorem `exists_mpModNull_equiv_unitInterval`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped unitInterval

public section

noncomputable section

namespace MeasureTheory.Measure

/-! ### The atomless real-line isomorphism

The mod-zero isomorphism between an atomless standard-Borel probability space and Lebesgue
measure on the unit interval is the composite of the standard-Borel transport into `ℝ` with the
CDF/quantile transport along `ℝ`. -/

private def atomless_standardBorel_mod0MeasureIso (α) [MeasurableSpace α]
    [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Mod0MeasureIso α ℝ μ (volume.restrict (Set.Icc 0 1)) := by
  have hne : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hprob : IsProbabilityMeasure (Measure.map (embeddingReal α) μ) := inferInstance
  have hnull : NullSingletonClass (Measure.map (embeddingReal α) μ) :=
    noAtoms_map_of_injective (measurableEmbedding_embeddingReal α)
  exact (@embeddingRealMod0MeasureIso α _ _ μ hne).trans
    (@realMod0MeasureIso (Measure.map (embeddingReal α) μ) hprob hnull)

/-- A measure-preserving map in each direction between an atomless standard-Borel
probability space and the unit interval, with the two maps mutually inverse almost everywhere. -/
theorem exists_mpModNull_equiv_unitInterval
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ (f : Ω → I) (g : I → Ω),
      MeasurePreserving f μ (volume : Measure I) ∧
      MeasurePreserving g (volume : Measure I) μ ∧
      (∀ᵐ x ∂μ, g (f x) = x) ∧
      (∀ᵐ y ∂(volume : Measure I), f (g y) = y) :=
  mod0MeasureIso_to_unitInterval (atomless_standardBorel_mod0MeasureIso Ω μ)

end MeasureTheory.Measure
