/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.MeasureTheory.Function.MemLpLoc.Coordinates

/-!
# Precise representatives of locally `Lᵖ` functions

On an open set `Ω` with a locally finite uniformly locally doubling Borel measure, a locally `Lᵖ`
function with `1 ≤ p` agrees almost everywhere on `Ω` with its precise representative
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`), and if its coordinates in a finite basis have
continuous precise representatives on `Ω`, its precise representative is the basis combination of
those coordinatewise precise representatives (`Module.Basis.eqOn_preciseRepresentative_sum_repr`).
-/

public noncomputable section

open MeasureTheory TopologicalSpace TauCeti.MeasureTheory

namespace TauCeti

/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω`
with its precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative {E F : Type*} [PseudoMetricSpace E]
    [SecondCountableTopology E] [LocallyCompactSpace E] [MeasureSpace E] [BorelSpace E]
    [IsUnifLocDoublingMeasure (volume : Measure E)] [IsLocallyFiniteMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ENNReal} {Ω : Opens E} {f : E → F} (hp : 1 ≤ p) (hu : MemLpLoc p Ω f) :
    f =ᵐ[volume.restrict Ω] preciseRepresentative volume f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

end TauCeti

namespace Module.Basis

open TauCeti

variable {E F : Type*} [PseudoMetricSpace E] [SecondCountableTopology E] [LocallyCompactSpace E]
  [MeasureSpace E] [BorelSpace E] [IsUnifLocDoublingMeasure (volume : Measure E)]
  [IsLocallyFiniteMeasure (volume : Measure E)] [(volume : Measure E).IsOpenPosMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] {p : ENNReal}
  {Ω : Opens E} {f : E → F}

/-- On an open set `Ω`, the precise representative of a locally `Lᵖ` map, `1 ≤ p`, whose
coordinates in a finite basis `b` have precise representatives continuous on `Ω`, is the
combination of those precise representatives with the vectors of `b`. -/
theorem eqOn_preciseRepresentative_sum_repr (b : Module.Basis ι ℝ F) (hp : 1 ≤ p)
    (hf : MemLpLoc p Ω f)
    (hc : ∀ i, ContinuousOn (preciseRepresentative volume fun z => b.repr (f z) i) Ω) :
    Set.EqOn (preciseRepresentative volume f)
      (fun z => ∑ i, preciseRepresentative volume (fun w => b.repr (f w) i) z • b i) Ω := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hf.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) ?_
    (continuousOn_finsetSum _ fun i _ => (hc i).smul continuousOn_const)
  have hcoord : ∀ i, (fun z => b.repr (f z) i) =ᵐ[volume.restrict Ω]
      preciseRepresentative volume fun z => b.repr (f z) i := fun i =>
    (b.memLpLoc_iff.1 hf i).ae_eq_preciseRepresentative hp
  filter_upwards [ae_all_iff.2 hcoord] with z hz
  conv_lhs => rw [← b.sum_repr (f z)]
  exact Finset.sum_congr rfl fun i _ => by rw [← hz i]

end Module.Basis
