/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coordinatewise precise representatives of locally `Lᵖ` functions

On an open set `Ω` with a locally finite uniformly locally doubling Borel measure `μ`, if the
coordinates of a locally `Lᵖ` map (`1 ≤ p`) in a finite basis have continuous precise
representatives on `Ω`, then its precise representative is the basis combination of those
coordinatewise precise representatives (`Module.Basis.eqOn_preciseRepresentative_sum_repr`).
-/

public noncomputable section

open MeasureTheory TopologicalSpace TauCeti.MeasureTheory

namespace Module.Basis

open TauCeti

variable {X F : Type*} [PseudoMetricSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsUnifLocDoublingMeasure μ]
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] {p : ENNReal}
  {Ω : Opens X} {f : X → F}

/-- On an open set `Ω`, the precise representative of a locally `Lᵖ` map, `1 ≤ p`, whose
coordinates in a finite basis `b` have precise representatives continuous on `Ω`, is the
combination of those precise representatives with the vectors of `b`. -/
theorem eqOn_preciseRepresentative_sum_repr (b : Module.Basis ι ℝ F) (hp : 1 ≤ p)
    (hf : MemLpLoc p Ω f μ)
    (hc : ∀ i, ContinuousOn (preciseRepresentative μ fun z => b.repr (f z) i) Ω) :
    Set.EqOn (preciseRepresentative μ f)
      (fun z => ∑ i, preciseRepresentative μ (fun w => b.repr (f w) i) z • b i) Ω := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hf.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) ?_
    (continuousOn_finsetSum _ fun i _ => (hc i).smul continuousOn_const)
  have hcoord : ∀ i, (fun z => b.repr (f z) i) =ᵐ[μ.restrict Ω]
      preciseRepresentative μ fun z => b.repr (f z) i := fun i =>
    (b.memLpLoc_iff.1 hf i).ae_eq_preciseRepresentative hp
  filter_upwards [ae_all_iff.2 hcoord] with z hz
  conv_lhs => rw [← b.sum_repr (f z)]
  exact Finset.sum_congr rfl fun i _ => by rw [← hz i]

end Module.Basis
