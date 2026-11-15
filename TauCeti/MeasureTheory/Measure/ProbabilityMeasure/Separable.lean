/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Separable
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakDensity

/-!
# Second countability of the weak probability-measure space

On a second-countable Borel pseudometrizable space with standard Borel measurable structure,
the space of probability measures is separable for weak convergence.
`TauCeti.WassersteinSpace.separableSpace` supplies a separable finite-first-moment space;
`TauCeti.WassersteinSpace.denseRange_toProbabilityMeasure` supplies its weakly dense inclusion.
Mathlib's Lévy–Prokhorov metrization then gives second countability. The Giry measurable structure
therefore agrees with the weak Borel structure, without any moment restriction on the laws.

These instances allow weak lower semicontinuity to imply Giry measurability for functionals
on all probability laws, including infinite-valued transport distances.
-/

public section

open MeasureTheory TopologicalSpace

namespace MeasureTheory.ProbabilityMeasure

variable {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X]

/-- Probability laws on a second-countable standard Borel pseudometrizable space form a separable
space for the weak topology, with no moment hypothesis. -/
instance instSeparableSpace : SeparableSpace (ProbabilityMeasure X) := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have := TauCeti.WassersteinSpace.separableSpace (X := X) (p := 1) (by simp)
  exact TauCeti.WassersteinSpace.denseRange_toProbabilityMeasure (X := X) (p := 1)
    |>.separableSpace TauCeti.WassersteinSpace.continuous_toProbabilityMeasure

/-- The weak topology on probability laws over a second-countable standard Borel pseudometrizable
space is second countable. -/
instance instSecondCountableTopology : SecondCountableTopology (ProbabilityMeasure X) := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ProbabilityMeasure X)
  exact UniformSpace.secondCountable_of_separable _

end MeasureTheory.ProbabilityMeasure
