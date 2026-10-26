/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Spectrum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Real spectral sets of partial linear maps

The real points of the spectrum of a partial operator on a complex Banach space
form a closed subset of `ℝ`, and hence a Borel measurable set. This permits
real spectral sets to be used in measure-theoretic constructions without
assuming that the operator is bounded or self-adjoint.

The statements use the preimage under `Complex.ofReal`, so they can be used
without choosing a separate definition of the real spectrum.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/ResolventOpen.lean`
in the Kitware DKPS formalization.
-/

public section

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The real points of the spectrum of a partial operator on a complex Banach
space form a closed set. -/
theorem isClosed_preimage_ofReal_spectrum (A : E →ₗ.[ℂ] E) :
    IsClosed (Complex.ofReal ⁻¹' A.spectrum) :=
  A.isClosed_spectrum.preimage Complex.continuous_ofReal

/-- The real points of the spectrum of a partial operator on a complex Banach
space form a Borel measurable subset of `ℝ`. -/
theorem measurableSet_preimage_ofReal_spectrum (A : E →ₗ.[ℂ] E) :
    MeasurableSet (Complex.ofReal ⁻¹' A.spectrum) :=
  (A.isClosed_preimage_ofReal_spectrum).measurableSet

end LinearPMap
