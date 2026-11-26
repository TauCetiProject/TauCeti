/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Multiplication by Schwartz functions on Schwartz functions in `H^s(ℝⁿ)`

Multiplication by a scalar Schwartz function `φ` on the Bessel-potential space `H^s(E, F)`
(`BesselPotentialSpace.smulLeftCLM`) extends the pointwise multiplication of Schwartz functions
(`SchwartzMap.smulLeftCLM`) along the inclusion `SchwartzMap.toBesselPotentialSpaceCLM`.

## Main results

* `BesselPotentialSpace.smulLeftCLM_toBesselPotentialSpaceCLM`: `φ` times the image of a Schwartz
  function `f` in `H^s` is the image of the Schwartz function `φ f`.
-/

public section

open scoped SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

/-- Multiplication by a Schwartz function `φ` on `H^s` extends the pointwise multiplication of
Schwartz functions. -/
@[simp]
theorem smulLeftCLM_toBesselPotentialSpaceCLM (s : ℝ) (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    smulLeftCLM s φ (SchwartzMap.toBesselPotentialSpaceCLM s 2 f) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 (SchwartzMap.smulLeftCLM F (φ : E → ℂ) f) :=
  ext (by simp [TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq])

end BesselPotentialSpace
