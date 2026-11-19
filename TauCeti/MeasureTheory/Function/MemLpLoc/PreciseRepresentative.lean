/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative

/-!
# The precise representative of a locally `Lᵖ` function

A function in `TauCeti.MemLpLoc p Ω` on an open set `Ω`, with `1 ≤ p`, is locally integrable on
`Ω`. Under a uniformly locally doubling, locally finite Borel measure on a locally compact
second-countable pseudometric space, such as an additive Haar measure on a finite-dimensional
real normed space, it therefore agrees almost everywhere on `Ω` with its precise representative
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`), by the Lebesgue differentiation theorem.
-/

public noncomputable section

open MeasureTheory TopologicalSpace TauCeti.MeasureTheory

namespace TauCeti

/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω` with
its precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative {X F : Type*} [PseudoMetricSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasureSpace X] [BorelSpace X]
    [IsUnifLocDoublingMeasure (volume : Measure X)] [IsLocallyFiniteMeasure (volume : Measure X)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ENNReal} {Ω : Opens X}
    {f : X → F} (hp : 1 ≤ p) (hu : MemLpLoc p Ω f) :
    f =ᵐ[volume.restrict Ω] preciseRepresentative volume f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

end TauCeti
