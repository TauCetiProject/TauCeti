/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Compact operators on a complex Hilbert space as a C⋆-algebra

For a complex Hilbert space `H`, the closed nonunital `⋆`-subalgebra
`TauCeti.compactOperatorStarSubalgebra ℂ H` of compact operators in `H →L[ℂ] H` inherits a
`NonUnitalCStarAlgebra` structure from `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap` and a
`PartialOrder` (the Loewner order) from `Mathlib.Analysis.InnerProductSpace.StarOrder`. This file
registers the `StarOrderedRing` instance via Mathlib's `Subtype.starOrderedRing`, making
`compactOperatorStarSubalgebra ℂ H` directly usable as a coefficient C⋆-algebra for `CStarModule`
and spectral-order arguments without pulling C⋆-algebra or continuous functional calculus imports
into `TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint`.

## Main declarations

* `TauCeti.instStarOrderedRingCompactOperatorStarSubalgebra`: `StarOrderedRing` instance on
  `TauCeti.compactOperatorStarSubalgebra ℂ H` under the Loewner order inherited from `H →L[ℂ] H`.
-/

public section

namespace TauCeti

/-- For a complex Hilbert space `H`, `compactOperatorStarSubalgebra ℂ H` is a `StarOrderedRing`
under the Loewner order inherited from `H →L[ℂ] H`. -/
noncomputable instance instStarOrderedRingCompactOperatorStarSubalgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    StarOrderedRing (compactOperatorStarSubalgebra ℂ H) :=
  Subtype.starOrderedRing (𝕜 := ℂ) (compactOperatorStarSubalgebra ℂ H)

end TauCeti
