/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.LineDegree

/-!
# The Arakelov degree of the line of an Arakelov divisor: examples

The line `O(D)` of an Arakelov divisor has degree `deg^(D)`; for a principal divisor this is `0`.
-/

public section

open NumberField TauCeti

namespace TauCeti.ArakelovDivisorLineDegreeExamples

/-- The line `O((f))` of a principal divisor has degree `0`. -/
example {K : Type*} [Field K] [NumberField K] (f : Additive Kˣ) :
    (ArakelovDivisor.principal K f).hermitianMetric.lineDegree = 0 := by
  simp

end TauCeti.ArakelovDivisorLineDegreeExamples
