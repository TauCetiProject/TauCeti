/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine
public import TauCeti.Geometry.Toric.Analytic.Fan.Compact

/-!
# Compactness of the projective-line fan realization

The two standard rank-one rays cover the real line. The completeness criterion therefore makes
their regular fan's analytic realization compact, as expected of the projective line.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
-/

public section

namespace TauCeti.Toric

/-- The analytic realization of the standard complete rank-one fan is compact. -/
theorem compactSpace_projectiveLineFan_analyticRealization :
    CompactSpace (projectiveLineFan.analyticRealization isRegular_projectiveLineFan) :=
  projectiveLineFan.compactSpace_analyticRealization_of_isComplete
    isRegular_projectiveLineFan isComplete_projectiveLineFan

end TauCeti.Toric
