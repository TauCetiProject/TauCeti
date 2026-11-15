/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine
public import TauCeti.Geometry.Toric.Algebraic.Fan.Point
public import TauCeti.Geometry.Toric.Analytic.Fan.Compact
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Proper

/-!
# Compactness and properness of the projective-line fan realization

The two standard rank-one rays cover the real line. The completeness criterion therefore makes
their regular fan's analytic realization compact, as expected of the projective line. The collapse
of this fan to the zero-dimensional fan is proper because the source realization is compact and
the target realization is Hausdorff.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.3--3.4.
-/

public section

namespace TauCeti.Toric

/-- The analytic map from the projective-line fan to a point is proper. -/
theorem isProperMap_analyticMap_projectiveLineFan_toPoint :
    IsProperMap
      (projectiveLineFan.toPoint.analyticMap isRegular_projectiveLineFan
        isRegular_pointFan) :=
  projectiveLineFan.toPoint.isProperMap_analyticMap_of_isComplete isRegular_projectiveLineFan
    isRegular_pointFan isComplete_projectiveLineFan

/-- The analytic realization of the standard complete rank-one fan is compact. -/
theorem compactSpace_projectiveLineFan_analyticRealization :
    CompactSpace (projectiveLineFan.analyticRealization isRegular_projectiveLineFan) :=
  projectiveLineFan.compactSpace_analyticRealization_of_isComplete
    isRegular_projectiveLineFan isComplete_projectiveLineFan

end TauCeti.Toric
