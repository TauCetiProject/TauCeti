/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GoodReduction.Witt
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# The projective line over `ℚ` has everywhere Witt good reduction

The projective line `ℙ¹_ℤ` is smooth and proper over `Spec ℤ`, and its generic fibre is `ℙ¹_ℚ`.
Hence `ℙ¹_ℚ` has Witt good reduction at every prime
(`TauCeti.AlgebraicGeometry.projectiveLine.hasEverywhereWittGoodReduction`). Since its Hodge
number `h¹¹` is one, the vanishing of `Hʲ(X, Ωⁱ)` in low degrees for smooth proper `ℚ`-schemes
with everywhere good reduction can only hold for `i ≠ j`.

## References

* J.-M. Fontaine, *Schémas propres et lisses sur Z*, Proceedings of the Indo-French Conference on
  Geometry (Bombay, 1989), Hindustan Book Agency (1993), 43–56; Theorem 1 and Remark (a).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.projectiveLine

/-- **The projective line over `ℚ` has everywhere Witt good reduction**: it is the generic fibre
of the smooth proper `ℤ`-scheme `ℙ¹_ℤ`. -/
theorem hasEverywhereWittGoodReduction :
    HasEverywhereWittGoodReduction (projectiveLine ℚ ↘ Spec (.of ℚ)) :=
  have := SmoothOfRelativeDimension.smooth 1 (projectiveLine ℤ ↘ Spec (.of ℤ))
  .of_int _ _ (isPullback_baseChangeProjection ℤ ℚ)

end TauCeti.AlgebraicGeometry.projectiveLine
