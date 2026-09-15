/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationHomogeneousClassification
public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationProjectedCoordinates

/-! # Graded injectivity for type-F4 derivations -/

public section

namespace TauCeti.F4ShortRoot
universe u
variable {R : Type u} [CommRing R] [CharP R 2]

/-- A derivation whose quotient and ideal coordinates vanish is zero. -/
theorem eq_zero_of_isDerivation_graded {X : Matrix (Fin 26) (Fin 26) R}
    (hX : IsDerivation X) (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  ext i j
  let d := entryDegree i j
  let Y := homogeneousPart d X
  have hY : Y = 0 := eq_zero_of_isHomogeneous_entryDegree i j
    (hX.homogeneousPart d) (isHomogeneous_homogeneousPart d X)
    (quotientCoordinate_homogeneousPart_eq_zero hq d)
    (ideal_homogeneousPart_eq_zero hi d)
  have hij := congrFun (congrFun hY i) j
  simpa [Y, d, homogeneousPart] using hij

end TauCeti.F4ShortRoot
