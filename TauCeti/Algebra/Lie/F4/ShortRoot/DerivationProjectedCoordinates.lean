/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationHomogeneousPart
public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate
/-!
# Coordinates of homogeneous derivation projections

Projection to one root-lattice degree preserves the vanishing of both coordinate systems used in
the derivation splitting.
-/

public section

namespace TauCeti.F4ShortRoot
universe u
variable {R : Type u} [CommRing R]

/-- Quotient coordinates remain zero after projection to one degree. -/
theorem quotientCoordinate_homogeneousPart_eq_zero {X : Matrix (Fin 26) (Fin 26) R}
    (hq : ∀ p, quotientCoordinate p X = 0) (d : Fin 4 → ℤ) (p : Fin 26) :
    quotientCoordinate p (homogeneousPart d X) = 0 := by
  have h := quotientCoordinate_entries hq p
  fin_cases p <;>
    simp [quotientCoordinate_def, homogeneousPart, coordinateCoeff, coordinateRow, coordinateCol,
      entryDegree_self] at h ⊢ <;>
    grind

/-- Private ideal coordinates remain zero after projection to one degree. -/
theorem ideal_homogeneousPart_eq_zero {X : Matrix (Fin 26) (Fin 26) R}
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) (d : Fin 4 → ℤ) (a : Fin 26) :
    homogeneousPart d X (idealRow a) (idealCol a) = 0 := by
  simp [homogeneousPart, hi]
end TauCeti.F4ShortRoot
