/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Limit.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.ConeComposition

/-!
# The mapping-space criterion for limits and colimits

For a quasicategory `C`, a cone is a limit exactly when composition with it induces a weak
homotopy equivalence on each vertex fibre. Dually a cocone is a colimit exactly when
precomposition with it induces these equivalences.
The composition maps and their section factorizations are defined in
`TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.ConeComposition`.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 4.2.4.3.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite Simplicial SimplexCategory

namespace SSet

variable {K C : SSet.{u}} {p : K ⟶ C} [Quasicategory C]

namespace slice

variable (c : (slice p) _⦋0⦌)

/-- **The mapping-space criterion for limits** (HTT Lemma 4.2.4.3). For a quasicategory `C`, a cone
`c` over a diagram `p : K ⟶ C` is a limit cone exactly when, for every vertex `y` of `C`,
postcomposition with `c` is a weak homotopy equivalence from the right mapping space
`Hom^R_C(y, x)` into the cone point `x` of `c` to the fibre over `y` of the projection
`C_{/p} ⟶ C`. -/
theorem isLimit_iff_forall_isWeakHomotopyEquivalence_postcomp :
    IsLimit p c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (postcomp (π p) y c) := by
  rw [isLimit_iff]
  exact isTerminalVertex_iff_forall_isWeakHomotopyEquivalence_postcomp (π p) c

end slice

namespace coslice

variable (c : (coslice p) _⦋0⦌)

/-- **The mapping-space criterion for colimits**, dually to HTT Lemma 4.2.4.3. For a quasicategory
`C`, a cocone `c` under a diagram `p : K ⟶ C` is a colimit cocone exactly when, for every vertex
`y` of `C`, precomposition with `c` is a weak homotopy equivalence from the left mapping space
`Hom^L_C(x, y)` out of the cocone point `x` of `c` to the fibre over `y` of the projection
`C_{p/} ⟶ C`. -/
theorem isColimit_iff_forall_isWeakHomotopyEquivalence_precomp :
    IsColimit p c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (precomp (π p) c y) := by
  rw [isColimit_iff]
  exact isInitialVertex_iff_forall_isWeakHomotopyEquivalence_precomp (π p) c

end coslice

end SSet
