/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.Boundary
public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex

/-!
# Initial vertices of the differential graded nerve

An object whose outgoing Hom complexes are exact in nonpositive cohomological degrees
is an initial vertex of the differential graded nerve. These degrees control the homotopy
groups of its outgoing mapping spaces. In particular, vanishing outgoing Hom complexes
suffice. Together with the terminal-vertex criterion, this constructs zero objects without
replacing mapping spaces by sets of homotopy classes.

The obstruction to extending a simplex boundary starting at `X` is a cycle in an outgoing
Hom complex of `X`. Exactness makes it a boundary, supplying the missing coherence. As in
the terminal-vertex criterion, the construction uses `DGNerve.exists_coherences_of_faces`
and `DGNerve.Coherences.exists_simplex_iff_of_boundary`.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.12.
* J. Lurie, *Higher Topos Theory*, §1.2.12.
-/

public section

open CategoryTheory Limits Finset Simplicial SSet

namespace TauCeti.dgNerve

open DGNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-- Exactness of every outgoing Hom complex in nonpositive degrees makes an object initial
in the dg nerve. No condition is imposed in positive cohomological degrees. -/
theorem isInitialVertex_of_exactAt {X : C}
    (h : ∀ (Y : C) (d : ℤ), d ≤ 0 → (dgHomComplex R X Y).ExactAt d) :
    (dgNerve R C).IsInitialVertex ((dgNerveEquiv R C).symm X) := by
  rw [SSet.isInitialVertex_iff]
  intro n σ₀ hσ₀
  have hX := congrArg (dgNerveEquiv R C) hσ₀
  rw [dgNerveEquiv_apply, Equiv.apply_symm_apply] at hX
  apply exists_extension_of_exactAt
  intro hn
  rw [hX]
  exact h _ _ (by omega)

/-- An object with zero outgoing Hom complexes is initial in the dg nerve. -/
theorem isInitialVertex_of_isZero {X : C} (h : ∀ Y : C, IsZero (dgHomComplex R X Y)) :
    (dgNerve R C).IsInitialVertex ((dgNerveEquiv R C).symm X) :=
  isInitialVertex_of_exactAt fun Y d _ ↦
    HomologicalComplex.ExactAt.of_isZero ((HomologicalComplex.eval _ _ d).map_isZero (h Y))

end TauCeti.dgNerve
