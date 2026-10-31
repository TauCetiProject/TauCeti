/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme
public import TauCeti.AlgebraicGeometry.GroupAction.ClosedOrbit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper orbit schemes

For a finite-type group scheme acting on a proper scheme over an algebraically
closed field, an orbit scheme is proper exactly when its geometric orbit is closed.
The inclusion of a closed orbit is a closed immersion, so properness holds for the
actual locally closed orbit model, not just its scheme-theoretic closure.
Every orbit closure consequently contains a proper orbit scheme.

The group need not be reduced, smooth or connected. When it is reduced, the
smoothness instance in `TauCeti.AlgebraicGeometry.GroupAction.Orbit.Smooth` makes
these proper orbit schemes smooth as well. Properness here is algebraic; no
compactness assertion about the Zariski topology substitutes for properness or
for a comparison with complex points.

The construction uses `TauCeti.SchemeAction.orbitScheme` and the closed-orbit
existence theorem, together with Mathlib's closed-immersion criterion and
`AlgebraicGeometry.IsProper.of_comp` for a separated target.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., §1.8, the closed-orbit lemma.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

section FiniteType

variable [LocallyOfFiniteType X.hom] [CompactSpace X.left]

/-- The orbit model is a closed subscheme exactly when the full geometric orbit is closed. -/
@[simp]
theorem isClosedImmersion_orbitι_iff :
    IsClosedImmersion (orbitι G x) ↔ IsClosed (orbit G x) := by
  rw [IsClosedImmersion.iff_isPreimmersion, range_orbitι]
  exact and_iff_right (inferInstance : IsPreimmersion (orbitι G x))

/-- A proper orbit in a separated scheme has closed geometric image. Properness of the
ambient scheme is not required for this direction. -/
theorem isClosed_orbit_of_isProper [IsSeparated X.hom] [IsProper (orbitToBase G x)] :
    IsClosed (orbit G x) := by
  have : IsProper (orbitι G x ≫ X.hom) := by
    rw [← orbitToBase_def]
    infer_instance
  have : IsProper (orbitι G x) := IsProper.of_comp (orbitι G x) X.hom
  rw [← range_orbitι]
  exact (orbitι G x).isClosedMap.isClosed_range

end FiniteType

section Proper

variable [IsProper X.hom]

local instance : CompactSpace X.left :=
  QuasiCompact.compactSpace_of_compactSpace X.hom

/-- A closed orbit in a proper scheme is proper, with its actual orbit scheme structure.
No reducedness assumption on the acting group or the ambient scheme is needed. -/
theorem isProper_orbitToBase_of_isClosed
    (hx : IsClosed (orbit G x)) : IsProper (orbitToBase G x) := by
  have : IsClosedImmersion (orbitι G x) := (isClosedImmersion_orbitι_iff G x).mpr hx
  rw [orbitToBase_def]
  infer_instance

/-- In a proper ambient scheme, an orbit scheme is proper exactly when the geometric
orbit is closed. This does not assert properness of arbitrary locally closed orbits. -/
@[simp]
theorem isProper_orbitToBase_iff :
    IsProper (orbitToBase G x) ↔ IsClosed (orbit G x) :=
  ⟨fun _ ↦ isClosed_orbit_of_isProper G x, isProper_orbitToBase_of_isClosed G x⟩

/-- Every orbit closure in a proper scheme contains a proper orbit scheme, embedded as
an actual closed subscheme of the ambient scheme. The chosen orbit need not be unique. -/
theorem exists_isProper_orbit_subset_orbitClosure :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      IsProper (orbitToBase G y) ∧ IsClosedImmersion (orbitι G y) ∧
        Set.range (orbitι G y) ⊆ orbitClosure G x := by
  obtain ⟨y, hy, hsub⟩ := exists_isClosed_orbit_subset_orbitClosure G x
  exact ⟨y, isProper_orbitToBase_of_isClosed G y hy,
    (isClosedImmersion_orbitι_iff G y).mpr hy, (range_orbitι G y).symm ▸ hsub⟩

end Proper

end TauCeti.SchemeAction
