/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Scheme
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Translation
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus

/-!
# Smooth orbit schemes

For a reduced finite-type group scheme acting on a finite-type scheme over an
algebraically closed field, every locally closed orbit has a smooth scheme model.
The model is the locally closed scheme image of the actual orbit morphism;
for closed orbits the entire scheme-theoretic image is smooth. Reducedness descends
from the group to this image; the dense smooth locus of the orbit scheme spreads
to the whole model by translations. The ambient scheme need not be
reduced, irreducible or separated, and the group need not be connected.

Every orbit closure contains such a smooth closed orbit. If the ambient scheme
is proper, the resulting smooth closed orbit is proper as well. In particular,
these models supply smooth proper schemes for comparison with complex manifolds.
The orbit morphism itself is not asserted smooth: in positive characteristic
its stabilizer can be nonreduced.

The smooth-locus argument uses
`AlgebraicGeometry.Scheme.Hom.smooth_of_transitive_on_closedPoints`, which adapts the proof
underlying Mathlib's `AlgebraicGeometry.smooth_of_grpObj`, by Andrew Yang. Combine this
with transitivity of equivariant immersions into an orbit to obtain smoothness;
the existing closed-orbit existence theorems then supply smooth closed orbits.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

/-- A reduced immersed scheme lying in one orbit is smooth when the ambient translations
lift to automorphisms of that scheme. -/
theorem smooth_of_equivariant_of_range_subset_orbit
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) {Y : Scheme.{u}} (i : Y ⟶ X.left)
    [IsImmersion i] [IsReduced Y] (hrange : Set.range i ⊆ orbit G x)
    (e : (𝟙_ (Over (Spec (.of k))) ⟶ G) → (Y ≅ Y))
    (he : ∀ g, (e g).hom ≫ i = i ≫ (translation X g).hom.left) :
    Smooth (i ≫ X.hom) := by
  apply Scheme.Hom.smooth_of_transitive_on_closedPoints
  intro y hy z hz
  obtain ⟨g, hg⟩ := exists_eq_of_equivariant_of_range_subset_orbit G x i hrange e he hy hz
  refine ⟨e g, ?_, hg⟩
  rw [← Category.assoc, he, Category.assoc, Over.w]

/-- Every orbit scheme of a reduced finite-type group over an algebraically closed field
is smooth. The stabilizer and orbit morphism need not be smooth. -/
instance [CompactSpace G.left] [CompactSpace X.left] [IsReduced G.left]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) : Smooth (orbitToBase G x) := by
  rw [orbitToBase_def]
  exact smooth_of_equivariant_of_range_subset_orbit G x (orbitι G x)
    (range_orbitι G x).le (orbitTranslation G x) (orbitTranslation_hom_ι G x)

/-- A closed orbit of a reduced finite-type group over an algebraically closed field
has a smooth scheme-theoretic image, even when the ambient scheme is nonreduced. -/
theorem smooth_orbitClosureToBase_of_isClosed [IsReduced G.left] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] (hc : IsClosed (orbit G x)) :
    Smooth (orbitClosureToBase G x) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsReduced (orbitClosureScheme G x) := by
    exact IsSchemeTheoreticallyDominant.isReduced (toOrbitClosure G x)
  rw [orbitClosureToBase_def]
  exact smooth_of_equivariant_of_range_subset_orbit G x (orbitClosureι G x)
    (range_orbitClosureι_of_isClosed G x hc).le (orbitClosureTranslation G x)
    (orbitClosureTranslation_hom_ι G x)

end TauCeti.SchemeAction
