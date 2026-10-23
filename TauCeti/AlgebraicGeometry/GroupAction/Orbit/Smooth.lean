/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Translation
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus

/-!
# Smooth closed orbit schemes

For a reduced finite-type group scheme acting on a finite-type scheme over an
algebraically closed field, every closed orbit has a smooth scheme model. The
model is the scheme-theoretic image of the actual orbit morphism. Reducedness
descends from the group to this image; its dense smooth locus spreads to the
whole model by the orbit-closure translations. The ambient scheme need not be
reduced, irreducible or separated, and the group need not be connected.

Every orbit closure contains such a smooth closed orbit. If the ambient scheme
is proper, the resulting smooth closed orbit is proper as well. In particular,
these models supply smooth proper schemes for comparison with complex manifolds.
The orbit morphism itself is not asserted smooth: in positive characteristic
its stabilizer can be nonreduced.

The smooth-locus argument uses
`AlgebraicGeometry.Scheme.Hom.smooth_of_transitive_on_closedPoints`, which adapts the proof
underlying Mathlib's `AlgebraicGeometry.smooth_of_grpObj`, by Andrew Yang. Combine this
with `TauCeti.SchemeAction.exists_orbitClosureTranslation_eq_of_isClosed` to obtain smoothness;
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
  [IsReduced G.left]

/-- A closed orbit of a reduced finite-type group over an algebraically closed field
has a smooth scheme-theoretic image, even when the ambient scheme is nonreduced. -/
theorem smooth_orbitClosureToBase_of_isClosed (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] (hc : IsClosed (orbit G x)) :
    Smooth (orbitClosureToBase G x) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsReduced (orbitClosureScheme G x) := by
    exact IsSchemeTheoreticallyDominant.isReduced (toOrbitClosure G x)
  apply Scheme.Hom.smooth_of_transitive_on_closedPoints
  intro y hyc z hzc
  obtain ⟨g, hg⟩ := exists_orbitClosureTranslation_eq_of_isClosed G x hc hyc hzc
  exact ⟨orbitClosureTranslation G x g, orbitClosureTranslation_hom_toBase G x g, hg⟩

end TauCeti.SchemeAction
