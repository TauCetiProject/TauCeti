/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Translation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

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

The smooth-locus argument adapts the proof underlying Mathlib's
`AlgebraicGeometry.smooth_of_grpObj`, by Andrew Yang, to closed orbits. It combines
`Scheme.Hom.dense_smoothLocus_of_perfectField` with
`TauCeti.SchemeAction.exists_orbitClosureTranslation_eq_of_isClosed` and the
existing closed-orbit existence theorem.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left] [LocallyOfFiniteType X.hom]
  [IsReduced G.left]

/-- A closed orbit of a reduced finite-type group over an algebraically closed field
has a smooth scheme-theoretic image, even when the ambient scheme is nonreduced. -/
theorem smooth_orbitClosureToBase_of_isClosed (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (hc : IsClosed (orbit G x)) : Smooth (orbitClosureToBase G x) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let f := orbitClosureToBase G x
  have : IsReduced (orbitClosureScheme G x) := by
    exact IsSchemeTheoreticallyDominant.isReduced (toOrbitClosure G x)
  have : JacobsonSpace (orbitClosureScheme G x) := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty (orbitClosureScheme G x) :=
    ⟨toOrbitClosure G x (η[G].left (IsLocalRing.closedPoint k))⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro h
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints h
    f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.isOpen.isLocallyClosed
  obtain ⟨g, hg⟩ := exists_orbitClosureTranslation_eq_of_isClosed G x hc hyc hzc
  have he : (orbitClosureTranslation G x g).hom ≫ f = f :=
    orbitClosureTranslation_hom_toBase G x g
  have hz' : y ∈ (orbitClosureTranslation G x g).hom ⁻¹ᵁ f.smoothLocus := by
    rw [Scheme.Hom.mem_preimage, hg]
    exact hz
  exact hy (by
    simpa only [Scheme.Hom.preimage_smoothLocus_eq, he, f, SetLike.mem_coe] using hz')

/-- Every geometric orbit closure contains a closed orbit whose scheme model is smooth. -/
theorem exists_smooth_closed_orbit_subset_orbitClosure
    [CompactSpace X.left] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      IsClosed (orbit G y) ∧ orbit G y ⊆ orbitClosure G x ∧
        Smooth (orbitClosureToBase G y) := by
  obtain ⟨y, hy, hsub⟩ := exists_isClosed_orbit_subset_orbitClosure G x
  exact ⟨y, hy, hsub, smooth_orbitClosureToBase_of_isClosed G y hy⟩

omit [LocallyOfFiniteType X.hom] in
/-- In a nonempty proper scheme, a reduced finite-type group has a smooth proper closed
orbit, with the closed immersion given by `orbitClosureι`. -/
theorem exists_smooth_proper_closed_orbit [Nonempty X.left] [IsProper X.hom] :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      IsClosed (orbit G y) ∧ Smooth (orbitClosureToBase G y) ∧
        IsProper (orbitClosureToBase G y) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  obtain ⟨y, hy⟩ := exists_isClosed_orbit G (X := X)
  exact ⟨y, hy, smooth_orbitClosureToBase_of_isClosed G y hy, inferInstance⟩

end TauCeti.SchemeAction
