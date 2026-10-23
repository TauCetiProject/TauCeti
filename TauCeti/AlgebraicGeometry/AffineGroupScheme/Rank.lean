/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# Rank of finite flat affine group schemes

The rank of the structural morphism of a finite flat affine group scheme equals the local rank
of its coordinate Hopf algebra. Neither commutativity of the group nor local finite presentation
is needed. The comparison uses the Hopf-spectrum anti-equivalence and `TauCeti.finrank_hopfSpec`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TauCeti

namespace TauCeti.AffineGroupSchemeCat

universe u

/-- The scheme-theoretic rank of a finite flat affine group scheme is the local rank of its
coordinate Hopf algebra. -/
@[simp]
theorem finrank_eq_rankAtStalk_coordinateHopfAlgebra (R : Type u) [CommRing R]
    (G : AffineGroupSchemeCat (CommRingCat.of R)) [IsFinite G.obj.X.hom] [Flat G.obj.X.hom]
    (x : PrimeSpectrum R) :
    G.obj.X.hom.finrank x = Module.rankAtStalk (R := R)
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse.obj G).unop x := by
  let H := ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse.obj G).unop
  -- `Grp.forget` projects a group object to its underlying object `X` in `Over`.
  let i : ((hopfSpec (CommRingCat.of R)).obj (op H)).X ≅ G.obj.X :=
    (Grp.forget _).mapIso (hopfSpecCoordinateHopfAlgebraIso R G)
  let _ : Module.Finite R H := (moduleFinite_iff_isFinite_hopfSpec R H).mpr
    ((MorphismProperty.over_iso_iff (@IsFinite) i).mpr inferInstance)
  let _ : Module.Flat R H := (moduleFlat_iff_flat_hopfSpec R H).mpr
    ((MorphismProperty.over_iso_iff (@Flat) i).mpr inferInstance)
  exact (congrFun (finrank_eq_of_nonempty_iso_over ⟨i⟩) x).symm.trans (finrank_hopfSpec R H x)

end TauCeti.AffineGroupSchemeCat
