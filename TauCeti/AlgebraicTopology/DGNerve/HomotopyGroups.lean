/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.RightMappingSpace
public import TauCeti.AlgebraicTopology.DoldKan.HomotopyGroups
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.ULift

/-!
# Homotopy groups of mapping spaces in the differential graded nerve

The right mapping spaces of a differential graded nerve are Kan complexes, and their
positive homotopy groups at zero are the negative cohomology groups of the DG Hom
complexes. The comparison is a group isomorphism, not just a bijection. In particular,
negative cohomology of a Hom complex is retained by the nerve even though it is invisible
in the ordinary homotopy category.

We combine the normalized-chain description of right mapping spaces with the Dold–Kan
homotopy-group comparison. The universe-lift comparison keeps the universes of objects
and morphisms independent. The base point is the preimage of zero under the Dold–Kan
mapping-space isomorphism.

## References

* J. Lurie, *Higher Algebra*, Remark 1.3.1.12.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter III, §2.
-/

public noncomputable section

open CategoryTheory Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace TauCeti.dgNerve

universe v u

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

-- Write the target as an actual simplicial module, rather than an opaque functor value,
-- to give the zero vertex a type carrying its additive structure.
private abbrev mappingDoldKanIso (X Y : C) :=
  rightMappingSpaceIsoCochainToSSet (R := R) X Y ≪≫
    SSet.uliftFunctor.mapIso (eqToIso (cochainToSSet_obj R (dgHomComplex R X Y)))

/-- Right mapping spaces of the differential graded nerve are Kan complexes. -/
instance rightMappingSpace_kanComplex (X Y : C) :
    SSet.KanComplex ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
      ((dgNerveEquiv R C).symm Y) : SSet) :=
  isFibrant_of_fibration (rightMappingSpaceIsoCochainToSSet (R := R) X Y).hom

/-- The zero base point in a right mapping space, obtained from the zero vertex of
the Dold–Kan simplicial module of the good truncation of the Hom complex. -/
def rightMappingSpaceZero (X Y : C) :
    ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
      ((dgNerveEquiv R C).symm Y) : SSet) _⦋0⦌ :=
  (mappingDoldKanIso (R := R) X Y).inv.app _ (ULift.up 0)

/-- The mapping-space comparison sends the zero base point to the zero vertex.
This explicitly transports through `cochainToSSet_obj` to access the simplicial module's zero. -/
lemma rightMappingSpaceZero_doldKan (X Y : C) :
    (SSet.uliftFunctor.mapIso (eqToIso (cochainToSSet_obj R (dgHomComplex R X Y)))).hom.app _
      ((rightMappingSpaceIsoCochainToSSet (R := R) X Y).hom.app _
        (rightMappingSpaceZero (R := R) X Y)) = ULift.up 0 := by
  exact congr($((mappingDoldKanIso (R := R) X Y).inv_hom_id).app _ (ULift.up 0))

/-- Positive homotopy groups of the right mapping space in the DG nerve are the
negative cohomology groups of the Hom complex. The base point is zero, and
homotopy degree `n + 1` corresponds to cochain degree `-(n + 1)`. -/
def rightMappingSpacePiAddEquivHomology (X Y : C) (n : ℕ) :
    Additive (SSet.KanComplex.π (n + 1)
      ((dgNerve R C).rightMappingSpace ((dgNerveEquiv R C).symm X)
        ((dgNerveEquiv R C).symm Y)) (rightMappingSpaceZero (R := R) X Y)) ≃+
      (dgHomComplex R X Y).homology (-((n + 1 : ℕ) : ℤ)) := by
  -- A typed vertex avoids unfolding the universe-lift functor during group inference.
  let z : (SSet.uliftFunctor.{u, v}.obj
      (Idempotents.DoldKan.Γ.obj
        ((dgHomComplex R X Y).truncLE' ComplexShape.embeddingDownNat) ⋙
          forget (ModuleCat R))) _⦋0⦌ := ULift.up 0
  exact ((SSet.KanComplex.π.mulEquivOfIso (mappingDoldKanIso (R := R) X Y)
      (y := z) (rightMappingSpaceZero_doldKan X Y)).trans
    (SSet.KanComplex.π.uliftMulEquiv n z)).toAdditive.trans
      ((dgHomComplex R X Y).doldKanPiAddEquivHomology n)

end TauCeti.dgNerve
