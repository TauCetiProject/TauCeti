/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.Basic

/-!
# Ambient coordinates for the positive tripled D₄ subgroup

The positive subgroup is defined inside the full generated tripled D₄ carrier. Here it is
identified with the quotient of the ambient general-linear coordinate algebra by the common
kernel of the four positive root maps and the weight-torus map. This presentation permits
scalar-extension comparisons without first identifying the full generated carriers.

The construction uses `CommHopfAlgCat.comapOfSurjective_commonKernelHopfIdeal` and
`CommHopfAlgCat.Hom.quotientIsoOfSurjective`.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
-/

public section

open CategoryTheory

namespace TauCeti.D4Tripled.Generated.Positive

noncomputable section

variable (R : Type*) [CommRing R]

/-- The ambient general-linear coordinate map of the positive tripled D₄ subgroup. -/
def coordinateMap : GeneralLinear.coordinateHopfAlgebra R 24 ⟶ coordinateHopfAlgebra R :=
  generatedCoordinateMap R ≫ CommHopfAlgCat.mkQuotient _ (definingIdeal R)

/-- The ambient coordinate map is the composite of the two closed inclusions. -/
theorem coordinateMap_def :
    coordinateMap R = generatedCoordinateMap R ≫
      CommHopfAlgCat.mkQuotient _ (definingIdeal R) := (rfl)

/-- The positive subgroup is closed in the ambient general-linear group. -/
theorem coordinateMap_surjective : Function.Surjective (coordinateMap R).hom :=
  (CommHopfAlgCat.mkQuotient_surjective _ _).comp (generatedCoordinateMap_surjective R)

/-- The factored positive generators recover their ambient general-linear coordinate maps. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_commonKernelLift (j : Fin 4 ⊕ Unit) :
    coordinateMap R ≫ CommHopfAlgCat.commonKernelLift (generator R) j =
      generatedCoordinateMap R ≫ generator R j := by
  simp only [coordinateMap_def, Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]

/-- The positive defining ideal in general-linear coordinates, rather than in the full
generated carrier's coordinates. -/
def ambientDefiningIdeal : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R 24) :=
  (definingIdeal R).comapOfSurjective (generatedCoordinateMap R).hom
    (generatedCoordinateMap_surjective R)

/-- The ambient ideal is the common kernel of the positive root and weight-torus maps. -/
theorem ambientDefiningIdeal_eq_commonKernelHopfIdeal :
    ambientDefiningIdeal R = CommHopfAlgCat.commonKernelHopfIdeal
      (fun j : Fin 4 ⊕ Unit ↦ generatedCoordinateMap R ≫ generator R j) :=
  CommHopfAlgCat.comapOfSurjective_commonKernelHopfIdeal _ _ _

/-- The ambient defining ideal is exactly the kernel of the closed inclusion's coordinate map. -/
-- The bundled-to-ring-hom coercion prevents this equation from matching under simp;
-- use it explicitly with rw.
theorem coordinateMap_ker :
    RingHom.ker (coordinateMap R).hom = (ambientDefiningIdeal R).toIdeal := by
  rw [coordinateMap_def, ambientDefiningIdeal,
    HopfIdeal.comapOfSurjective_eq_kerOfSurjective, HopfIdeal.kerOfSurjective_toIdeal]
  -- The category composite's hom is the BialgHom composite of the quotient projection
  -- with generatedCoordinateMap; coercing either composite to a ring hom is definitionally equal.
  rfl

/-- The ambient quotient presentation of the positive subgroup. -/
def ambientQuotientIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R 24)
        (ambientDefiningIdeal R) ≅ coordinateHopfAlgebra R :=
  (generatedCoordinateMap R).quotientIsoOfSurjective
    (generatedCoordinateMap_surjective R) (definingIdeal R)

/-- The ambient presentation identifies its quotient projection with the closed inclusion's
coordinate map. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_ambientQuotientIso_hom :
    CommHopfAlgCat.mkQuotient _ (ambientDefiningIdeal R) ≫ (ambientQuotientIso R).hom =
      coordinateMap R :=
  CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoOfSurjective_hom _ _ _

end

end TauCeti.D4Tripled.Generated.Positive
