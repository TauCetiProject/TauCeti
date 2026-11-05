/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.Presentation
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.BaseChange

/-!
# Arbitrary base change of the positive tripled D₄ subgroup

There is a canonical surjection from scalar-extended positive coordinates to the coordinates
of the positive subgroup generated after extension. Contravariantly, the latter subgroup is
closed in the scalar extension of the former. The comparison respects the ambient GL₂₄
coordinates and each positive root and torus map, and agrees with the existing isomorphism for
free extensions. No equality after non-flat specialization is asserted.

The ambient quotient presentation allows the comparison to be constructed independently of
base-change comparisons for the full generated group. It applies, in particular, to reduction
from ℤ to a prime field.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 2.

The generator compatibility argument follows the existing tripled D₄ and E₇ free-base-change
comparisons. The construction uses the common-kernel base-change inclusion and the quotient
universal property in `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`.
-/

public section

open CategoryTheory

namespace TauCeti.D4Tripled.Generated.Positive

noncomputable section

universe v w

variable (R : Type v) (S : Type max v w) [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension of the ambient positive defining ideal is contained in the ideal of the
positive subgroup generated over the new base. -/
theorem map_baseChangeHopfIdeal_ambientDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (ambientDefiningIdeal R)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom.hom ≤
      ambientDefiningIdeal S := by
  rw [ambientDefiningIdeal_eq_commonKernelHopfIdeal,
    ambientDefiningIdeal_eq_commonKernelHopfIdeal]
  exact CommHopfAlgCat.map_baseChangeHopfIdeal_commonKernelHopfIdeal_le
    (fun j ↦ generatedCoordinateMap R ≫ generator R j)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24)
    (generatorCodomainBaseChangeIso R S) (fun j ↦ generatedCoordinateMap S ≫ generator S j)
    (fun j ↦ (Category.assoc _ _ _).trans (generatedCoordinateMap_comp_generator_baseChange R S j))

/-- The canonical comparison from scalar-extended positive coordinates to the positive
coordinates generated after extension. No freeness or flatness hypothesis is required. -/
def coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := S) (coordinateHopfAlgebra R) ⟶ coordinateHopfAlgebra S :=
  (CommHopfAlgCat.baseChangeFunctor (k := R) (K := S)).map (ambientQuotientIso R).inv ≫
    (CommHopfAlgCat.quotientBaseChangeIsoOfMapEq (ambientDefiningIdeal R)
      ((CommHopfAlgCat.baseChangeHopfIdeal (K := S) (ambientDefiningIdeal R)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom.hom)
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24) rfl).hom ≫
    CommHopfAlgCat.quotientMapOfLe _ (map_baseChangeHopfIdeal_ambientDefiningIdeal_le R S) ≫
    (ambientQuotientIso S).hom

/-- The comparison's defining ambient GL₂₄ coordinate square. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R) ≫
        coordinateHopfAlgebraBaseChangeMap R S =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom ≫ coordinateMap S := by
  let F := CommHopfAlgCat.baseChangeFunctor (k := R) (K := S)
  have hbase : CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R) ≫
      F.map (ambientQuotientIso R).inv =
        CommHopfAlgCat.baseChangeMap (K := S)
          (CommHopfAlgCat.mkQuotient _ (ambientDefiningIdeal R)) := by
    rw [← CommHopfAlgCat.baseChangeFunctor_map, ← F.map_comp]
    apply congrArg F.map
    exact (Iso.comp_inv_eq (ambientQuotientIso R)).mpr
      (mkQuotient_comp_ambientQuotientIso_hom R).symm
  rw [coordinateHopfAlgebraBaseChangeMap, ← Category.assoc, hbase]
  rw [← Category.assoc,
    CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom,
    Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc,
    mkQuotient_comp_ambientQuotientIso_hom]

private instance baseChangeCoordinateMap_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R)) :=
  ConcreteCategory.epi_of_surjective _
    (CommHopfAlgCat.baseChangeMap_surjective (K := S) _ (coordinateMap_surjective R))

/-- The ambient coordinate square uniquely determines the comparison. -/
theorem coordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := S) (coordinateHopfAlgebra R) ⟶
      coordinateHopfAlgebra S)
    (hf : CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom ≫ coordinateMap S) :
    f = coordinateHopfAlgebraBaseChangeMap R S := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R))).mp
  rw [hf, baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeMap]

/-- The subgroup generated after extension is closed in the scalar-extended positive subgroup. -/
theorem coordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (coordinateHopfAlgebraBaseChangeMap R S).hom := by
  have hsurj : Function.Surjective
      (CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R) ≫
        coordinateHopfAlgebraBaseChangeMap R S).hom := by
    rw [baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeMap]
    exact (coordinateMap_surjective S).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom).2
  exact Function.Surjective.of_comp hsurj

/-- Every positive numbered root and the weight torus commute with the comparison. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_commonKernelLift_comp_generatorCodomainBaseChangeIso_hom
    (j : Fin 4 ⊕ Unit) :
    CommHopfAlgCat.baseChangeMap (K := S) (CommHopfAlgCat.commonKernelLift (generator R) j) ≫
        (generatorCodomainBaseChangeIso R S j).hom =
      coordinateHopfAlgebraBaseChangeMap R S ≫
        CommHopfAlgCat.commonKernelLift (generator S) j := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S) (coordinateMap R))).mp
  rw [baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeMap_assoc]
  rw [coordinateMap_comp_commonKernelLift]
  rw [← Category.assoc, ← CommHopfAlgCat.baseChangeFunctor_map,
    ← CommHopfAlgCat.baseChangeFunctor_map, ← Functor.map_comp,
    coordinateMap_comp_commonKernelLift, CommHopfAlgCat.baseChangeFunctor_map]
  exact (Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24)).mp
    (generatedCoordinateMap_comp_generator_baseChange R S j)

/-- For free extensions the canonical comparison is the existing base-change isomorphism. -/
theorem coordinateHopfAlgebraBaseChangeMap_eq_baseChangeIso_hom [Module.Free R S] :
    coordinateHopfAlgebraBaseChangeMap R S = (coordinateHopfAlgebraBaseChangeIso R S).hom := by
  symm
  apply coordinateHopfAlgebraBaseChangeMap_unique
  simp only [coordinateMap_def]
  rw [← CommHopfAlgCat.baseChangeFunctor_map, Functor.map_comp]
  simp only [Category.assoc]
  rw [baseChangeMap_mkQuotient_comp_baseChangeIso_hom,
    ← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom]
  simp only [Category.assoc]

end

end TauCeti.D4Tripled.Generated.Positive
