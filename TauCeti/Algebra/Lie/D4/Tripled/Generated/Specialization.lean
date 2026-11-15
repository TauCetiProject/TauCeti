/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.BaseChange

/-!
# Specialization of the generated tripled D₄ subgroup

For any extension of commutative ground rings `R → S`, the subgroup generated over `S` by the
numbered root subgroups and weight torus is a closed subgroup of the scalar extension of the
subgroup generated over `R`. This file constructs its surjective coordinate comparison, proves
its compatibility with the ambient general-linear coordinates and all generators, and identifies
it with the existing base-change isomorphism when `S` is free over `R`.

In particular this constructs a surjection from the scalar-extended coordinate algebra of the
integral generated subgroup to the coordinate algebra of the subgroup generated over any field,
including positive characteristic. It does not prove that comparison an isomorphism for non-free
extensions: generation may impose additional equations after
specialization. Equality with the specialized integral toral closure, and identification with an
independently pinned simply connected group, are not asserted.

The construction uses the common-kernel base-change inequality and quotient maps for nested Hopf
ideals, rather than assuming flatness of the integral carrier. The generator comparisons extend
those in `TauCeti.Algebra.Lie.D4.Tripled.Generated.BaseChange`.

## Main declarations

* `generatedCoordinateHopfAlgebraBaseChangeMap`: the canonical surjection of coordinate algebras.
* `generatedCoordinateHopfAlgebraBaseChangeMap_unique`: its ambient-coordinate characterization.
* `generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift`: compatibility with
  each numbered root subgroup and the weight torus.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

open CategoryTheory

namespace TauCeti.D4Tripled

universe u v

noncomputable section

variable (R : Type u) (S : Type max u v) [CommRing R] [CommRing S] [Algebra R S]

/-- Without any flatness hypothesis, the generated subgroup over `S` is contained in the scalar
extension of the generated subgroup over `R`, expressed contravariantly on defining ideals. -/
theorem map_baseChangeHopfIdeal_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom.hom ≤
      generatedDefiningIdeal S := by
  rw [generatedDefiningIdeal_def, generatedDefiningIdeal_def]
  refine (HopfIdeal.map_mono _
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le
      (K := S) (generatorCoordinateMap R))).trans ?_
  rw [CommHopfAlgCat.map_commonKernelHopfIdeal,
    ← funext (generatorCoordinateMap_baseChange R S),
    CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective _ _ fun j ↦
      (ConcreteCategory.bijective_of_isIso
        (generatorCoordinateAlgebraBaseChangeIso R S j).hom).1]

/-- **The canonical specialization comparison.** On coordinate algebras it is a surjection from
scalar extension of the generated tripled D₄ subgroup to the subgroup generated after scalar
extension. No freeness, flatness or field hypothesis is required. -/
def generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := S) (generatedCoordinateHopfAlgebra R) ⟶
      generatedCoordinateHopfAlgebra S :=
  (CommHopfAlgCat.baseChangeIsoOfEqQuotient (generatedDefiningIdeal R)
    ((CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R)).map
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom.hom)
    (generatedCoordinateHopfAlgebra_def R) rfl
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24) rfl).hom ≫
      CommHopfAlgCat.quotientMapOfLe _
        (map_baseChangeHopfIdeal_generatedDefiningIdeal_le R S) ≫
      eqToHom (generatedCoordinateHopfAlgebra_def S).symm

/-- The comparison preserves the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫
        generatedCoordinateHopfAlgebraBaseChangeMap R S =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom ≫
        generatedCoordinateMap S := by
  rw [generatedCoordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    CommHopfAlgCat.baseChangeMap_comp_baseChangeIsoOfEqQuotient_hom _ _ _ _ _ _ _
      (CommHopfAlgCat.mkQuotient _ _)
      (generatedCoordinateMap_comp_eqToIso_hom R) (by simp)]
  simp only [Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc]
  rw [← cancel_mono (eqToHom (generatedCoordinateHopfAlgebra_def S))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    generatedCoordinateMap_comp_eqToIso_hom]

/-- The ambient-coordinate equation uniquely determines the specialization comparison. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := S) (generatedCoordinateHopfAlgebra R) ⟶
      generatedCoordinateHopfAlgebra S)
    (hf : CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom ≫
        generatedCoordinateMap S) :
    f = generatedCoordinateHopfAlgebraBaseChangeMap R S := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R))).mp
  exact hf.trans
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap
      R S).symm

/-- The specialization comparison is surjective on coordinate rings, hence defines a closed
immersion of the generated group after scalar extension into the scalar-extended group. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (generatedCoordinateHopfAlgebraBaseChangeMap R S).hom := by
  have h := (generatedCoordinateMap_surjective S).comp
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24).hom).2
  rw [← BialgHom.coe_comp, ← _root_.CommHopfAlgCat.hom_comp,
    ← baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap,
    _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at h
  exact Function.Surjective.of_comp h

/-- The specialization comparison intertwines every numbered root-subgroup and weight-torus
coordinate lift with its scalar extension, including over non-flat extensions. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift
    (j : Sum (Fin 4 ⊕ Fin 4) Unit) :
    generatedCoordinateHopfAlgebraBaseChangeMap R S ≫ generatedCoordinateLift S j =
      CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateLift R j) ≫
        (generatorCoordinateAlgebraBaseChangeIso R S j).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R))).mp
  rw [← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap,
    Category.assoc, generatedCoordinateMap_comp_generatedCoordinateLift]
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := S)).map_comp,
    generatedCoordinateMap_comp_generatedCoordinateLift]
  symm
  apply (Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 24)).mp
  rw [← Category.assoc]
  exact generatorCoordinateMap_baseChange R S j

/-- For free scalar extensions, the comparison is the existing base-change isomorphism. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_eq_iso_hom [Module.Free R S] :
    generatedCoordinateHopfAlgebraBaseChangeMap R S =
      (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom := by
  exact (generatedCoordinateHopfAlgebraBaseChangeMap_unique R S _
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom
      R S)).symm

/-- The full generated-carrier comparison intertwines each factored root or torus generator
with its scalar extension. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom
    [Module.Free R S] (j : Sum (Fin 4 ⊕ Fin 4) Unit) :
    CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateLift R j) ≫
        (generatorCoordinateAlgebraBaseChangeIso R S j).hom =
      (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom ≫ generatedCoordinateLift S j := by
  rw [← generatedCoordinateHopfAlgebraBaseChangeMap_eq_iso_hom]
  exact (generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift R S j).symm

end

end TauCeti.D4Tripled
