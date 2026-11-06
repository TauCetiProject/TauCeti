/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange

/-!
# The generated E₇ subgroup under arbitrary base change

For any algebra of commutative rings `R → S`, the subgroup generated over `S` by the numbered
root subgroups and weight torus is a closed subgroup of the base change of the subgroup generated
over `R`. Its coordinate map is the surjection `generatedCoordinateBaseChangeMap`, characterized
by its compatibility with the ambient general-linear quotient maps.

This direction requires no flatness or freeness, so it applies to reduction of the integral
carrier modulo a prime. Under free base change the map agrees with the existing coordinate
isomorphism. Equality of the two subgroups under arbitrary base change is a separate question.

## Main declarations

* `TauCeti.E7Minuscule.generatedCoordinateBaseChangeMap`: the coordinate comparison.
* `TauCeti.E7Minuscule.generatedCoordinateBaseChangeMap_surjective`: the comparison defines a
  closed immersion.
* `TauCeti.E7Minuscule.generatedCoordinateBaseChangeMap_eq_iso_hom`: agreement with the free
  base-change comparison.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

universe u

attribute [local instance high] Algebra.toModule

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The base change of the defining Hopf ideal lies in the defining Hopf ideal of the subgroup
generated over `S`. -/
theorem map_baseChange_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom.hom ≤
      generatedDefiningIdeal S := by
  rw [generatedDefiningIdeal_def, generatedDefiningIdeal_def]
  exact CommHopfAlgCat.map_baseChangeHopfIdeal_commonKernelHopfIdeal_le
    (generatorCoordinateMap R) (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56)
    (generatorCoordinateAlgebraBaseChangeIso R S) (generatorCoordinateMap S)
    (fun j ↦ by simpa only [Category.assoc] using generatorCoordinateMap_baseChange R S j)

private theorem baseChangeDefiningIdeal_le_ker :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R)).toIdeal ≤
      RingHom.ker ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom ≫
        generatedCoordinateMap S).hom.toAlgHom.toRingHom := by
  intro x hx
  have h := map_baseChange_generatedDefiningIdeal_le R S
    (HopfIdeal.mem_map_of_mem
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom.hom hx)
  rw [← HopfIdeal.mem_toIdeal, ← generatedCoordinateMap_ker] at h
  simpa only [RingHom.mem_ker, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom,
    AlgHom.comp_toRingHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    BialgHom.coe_toAlgHom] using h

/-- The coordinate map from the base-changed generated carrier to the carrier generated over
the new ring. It is defined for every algebra of commutative rings. -/
noncomputable def generatedCoordinateBaseChangeMap :
    CommHopfAlgCat.baseChange (K := S) (generatedCoordinateHopfAlgebra R) ⟶
      generatedCoordinateHopfAlgebra S :=
  (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := S))
    (generatedCoordinateHopfAlgebra_def R))).hom ≫
  (CommHopfAlgCat.quotientBaseChangeIso (K := S) (generatedDefiningIdeal R)).inv ≫
  CommHopfAlgCat.liftQuotient
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R))
    ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom ≫
      generatedCoordinateMap S) (baseChangeDefiningIdeal_le_ker R S)

/-- The arbitrary base-change comparison commutes with the ambient quotient maps. -/
@[simp]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫
        generatedCoordinateBaseChangeMap R S =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom ≫
        generatedCoordinateMap S := by
  rw [generatedCoordinateBaseChangeMap, ← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_eqToIso_hom R S,
    ← CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, CommHopfAlgCat.mkQuotient_comp_liftQuotient]

/-- The coordinate comparison is surjective, so the newly generated group is a closed subgroup
of the base change of the original generated group. -/
theorem generatedCoordinateBaseChangeMap_surjective :
    Function.Surjective (generatedCoordinateBaseChangeMap R S).hom := by
  intro y
  obtain ⟨x, hx⟩ := generatedCoordinateMap_surjective S y
  obtain ⟨z, hz⟩ :=
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom).2 x
  refine ⟨(CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R)).hom z, ?_⟩
  have h := congrArg (fun f ↦ f.hom z)
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateBaseChangeMap R S)
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, hz, hx] using h

/-- The ambient quotient square uniquely determines the generated coordinate comparison. -/
theorem generatedCoordinateBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := S) (generatedCoordinateHopfAlgebra R) ⟶
      generatedCoordinateHopfAlgebra S)
    (hf : CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom ≫
        generatedCoordinateMap S) :
    f = generatedCoordinateBaseChangeMap R S := by
  let : Epi (CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R)) :=
    ConcreteCategory.epi_of_surjective _
      (CommHopfAlgCat.baseChangeMap_surjective _ (generatedCoordinateMap_surjective R))
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R))).mp
  rw [hf, baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateBaseChangeMap]

/-- Under free base change, the canonical surjection is the existing coordinate isomorphism. -/
theorem generatedCoordinateBaseChangeMap_eq_iso_hom [Module.Free R S] :
    generatedCoordinateBaseChangeMap R S =
      (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom :=
  (generatedCoordinateBaseChangeMap_unique R S _
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom
      R S)).symm

end TauCeti.E7Minuscule
