/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.Basic

/-!
# Arbitrary base change of the generated E₆ minuscule subgroup

For any extension `S / R` of commutative rings, the subgroup of `GL₂₇` generated over `S`
by the numbered minuscule roots and weight torus is a closed subgroup of the scalar extension
of the subgroup generated over `R`. The surjective coordinate map
`generatedCoordinateHopfAlgebraBaseChangeMap` realizes this inclusion. Its characteristic
square with the ambient general-linear quotient maps determines it uniquely, and it
intertwines every root-subgroup and weight-torus coordinate lift.

When `S` is free over `R`, this map is the existing base-change isomorphism. Without
freeness no reverse containment is asserted: specialization can introduce new equations.
In particular, this comparison does not identify the generated subgroup with the
specialization of the integral minuscule carrier or with a pinned simply connected group.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* J. S. Milne, *Algebraic Groups* (2017), §2.h.

-/

-- The construction uses `CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le` and
-- `CommHopfAlgCat.quotientBaseChangeIso`. The generator identifications and free comparison
-- are those of `TauCeti.Algebra.Lie.E6.Minuscule.Generated.Basic`.

public section

open CategoryTheory

namespace TauCeti.E6Minuscule

universe v w

noncomputable section

variable (R : Type v) (S : Type max v w) [CommRing R] [CommRing S] [Algebra R S]

/-- Arbitrary base change of the generated defining ideal is contained in the defining ideal
of the subgroup generated after base change. -/
theorem map_baseChangeHopfIdeal_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom.hom ≤
      generatedDefiningIdeal S := by
  have h := HopfIdeal.map_mono
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom.hom
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le
      (K := S) (generatorCoordinateMap R))
  rw [generatedDefiningIdeal_def]
  exact h.trans_eq (map_commonKernelHopfIdeal_baseChangeMap_generatorCoordinateMap R S)

private theorem baseChangeDefiningIdeal_le_ker_generatedCoordinateMap :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (generatedDefiningIdeal R)).toIdeal ≤
      RingHom.ker ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom ≫
        generatedCoordinateMap S).hom.toAlgHom.toRingHom := by
  have h := map_baseChangeHopfIdeal_generatedDefiningIdeal_le R S
  rw [← HopfIdeal.toIdeal_le_toIdeal, HopfIdeal.map_toIdeal,
    Ideal.map_le_iff_le_comap] at h
  intro x hx
  have hx' := h hx
  rw [Ideal.mem_comap, ← generatedCoordinateMap_ker S, RingHom.mem_ker] at hx'
  exact hx'

/-- The coordinate map of the closed immersion from the subgroup generated over `S` to the
scalar extension of the subgroup generated over `R`. No flatness hypothesis is needed. -/
def generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := S) (generatedCoordinateHopfAlgebra R) ⟶
      generatedCoordinateHopfAlgebra S :=
  -- The quotient presentation is not exposed across the `Basic` module boundary;
  -- use its public equality rather than exposing the implementation of the algebra.
  (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := S))
      (generatedCoordinateHopfAlgebra_def R))).hom ≫
    (CommHopfAlgCat.quotientBaseChangeIso (K := S) (generatedDefiningIdeal R)).inv ≫
      CommHopfAlgCat.liftQuotient _
        ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom ≫
          generatedCoordinateMap S)
        (baseChangeDefiningIdeal_le_ker_generatedCoordinateMap R S)

/-- The arbitrary-base-change comparison commutes with the ambient `GL₂₇` coordinate maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫
        generatedCoordinateHopfAlgebraBaseChangeMap R S =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom ≫
        generatedCoordinateMap S := by
  have hq : CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := S))
        (generatedCoordinateHopfAlgebra_def R))).hom =
      CommHopfAlgCat.baseChangeMap (K := S)
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R 27)
          (generatedDefiningIdeal R)) := by
    let F := CommHopfAlgCat.baseChangeFunctor (k := R) (K := S)
    rw [generatedCoordinateMap_def]
    rw [← CommHopfAlgCat.baseChangeFunctor_map, F.map_comp]
    simp only [eqToIso.hom, eqToHom_map, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
    exact CommHopfAlgCat.baseChangeFunctor_map _
  rw [generatedCoordinateHopfAlgebraBaseChangeMap, ← Category.assoc, ← Category.assoc, hq]
  rw [← CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom,
    Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient]

/-- The characteristic ambient square determines the arbitrary-base-change comparison. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := S) (generatedCoordinateHopfAlgebra R) ⟶
      generatedCoordinateHopfAlgebra S)
    (hf : CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom ≫
        generatedCoordinateMap S) :
    f = generatedCoordinateHopfAlgebraBaseChangeMap R S := by
  let q := CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R)
  let _ : Epi q := ConcreteCategory.epi_of_surjective q
    (CommHopfAlgCat.baseChangeMap_surjective _ (generatedCoordinateMap_surjective R))
  apply (cancel_epi q).mp
  exact hf.trans
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap R S).symm

/-- The comparison is surjective on coordinate algebras, hence represents a closed immersion. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (generatedCoordinateHopfAlgebraBaseChangeMap R S).hom := by
  have h := congrArg _root_.CommHopfAlgCat.Hom.hom
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap R S)
  have hsurj : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom ≫
        generatedCoordinateMap S).hom :=
    (generatedCoordinateMap_surjective S).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27).hom).2
  rw [← h, _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- Arbitrary scalar extension intertwines every numbered root and weight-torus lift. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift
    (j : Sum (Fin 6 ⊕ Fin 6) Unit) :
    generatedCoordinateHopfAlgebraBaseChangeMap R S ≫ generatedCoordinateLift S j =
      CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateLift R j) ≫
        (generatorCoordinateAlgebraBaseChangeIso R S j).hom := by
  let q := CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateMap R)
  let _ : Epi q := ConcreteCategory.epi_of_surjective q
    (CommHopfAlgCat.baseChangeMap_surjective _ (generatedCoordinateMap_surjective R))
  apply (cancel_epi q).mp
  dsimp only [q]
  rw [← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap,
    Category.assoc, generatedCoordinateMap_comp_generatedCoordinateLift,
    ← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := S)).map_comp,
    generatedCoordinateMap_comp_generatedCoordinateLift]
  exact ((Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 27)).mp
    (generatorCoordinateMap_baseChange R S j)).symm

/-- Over a free extension, the arbitrary-base-change comparison is the existing isomorphism. -/
theorem
  generatedCoordinateHopfAlgebraBaseChangeMap_eq_generatedCoordinateHopfAlgebraBaseChangeIso_hom
    [Module.Free R S] :
    generatedCoordinateHopfAlgebraBaseChangeMap R S =
      (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom :=
  (generatedCoordinateHopfAlgebraBaseChangeMap_unique R S _
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom
      R S)).symm

/-- Free scalar extension intertwines every numbered root-subgroup and weight-torus lift. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom
    [Module.Free R S] (j : Sum (Fin 6 ⊕ Fin 6) Unit) :
    CommHopfAlgCat.baseChangeMap (K := S) (generatedCoordinateLift R j) ≫
        (generatorCoordinateAlgebraBaseChangeIso R S j).hom =
      (generatedCoordinateHopfAlgebraBaseChangeIso R S).hom ≫
        generatedCoordinateLift S j := by
  rw [←
    generatedCoordinateHopfAlgebraBaseChangeMap_eq_generatedCoordinateHopfAlgebraBaseChangeIso_hom]
  exact (generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift R S j).symm

end

end TauCeti.E6Minuscule
