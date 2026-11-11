/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Positive.BaseChange

/-!
# Arbitrary specialization of the generated positive E₇ subgroup

For every extension of commutative rings `R → S`, the subgroup generated over `S` by the
seven positive numbered roots and the weight torus is a closed subgroup of the scalar
extension of the subgroup generated over `R`. The coordinate comparison is surjective,
is uniquely determined by its ambient `GL₅₆` square, and respects every generating map.
When `S` is free over `R`, it is the existing base-change isomorphism.

The comparison applies in particular to reduction modulo a prime. It does not assert that
formation of the positive subgroup commutes with non-flat specialization, or identify it
with the Borel of an independently pinned simply connected group.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 17.
* The generator compatibility argument follows the generated-carrier comparison in
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule.Generated.Positive

universe u

attribute [local instance high] Algebra.toModule

noncomputable section

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The specialized positive generators kill the scalar extension of the original defining
ideal. Contravariantly, the subgroup generated after extension lies in the extended subgroup. -/
theorem map_baseChange_definingIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (definingIdeal R)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom.hom ≤
      definingIdeal S := by
  have h := HopfIdeal.map_mono
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom.hom
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le (K := S) (generator R))
  rw [CommHopfAlgCat.map_commonKernelHopfIdeal] at h
  rw [← CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective
    (fun j ↦ (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).inv ≫
      CommHopfAlgCat.baseChangeMap (K := S) (generator R j))
    (fun j ↦ (generatorCoordinateAlgebraBaseChangeIso R S (match j with
      | .inl i => .inl (.inl i)
      | .inr u => .inr u)).hom)
    (fun j ↦ (ConcreteCategory.bijective_of_isIso
      (generatorCoordinateAlgebraBaseChangeIso R S (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u)).hom).1)] at h
  convert h using 1
  unfold definingIdeal
  congr 1
  funext j
  symm
  cases j with
  | inl i =>
      simpa only [Category.assoc, generator_inl] using
        generatorCoordinateMap_baseChange R S (.inl (.inl i))
  | inr u =>
      obtain rfl := Subsingleton.elim u ()
      simpa only [Category.assoc, generator_inr] using
        generatorCoordinateMap_baseChange R S (.inr ())

/-- Restriction from the scalar-extended positive subgroup to the subgroup generated after
extension. On group schemes its direction is the opposite closed immersion. -/
def coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := S) (coordinateHopfAlgebra R) ⟶
      coordinateHopfAlgebra S :=
  (CommHopfAlgCat.quotientBaseChangeIsoOfMapEq (definingIdeal R)
    ((CommHopfAlgCat.baseChangeHopfIdeal (K := S) (definingIdeal R)).map
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom.hom)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56) rfl).hom ≫
    CommHopfAlgCat.quotientMapOfLe _ (map_baseChange_definingIdeal_le R S)

/-- The comparison is characterized on the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := S)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal R)) ≫
        coordinateHopfAlgebraBaseChangeMap R S =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal S) := by
  rw [coordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom,
    Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]

private instance : Epi (CommHopfAlgCat.baseChangeMap (K := S)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R))) :=
  ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.baseChangeMap_surjective _
    (CommHopfAlgCat.mkQuotient_surjective _ _))

/-- There is only one coordinate comparison with the specified ambient square. -/
theorem coordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := S) (coordinateHopfAlgebra R) ⟶
      coordinateHopfAlgebra S)
    (hf : CommHopfAlgCat.baseChangeMap (K := S)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal R)) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal S)) :
    f = coordinateHopfAlgebraBaseChangeMap R S := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)))).mp
  rw [hf, baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap]

/-- The coordinate comparison is surjective, hence defines a closed immersion of group
schemes, without any flatness hypothesis. -/
theorem coordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (coordinateHopfAlgebraBaseChangeMap R S).hom := by
  rw [coordinateHopfAlgebraBaseChangeMap, _root_.CommHopfAlgCat.hom_comp,
    BialgHom.coe_comp]
  exact (CommHopfAlgCat.quotientMapOfLe_surjective _ _).comp
    (ConcreteCategory.bijective_of_isIso _).2

/-- Every numbered positive root and the weight torus commute with the comparison. -/
@[reassoc (attr := simp)]
theorem coordinateHopfAlgebraBaseChangeMap_comp_commonKernelLift (j : Fin 7 ⊕ Unit) :
    coordinateHopfAlgebraBaseChangeMap R S ≫
        CommHopfAlgCat.commonKernelLift (generator S) j =
      CommHopfAlgCat.baseChangeMap (K := S)
          (CommHopfAlgCat.commonKernelLift (generator R) j) ≫
        (generatorCoordinateAlgebraBaseChangeIso R S (match j with
          | .inl i => .inl (.inl i)
          | .inr u => .inr u)).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := S)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal R)))).mp
  rw [baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap_assoc,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  have hcomp : CommHopfAlgCat.baseChangeMap (K := S)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal R)) ≫
        CommHopfAlgCat.baseChangeMap (K := S)
          (CommHopfAlgCat.commonKernelLift (generator R) j) =
      CommHopfAlgCat.baseChangeMap (K := S) (generator R j) := by
    rw [← CommHopfAlgCat.baseChangeFunctor_map, ← CommHopfAlgCat.baseChangeFunctor_map,
      ← Functor.map_comp, CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
      CommHopfAlgCat.baseChangeFunctor_map]
  rw [← Category.assoc, hcomp]
  symm
  apply (Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R S 56)).mp
  cases j with
  | inl i =>
      simpa only [Category.assoc, generator_inl] using
        generatorCoordinateMap_baseChange R S (.inl (.inl i))
  | inr u =>
      obtain rfl := Subsingleton.elim u ()
      simpa only [Category.assoc, generator_inr] using
        generatorCoordinateMap_baseChange R S (.inr ())

/-- For free extensions the comparison is the existing base-change isomorphism. -/
theorem coordinateHopfAlgebraBaseChangeMap_eq_iso_hom [Module.Free R S] :
    coordinateHopfAlgebraBaseChangeMap R S = (coordinateHopfAlgebraBaseChangeIso R S).hom := by
  symm
  exact coordinateHopfAlgebraBaseChangeMap_unique R S _
    (baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_hom R S)

end

end TauCeti.E7Minuscule.Generated.Positive
