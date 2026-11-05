/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Positive.BaseChange

/-!
# Specialization of the generated positive doubled E₆ subgroup

For any extension of commutative rings, the subgroup of `GL₅₄` generated after extension
by the six positive numbered root subgroups and weight torus lies in the scalar extension
of the subgroup generated before extension. The comparison is a surjection on coordinate
Hopf algebras, hence a closed immersion in the opposite group-scheme direction. It respects
all seven generating maps and is uniquely characterized by its ambient general-linear square.

Unlike the free-extension isomorphism, this comparison applies to reduction modulo a prime.
It supplies one direction of the comparison needed to recognize the positive subgroup after
specialization of the integral doubled minuscule carrier. Neither equality under arbitrary
scalar extension nor Borel maximality is asserted. For free extensions the comparison is the
existing isomorphism.

## Main declarations

* `generatorCodomainBaseChangeIso`: scalar extension of each positive generator's codomain.
* `map_baseChangeHopfIdeal_definingIdeal_le`: containment of the extended defining ideal.
* `coordinateHopfAlgebraBaseChangeMap`: the canonical, surjective comparison of coordinates.
* `baseChangeMap_commonKernelLift_comp_generatorCodomainBaseChangeIso_hom`:
  compatibility with every positive root and weight-torus generator.
* `coordinateHopfAlgebraBaseChangeMap_eq_iso_hom`: agreement with the free comparison.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26–28.

The generator-compatibility argument follows the full generated E₇ comparison in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`. The construction uses the
common-kernel inclusion and quotient comparison of
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule.Generated.Positive

universe v w

noncomputable section

variable (k : Type v) (K : Type max v w) [CommRing k] [CommRing K] [Algebra k K]

/-- Scalar extension of a positive root or weight-torus coordinate algebra, with source and
 target expressed in the positive generating family's own codomains. -/
def generatorCodomainBaseChangeIso (j : Fin 6 ⊕ Unit) :
    CommHopfAlgCat.baseChange (K := K) (generatorCodomain k j) ≅ generatorCodomain K j :=
  generatorCoordinateAlgebraBaseChangeIso k K (match j with
    | .inl i => .inl (.inl i)
    | .inr u => .inr u)

/-- The positive root and weight-torus coordinate maps commute with scalar extension. -/
theorem generator_baseChange (j : Fin 6 ⊕ Unit) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (generator k j) ≫
        (generatorCodomainBaseChangeIso k K j).hom = generator K j := by
  cases j with
  | inl i =>
      simpa only [generator_inl, generatorCodomainBaseChangeIso, Category.assoc] using
        generatorCoordinateMap_baseChange k K (.inl (.inl i))
  | inr u =>
      cases u
      simpa only [generator_inr, generatorCodomainBaseChangeIso, Category.assoc] using
        generatorCoordinateMap_baseChange k K (.inr ())

/-- Extension of the positive generated ideal is contained in the ideal generated after
extension. Contravariantly, the subgroup generated after extension is contained in the
scalar extension of the original subgroup. No flatness hypothesis is needed. -/
theorem map_baseChangeHopfIdeal_definingIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingIdeal k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom.hom ≤
      definingIdeal K := by
  refine (HopfIdeal.map_mono _
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le (generator k))).trans ?_
  rw [CommHopfAlgCat.map_commonKernelHopfIdeal]
  rw [← CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective
    (fun j ↦ (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).inv ≫
      CommHopfAlgCat.baseChangeMap (K := K) (generator k j))
    (fun j ↦ (generatorCodomainBaseChangeIso k K j).hom)
    (fun j ↦ (ConcreteCategory.bijective_of_isIso
      (generatorCodomainBaseChangeIso k K j).hom).1)]
  simpa only [Category.assoc, generator_baseChange] using (le_rfl : definingIdeal K ≤ _)

private theorem baseChangeDefiningIdeal_le_ker :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingIdeal k)).toIdeal ≤
      RingHom.ker ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal K)).hom.toAlgHom.toRingHom := by
  intro x hx
  have hxK := map_baseChangeHopfIdeal_definingIdeal_le k K
    (HopfIdeal.mem_map_of_mem
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom.hom hx)
  have hxI := HopfIdeal.mem_toIdeal.mpr hxK
  rw [← CommHopfAlgCat.mkQuotient_ker] at hxI
  exact hxI

/-- The coordinates of the scalar-extended positive generated subgroup map canonically onto
the coordinates generated over the extension ring. Geometrically this is a closed immersion
in the opposite direction, not an asserted isomorphism. -/
def coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k) ⟶
      coordinateHopfAlgebra K :=
  (CommHopfAlgCat.quotientBaseChangeIso (K := K) (definingIdeal k)).inv ≫
    CommHopfAlgCat.liftQuotient _
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal K))
      (baseChangeDefiningIdeal_le_ker k K)

/-- The canonical comparison respects the ambient `GL₅₄` quotient maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal k)) ≫
        coordinateHopfAlgebraBaseChangeMap k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal K) := by
  rw [coordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    ← CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient]

private instance baseChangeQuotient_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K)
      (CommHopfAlgCat.mkQuotient _ (definingIdeal k))) :=
  ConcreteCategory.epi_of_surjective _
    (CommHopfAlgCat.baseChangeMap_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _))

/-- The ambient general-linear square uniquely determines the comparison. -/
theorem coordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k) ⟶
      coordinateHopfAlgebra K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal k)) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal K)) :
    f = coordinateHopfAlgebraBaseChangeMap k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal k)))).mp
  rw [hf, baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap]

/-- The coordinate comparison is surjective, giving a closed immersion of group schemes. -/
theorem coordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (coordinateHopfAlgebraBaseChangeMap k K).hom := by
  have hsurj : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal K)).hom :=
    (CommHopfAlgCat.mkQuotient_surjective _ (definingIdeal K)).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom).2
  rw [← baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- The comparison intertwines the lifts of all six positive numbered root subgroups and
of the weight torus. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_commonKernelLift_comp_generatorCodomainBaseChangeIso_hom
    (j : Fin 6 ⊕ Unit) :
    CommHopfAlgCat.baseChangeMap (K := K) (CommHopfAlgCat.commonKernelLift (generator k) j) ≫
        (generatorCodomainBaseChangeIso k K j).hom =
      coordinateHopfAlgebraBaseChangeMap k K ≫
        CommHopfAlgCat.commonKernelLift (generator K) j := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal k)))).mp
  calc
    _ = CommHopfAlgCat.baseChangeMap (K := K) (generator k j) ≫
        (generatorCodomainBaseChangeIso k K j).hom := by
      rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
        CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
        CommHopfAlgCat.baseChangeFunctor_map]
    _ = (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generator K j :=
      (Iso.inv_comp_eq _).mp (generator_baseChange k K j)
    _ = _ := by
      rw [← Category.assoc,
        baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap,
        Category.assoc, CommHopfAlgCat.mkQuotient_comp_commonKernelLift]

/-- For a free extension the canonical comparison is the existing scalar-extension
isomorphism. In particular this includes every extension of fields. -/
theorem coordinateHopfAlgebraBaseChangeMap_eq_iso_hom [Module.Free k K] :
    coordinateHopfAlgebraBaseChangeMap k K = (coordinateHopfAlgebraBaseChangeIso k K).hom := by
  exact (coordinateHopfAlgebraBaseChangeMap_unique k K _
    (baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_hom k K)).symm

end

end TauCeti.E6DoubledMinuscule.Generated.Positive
