/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Positive.Generated.BaseChange

/-!
# Specialization of the positive generated Geck subgroup

For any extension of commutative rings, the subgroup generated after extension is a closed
subgroup of the scalar extension of the original positive generated Geck subgroup. On coordinate
algebras the comparison is surjective. It respects the ambient general-linear inclusion and each
positive numbered root subgroup and the weight torus. These comparisons are needed to specialize
the positive subgroup together with the proposed pinning, including at non-flat reductions.

For free extensions the map is the existing base-change isomorphism. Equality of the two subgroup
schemes is not asserted for arbitrary extensions, nor is an identification with the specialization
of the integral toral closure.

The construction uses the common-kernel base-change inclusion and quotient transport of
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`. The generator compatibility argument follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* B. Conrad, *Reductive Group Schemes*, §1.
-/

public section

namespace TauCeti.DynkinType

open CategoryTheory

universe v w

noncomputable section

variable (t : DynkinType) (ht : t.Valid)
variable (k : Type v) (K : Type max v w) [CommRing k] [CommRing K] [Algebra k K]

/-- The extended defining ideal is contained in the defining ideal generated after extension.
The reverse containment need not follow from arbitrary scalar extension. -/
theorem map_baseChangeHopfIdeal_geckPositiveGeneratedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K)
        (t.geckPositiveGeneratedDefiningIdeal ht k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom.hom ≤
      t.geckPositiveGeneratedDefiningIdeal ht K := by
  rw [geckPositiveGeneratedDefiningIdeal_def, geckPositiveGeneratedDefiningIdeal_def]
  refine (HopfIdeal.map_mono _
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le _)).trans_eq ?_
  rw [CommHopfAlgCat.map_commonKernelHopfIdeal]
  rw [← CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective
    (fun j ↦ (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).inv ≫
      CommHopfAlgCat.baseChangeMap (K := K) (t.geckPositiveGeneratorCoordinateMap ht k j))
    (fun j ↦ (t.geckPositiveGeneratorCoordinateAlgebraBaseChangeIso k K j).hom)
    (fun j ↦ (ConcreteCategory.bijective_of_isIso
      (t.geckPositiveGeneratorCoordinateAlgebraBaseChangeIso k K j).hom).1)]
  congr 1
  funext j
  exact t.geckPositiveGeneratorCoordinateMap_baseChange ht k K j

/-- The coordinate comparison from the scalar-extended positive subgroup to the subgroup
coordinates generated over the extension ring. Contravariantly it is a closed immersion. -/
def geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (t.geckPositiveGeneratedCoordinateHopfAlgebra ht k) ⟶
      t.geckPositiveGeneratedCoordinateHopfAlgebra ht K :=
  (CommHopfAlgCat.baseChangeIsoOfEqQuotient
    (t.geckPositiveGeneratedDefiningIdeal ht k) _
    (t.geckPositiveGeneratedCoordinateHopfAlgebra_def ht k) rfl
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)) rfl).hom ≫
    CommHopfAlgCat.quotientMapOfLe _
      (t.map_baseChangeHopfIdeal_geckPositiveGeneratedDefiningIdeal_le ht k K) ≫
    eqToHom (t.geckPositiveGeneratedCoordinateHopfAlgebra_def ht K).symm

/-- The arbitrary-extension comparison commutes with restriction from the ambient general
linear group. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_geckPositiveGeneratedCoordinateMap_comp_baseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K) (t.geckPositiveGeneratedCoordinateMap ht k) ≫
        t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom ≫
        t.geckPositiveGeneratedCoordinateMap ht K := by
  rw [geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    ← Category.assoc]
  rw [CommHopfAlgCat.baseChangeMap_comp_baseChangeIsoOfEqQuotient_hom
    (f' := CommHopfAlgCat.mkQuotient _ _)]
  · simp only [Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc]
    rw [← geckPositiveGeneratedCoordinateMap_def]
  · rw [geckPositiveGeneratedCoordinateMap_def]
    simp
  · simp

private instance epi_baseChange_geckPositiveGeneratedCoordinateMap :
    Epi (CommHopfAlgCat.baseChangeMap (K := K)
      (t.geckPositiveGeneratedCoordinateMap ht k)) :=
  ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.baseChangeMap_surjective (K := K) _
    (t.geckPositiveGeneratedCoordinateMap_surjective ht k))

/-- The ambient general-linear square uniquely determines the comparison map. -/
theorem geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K)
        (t.geckPositiveGeneratedCoordinateHopfAlgebra ht k) ⟶
      t.geckPositiveGeneratedCoordinateHopfAlgebra ht K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K) (t.geckPositiveGeneratedCoordinateMap ht k) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom ≫
        t.geckPositiveGeneratedCoordinateMap ht K) :
    f = t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (t.geckPositiveGeneratedCoordinateMap ht k))).mp
  rw [hf, baseChangeMap_geckPositiveGeneratedCoordinateMap_comp_baseChangeMap]

/-- The coordinate comparison is surjective over every commutative extension ring. -/
theorem geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K).hom := by
  unfold geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    ((CommHopfAlgCat.quotientMapOfLe_surjective _ _).comp
      (ConcreteCategory.bijective_of_isIso _).2)

/-- Over a free extension the comparison is the previously constructed isomorphism. -/
theorem geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap_eq_hom [Module.Free k K] :
    t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K =
      (t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeIso ht k K).hom := by
  symm
  apply t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap_unique ht k K
  exact t.baseChangeMap_geckPositiveGeneratedCoordinateMap_comp_baseChangeIso_hom ht k K

/-- Every positive numbered root subgroup and the weight torus are preserved by the comparison. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_geckPositiveGeneratedCoordinateLift_comp_baseChangeIso_hom
    (j : Sum (Fin t.rank) Unit) :
    CommHopfAlgCat.baseChangeMap (K := K) (t.geckPositiveGeneratedCoordinateLift ht k j) ≫
        (t.geckPositiveGeneratorCoordinateAlgebraBaseChangeIso k K j).hom =
      t.geckPositiveGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K ≫
        t.geckPositiveGeneratedCoordinateLift ht K j := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (t.geckPositiveGeneratedCoordinateMap ht k))).mp
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    geckPositiveGeneratedCoordinateMap_comp_lift]
  rw [baseChangeMap_geckPositiveGeneratedCoordinateMap_comp_baseChangeMap_assoc,
    geckPositiveGeneratedCoordinateMap_comp_lift]
  exact (Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K
    (t.geckDim ht))).mp (t.geckPositiveGeneratorCoordinateMap_baseChange ht k K j)

end

end TauCeti.DynkinType
