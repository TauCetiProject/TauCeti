/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Generated.Basic

/-!
# Arbitrary base change of the generated Geck subgroup

The subgroup generated over an extension ring by the numbered Geck root subgroups and weight
torus is a closed subgroup of the scalar extension of the subgroup generated over the original
ring. Its coordinate map `TauCeti.DynkinType.geckGeneratedCoordinateHopfAlgebraBaseChangeMap`
is surjective, is characterized by its ambient general-linear coordinate square, and preserves
every generating coordinate lift. For free extensions it is the existing base-change isomorphism.

The comparison applies to non-flat specialization, in particular reduction from the integers to
a prime field. It does not assert equality of the two subgroup schemes under arbitrary base
change, nor identify either with a pinned simply connected group scheme. The construction uses
the common-kernel base-change inclusion and the universal property of Hopf-ideal quotients.
The generator compatibility argument follows the relative E₇ minuscule comparison in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

universe v w

variable (t : DynkinType) (ht : t.Valid)
variable (k : Type v) (K : Type max v w) [CommRing k] [CommRing K] [Algebra k K]

/-- The subgroup generated after scalar extension lies in the scalar extension of the generated
Geck subgroup. This inclusion need not be an equality for a non-flat extension. -/
theorem map_baseChangeHopfIdeal_geckGeneratedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (t.geckGeneratedDefiningIdeal ht k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom.hom ≤
      t.geckGeneratedDefiningIdeal ht K := by
  rw [t.geckGeneratedDefiningIdeal_def ht k]
  exact (HopfIdeal.map_mono _
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le _)).trans_eq
      (t.map_commonKernelHopfIdeal_geckGeneratorCoordinateMap_baseChange ht k K)

/-- The canonical coordinate surjection from the scalar extension of the generated Geck group
to the group generated after extension. Contravariantly, it is a closed subgroup inclusion. -/
noncomputable def geckGeneratedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (t.geckGeneratedCoordinateHopfAlgebra ht k) ⟶
      t.geckGeneratedCoordinateHopfAlgebra ht K :=
  CommHopfAlgCat.baseChangeMapOfLeQuotient (t.geckGeneratedDefiningIdeal ht k)
    (t.geckGeneratedDefiningIdeal ht K) (t.geckGeneratedCoordinateHopfAlgebra_def ht k)
    (t.geckGeneratedCoordinateHopfAlgebra_def ht K)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht))
    (t.map_baseChangeHopfIdeal_geckGeneratedDefiningIdeal_le ht k K)

/-- The arbitrary-extension comparison preserves the closed immersion into the general-linear
group. This square characterizes the comparison. -/
@[reassoc (attr := simp)]
theorem
  baseChangeMap_geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K) (t.geckGeneratedCoordinateMap ht k) ≫
        t.geckGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom ≫
        t.geckGeneratedCoordinateMap ht K := by
  apply CommHopfAlgCat.baseChangeMap_comp_baseChangeMapOfLeQuotient
  all_goals simp [geckGeneratedCoordinateMap_def]

private noncomputable instance baseChangeGeckGeneratedCoordinateMap_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K) (t.geckGeneratedCoordinateMap ht k)) :=
  ConcreteCategory.epi_of_surjective _
    (CommHopfAlgCat.baseChangeMap_surjective _ (t.geckGeneratedCoordinateMap_surjective ht k))

/-- The ambient coordinate square uniquely determines the generated Geck comparison. -/
theorem geckGeneratedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (t.geckGeneratedCoordinateHopfAlgebra ht k) ⟶
      t.geckGeneratedCoordinateHopfAlgebra ht K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K) (t.geckGeneratedCoordinateMap ht k) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom ≫
        t.geckGeneratedCoordinateMap ht K) :
    f = t.geckGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (t.geckGeneratedCoordinateMap ht k))).mp
  rw [hf,
    baseChangeMap_geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateHopfAlgebraBaseChangeMap]

/-- The comparison is surjective on coordinate rings, hence defines a closed immersion in the
opposite direction on affine group schemes. -/
theorem geckGeneratedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (t.geckGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K).hom := by
  have h := congrArg (fun f ↦ f.hom)
    (t.baseChangeMap_geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateHopfAlgebraBaseChangeMap
      ht k K)
  have hs : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom ≫
        t.geckGeneratedCoordinateMap ht K).hom :=
    (t.geckGeneratedCoordinateMap_surjective ht K).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht)).hom).2
  rw [← h] at hs
  exact Function.Surjective.of_comp hs

/-- The comparison intertwines every numbered root-subgroup and weight-torus coordinate lift. -/
@[reassoc (attr := simp)]
theorem geckGeneratedCoordinateHopfAlgebraBaseChangeMap_comp_geckGeneratedCoordinateLift
    (j : Sum (Fin t.rank ⊕ Fin t.rank) Unit) :
    t.geckGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K ≫
        t.geckGeneratedCoordinateLift ht K j =
      CommHopfAlgCat.baseChangeMap (K := K) (t.geckGeneratedCoordinateLift ht k j) ≫
        (t.geckGeneratorCoordinateAlgebraBaseChangeIso k K j).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (t.geckGeneratedCoordinateMap ht k))).mp
  have hsquare :=
    t.baseChangeMap_geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateHopfAlgebraBaseChangeMap
      ht k K
  rw [← Category.assoc, hsquare, Category.assoc,
    geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateLift]
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    geckGeneratedCoordinateMap_comp_geckGeneratedCoordinateLift]
  exact ((Iso.inv_comp_eq
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (t.geckDim ht))).mp
      (t.geckGeneratorCoordinateMap_baseChange ht k K j)).symm

/-- For a free extension the arbitrary-extension comparison is the existing coordinate
isomorphism, so no second comparison is introduced in that case. -/
theorem geckGeneratedCoordinateHopfAlgebraBaseChangeMap_eq_hom [Module.Free k K] :
    t.geckGeneratedCoordinateHopfAlgebraBaseChangeMap ht k K =
      (t.geckGeneratedCoordinateHopfAlgebraBaseChangeIso ht k K).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (t.geckGeneratedCoordinateMap ht k))).mp
  simp

end TauCeti.DynkinType
