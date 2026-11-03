/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Basic

/-!
# Arbitrary base change of the generated type-D spin subgroup

For any extension of commutative rings `k → K`, the subgroup generated over `K` by the
numbered spin root subgroups and weight torus lies inside the base change of the subgroup
generated over `k`. Contravariantly, this gives a canonical surjective coordinate morphism.
Its square with the ambient general-linear quotient characterizes it uniquely, and it
respects every generator. For free extensions it is the existing base-change isomorphism.

In particular the comparison applies to non-flat specializations such as `ℤ → 𝔽₂`. No reverse
containment is asserted for an arbitrary extension. Neither generated subgroup is identified
here with the pinned simply connected group scheme of type D.

The construction uses `CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le` and
`CommHopfAlgCat.quotientBaseChangeIso`. The quotient-presentation transport follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open CategoryTheory

universe v w

variable (n : ℕ) (hn : 4 ≤ n)
variable (k : Type v) (K : Type max v w) [CommRing k] [CommRing K] [Algebra k K]

/-- Under arbitrary scalar extension, the generated subgroup is contained in the scalar
extension of the original generated subgroup. -/
theorem map_baseChangeHopfIdeal_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n hn k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom ≤
      generatedDefiningIdeal n hn K := by
  rw [generatedDefiningIdeal_def, generatedDefiningIdeal_def]
  exact CommHopfAlgCat.map_baseChangeHopfIdeal_commonKernelHopfIdeal_le
    (generatorCoordinateMap n hn k)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n))
    (generatorCoordinateAlgebraBaseChangeIso n k K) (generatorCoordinateMap n hn K)
    (generatorCoordinateMap_baseChange n hn k K)

private theorem baseChangeDefiningIdeal_le_ker :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n hn k)).toIdeal ≤
      RingHom.ker (((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n hn K).hom.toAlgHom.toRingHom) := by
  intro x hx
  have hx' := HopfIdeal.mem_toIdeal.mpr ((HopfIdeal.map_le_iff.mp
    (map_baseChangeHopfIdeal_generatedDefiningIdeal_le n hn k K)) hx)
  rw [← generatedCoordinateMap_ker] at hx'
  simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    BialgHom.coe_toAlgHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] using hx'

/-- The canonical coordinate morphism from the scalar extension of the generated spin subgroup
to the subgroup generated after scalar extension. Geometrically it is a closed immersion in
the opposite direction. -/
noncomputable def generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n hn k) ⟶
      generatedCoordinateHopfAlgebra n hn K :=
  (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
    (generatedCoordinateHopfAlgebra_def n hn k))).hom ≫
    (CommHopfAlgCat.quotientBaseChangeIso (K := K) (generatedDefiningIdeal n hn k)).inv ≫
    CommHopfAlgCat.liftQuotient _
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n hn K) (baseChangeDefiningIdeal_le_ker n hn k K)

private theorem baseChangeMap_generatedCoordinateMap_comp_presentation :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k) ≫
        (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
          (generatedCoordinateHopfAlgebra_def n hn k))).hom =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (generatedDefiningIdeal n hn k)) := by
  let F := CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)
  have htransport :
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
        (generatedCoordinateHopfAlgebra_def n hn k))).hom =
      F.map (eqToIso (generatedCoordinateHopfAlgebra_def n hn k)).hom := by
    simpa only [eqToIso.hom] using
      (eqToHom_map F (generatedCoordinateHopfAlgebra_def n hn k)).symm
  rw [htransport, ← CommHopfAlgCat.baseChangeFunctor_map, ← F.map_comp,
    generatedCoordinateMap_comp_eqToIso_hom, CommHopfAlgCat.baseChangeFunctor_map]

/-- The arbitrary-base-change comparison respects the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k) ≫
        generatedCoordinateHopfAlgebraBaseChangeMap n hn k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n hn K := by
  have hquot := CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom
    (K := K) (generatedDefiningIdeal n hn k)
  have hinv :
      CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient _ (generatedDefiningIdeal n hn k)) ≫
          (CommHopfAlgCat.quotientBaseChangeIso (K := K)
            (generatedDefiningIdeal n hn k)).inv =
        CommHopfAlgCat.mkQuotient _
          (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n hn k)) :=
    (Iso.comp_inv_eq _).mpr hquot.symm
  rw [generatedCoordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_presentation, ← Category.assoc, hinv,
    _root_.CommHopfAlgCat.mkQuotient_comp_liftQuotient]

private instance baseChangeGeneratedCoordinateMap_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k)) :=
  ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.baseChangeMap_surjective _
    (generatedCoordinateMap_surjective n hn k))

/-- The ambient general-linear square uniquely determines the comparison morphism. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n hn k) ⟶
      generatedCoordinateHopfAlgebra n hn K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n hn K) :
    f = generatedCoordinateHopfAlgebraBaseChangeMap n hn k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (generatedCoordinateMap n hn k))).mp
  rw [hf, baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap]

/-- The comparison is surjective on coordinates, so the corresponding subgroup map is closed.
No flatness of the extension is required. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (generatedCoordinateHopfAlgebraBaseChangeMap n hn k K).hom := by
  have hsurj := (generatedCoordinateMap_surjective n hn K).comp
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom).2
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨(CommHopfAlgCat.baseChangeMap (K := K)
    (generatedCoordinateMap n hn k)).hom x, ?_⟩
  -- Evaluate the ambient square at a preimage of the target coordinate.
  exact (congrArg (fun f ↦ f.hom x)
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap
      n hn k K)).trans hx

/-- The arbitrary-base-change comparison respects every numbered root-subgroup and weight-torus
coordinate lift. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift
    (j : (Fin n ⊕ Fin n) ⊕ Unit) :
    generatedCoordinateHopfAlgebraBaseChangeMap n hn k K ≫ generatedCoordinateLift n hn K j =
      CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateLift n hn k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso n k K j).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (generatedCoordinateMap n hn k))).mp
  rw [← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap,
    Category.assoc, generatedCoordinateMap_comp_generatedCoordinateLift,
    ← Category.assoc]
  let F := CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)
  rw [← CommHopfAlgCat.baseChangeFunctor_map,
    ← CommHopfAlgCat.baseChangeFunctor_map, ← F.map_comp,
    generatedCoordinateMap_comp_generatedCoordinateLift, CommHopfAlgCat.baseChangeFunctor_map]
  exact ((Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K
    (dimension n))).mp (generatorCoordinateMap_baseChange n hn k K j)).symm

/-- For a free extension, the arbitrary comparison is the existing base-change isomorphism. -/
theorem generatedCoordinateHopfAlgebraBaseChangeIso_hom_eq [Module.Free k K] :
    (generatedCoordinateHopfAlgebraBaseChangeIso n hn k K).hom =
      generatedCoordinateHopfAlgebraBaseChangeMap n hn k K :=
  generatedCoordinateHopfAlgebraBaseChangeMap_unique n hn k K _
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom
      n hn k K)

end TauCeti.TypeDSpinCarrier
