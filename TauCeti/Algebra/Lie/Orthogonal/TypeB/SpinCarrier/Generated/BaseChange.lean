/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Basic

/-!
# Arbitrary base change of the generated type-B spin group

For any extension of commutative rings, the subgroup generated after extension by the
numbered spin root subgroups and weight torus lies in the scalar extension of the subgroup
generated before extension. This file constructs the corresponding surjection of coordinate
Hopf algebras and characterizes it by its ambient general-linear square. Every generating
map commutes with this comparison. For free extensions it is the existing comparison
isomorphism.

In particular the construction applies to specialization from the integers to a prime field,
where freeness is unavailable. It does not assert equality of the two subgroups in that case,
or identify either subgroup with an independently pinned simply connected group.

The quotient comparison follows the free-extension construction in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`, using instead the
unconditional common-kernel ideal inclusion from
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`.

## References

* B. Conrad, *Reductive Group Schemes*, §1 (base change of affine group schemes).
* R. Steinberg, *Lectures on Chevalley Groups*, §3 (root-generated groups).
-/

public section

open CategoryTheory

namespace TauCeti.TypeBSpinCarrier

universe v w

variable (n : ℕ) (k : Type v) (K : Type max v w)
  [CommRing k] [CommRing K] [Algebra k K]

/-- The subgroup generated over the extension ring lies in the scalar extension of the
subgroup generated over the ground ring. No flatness assumption is needed. -/
theorem map_baseChangeHopfIdeal_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom ≤
      generatedDefiningIdeal n K := by
  rw [generatedDefiningIdeal_def, generatedDefiningIdeal_def]
  exact CommHopfAlgCat.map_baseChangeHopfIdeal_commonKernelHopfIdeal_le
    (generatorCoordinateMap n k)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n))
    (generatorCoordinateAlgebraBaseChangeIso n k K) (generatorCoordinateMap n K)
    (generatorCoordinateMap_baseChange n k K)

private theorem baseChange_generatedDefiningIdeal_le_ker :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n k)).toIdeal ≤
      RingHom.ker ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n K).hom.toAlgHom.toRingHom := by
  intro x hx
  have hmem := map_baseChangeHopfIdeal_generatedDefiningIdeal_le n k K
    (HopfIdeal.mem_map_of_mem
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom hx)
  rw [← HopfIdeal.mem_toIdeal, ← generatedCoordinateMap_ker] at hmem
  -- The kernel of the composite evaluates the quotient map on the transported ambient element.
  exact hmem

/-- The coordinate comparison from the scalar extension of the generated spin group to the
group generated over the extension ring. Contravariantly this is a closed subgroup inclusion. -/
noncomputable def generatedBaseChangeComparison :
    CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n k) ⟶
      generatedCoordinateHopfAlgebra n K :=
  (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
      (generatedCoordinateHopfAlgebra_def n k))).hom ≫
    (CommHopfAlgCat.quotientBaseChangeIso (K := K) (generatedDefiningIdeal n k)).inv ≫
      CommHopfAlgCat.liftQuotient
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n k))
        ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
          generatedCoordinateMap n K) (baseChange_generatedDefiningIdeal_le_ker n k K)

/-- The comparison preserves the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedBaseChangeComparison :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n k) ≫
        generatedBaseChangeComparison n k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n K := by
  let F := CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)
  have hbase :
      CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n k) ≫
          (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
            (generatedCoordinateHopfAlgebra_def n k))).hom =
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra k (dimension n))
            (generatedDefiningIdeal n k)) := by
    calc
      _ = F.map (generatedCoordinateMap n k) ≫
          F.map (eqToIso (generatedCoordinateHopfAlgebra_def n k)).hom := by
        rw [CommHopfAlgCat.baseChangeFunctor_map]
        congr 1
        simpa only [eqToIso.hom] using
          (eqToHom_map F (generatedCoordinateHopfAlgebra_def n k)).symm
      _ = F.map (generatedCoordinateMap n k ≫
          (eqToIso (generatedCoordinateHopfAlgebra_def n k)).hom) :=
        (F.map_comp _ _).symm
      _ = _ := by
        rw [generatedCoordinateMap_comp_eqToIso_hom, CommHopfAlgCat.baseChangeFunctor_map]
  rw [generatedBaseChangeComparison, ← Category.assoc, hbase,
    ← CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, CommHopfAlgCat.mkQuotient_comp_liftQuotient]

private instance :
    Epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n k)) :=
  ConcreteCategory.epi_of_surjective _
    (CommHopfAlgCat.baseChangeMap_surjective (K := K) _
      (generatedCoordinateMap_surjective n k))

/-- The ambient square uniquely determines the generated-group comparison. -/
theorem generatedBaseChangeComparison_unique
    (g : CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n k) ⟶
      generatedCoordinateHopfAlgebra n K)
    (hg : CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n k) ≫ g =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n K) :
    g = generatedBaseChangeComparison n k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n k))).mp
  exact hg.trans
    (baseChangeMap_generatedCoordinateMap_comp_generatedBaseChangeComparison n k K).symm

/-- The coordinate comparison is surjective, so the group generated after extension is a closed
subgroup of the scalar extension of the group generated before extension. -/
theorem generatedBaseChangeComparison_surjective :
    Function.Surjective (generatedBaseChangeComparison n k K).hom := by
  have hsurj : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n K).hom :=
    (generatedCoordinateMap_surjective n K).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom).2
  rw [← baseChangeMap_generatedCoordinateMap_comp_generatedBaseChangeComparison n k K,
    _root_.CommHopfAlgCat.hom_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- Each numbered root-subgroup and weight-torus map commutes with the comparison. -/
@[reassoc (attr := simp)]
theorem generatedBaseChangeComparison_comp_generatedCoordinateLift
    (j : (Fin (n + 1) ⊕ Fin (n + 1)) ⊕ Unit) :
    generatedBaseChangeComparison n k K ≫ generatedCoordinateLift n K j =
      CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateLift n k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso n k K j).hom := by
  let F := CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n k))).mp
  rw [← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_generatedBaseChangeComparison,
    Category.assoc, generatedCoordinateMap_comp_generatedCoordinateLift]
  calc
    _ = CommHopfAlgCat.baseChangeMap (K := K) (generatorCoordinateMap n k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso n k K j).hom :=
      ((Iso.inv_comp_eq
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n))).mp
          (generatorCoordinateMap_baseChange n k K j)).symm
    _ = _ := by
      rw [← generatedCoordinateMap_comp_generatedCoordinateLift n k j,
        ← CommHopfAlgCat.baseChangeFunctor_map, F.map_comp]
      exact Category.assoc _ _ _

/-- For a free extension, the arbitrary-ring comparison is the existing base-change
isomorphism. -/
theorem generatedBaseChangeComparison_eq_iso_hom [Module.Free k K] :
    generatedBaseChangeComparison n k K =
      (generatedCoordinateHopfAlgebraBaseChangeIso n k K).hom := by
  symm
  apply generatedBaseChangeComparison_unique
  exact baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom
    n k K

/-- Generation commutes with free extensions; the comparison is then an isomorphism. -/
instance [Module.Free k K] : IsIso (generatedBaseChangeComparison n k K) := by
  rw [generatedBaseChangeComparison_eq_iso_hom]
  infer_instance

end TauCeti.TypeBSpinCarrier
