/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.Basic

/-!
# Arbitrary base change of the generated doubled E₆ subgroup

The subgroup generated over an extension ring by the numbered roots and weight torus is a
closed subgroup of the scalar extension of the generated subgroup. The coordinate comparison
constructed here is surjective, commutes with the ambient `GL₅₄` coordinate maps, and respects
every generator. For free extensions it agrees with the existing base-change isomorphism.

In particular the comparison is available for specialization from ℤ to a prime field. Neither
its injectivity nor agreement with the specialized integral toral closure is asserted.

The construction uses `CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le` and the
quotient universal property. The generator compatibility argument follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.RelativeBaseChange`.

## References

* B. Conrad, *Reductive Group Schemes*, §1 (base change and closed subgroup schemes).
* J. S. Milne, *Algebraic Groups*, Chapter 2 (affine groups and their coordinate algebras).
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

universe u v

variable (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K]

/-- Under arbitrary scalar extension, the subgroup generated over the extension ring is
contained in the scalar extension of the generated subgroup. -/
theorem map_baseChangeHopfIdeal_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom.hom ≤
      generatedDefiningIdeal K := by
  rw [generatedDefiningIdeal_def, generatedDefiningIdeal_def]
  refine (HopfIdeal.map_mono _
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le
      (K := K) (generatorCoordinateMap k))).trans_eq ?_
  rw [CommHopfAlgCat.map_commonKernelHopfIdeal]
  rw [← CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective
    (fun j ↦ (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).inv ≫
      CommHopfAlgCat.baseChangeMap (generatorCoordinateMap k j))
    (fun j ↦ (generatorCoordinateAlgebraBaseChangeIso k K j).hom)
    fun j ↦ (ConcreteCategory.bijective_of_isIso
      (generatorCoordinateAlgebraBaseChangeIso k K j).hom).1]
  congr 1
  funext j
  exact generatorCoordinateMap_baseChange k K j

private theorem baseChangeDefiningIdeal_le_comparison_ker :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal k)).toIdeal ≤
      RingHom.ker ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K).hom.toAlgHom.toRingHom := by
  have h := HopfIdeal.toIdeal_le_toIdeal.mpr
    (map_baseChangeHopfIdeal_generatedDefiningIdeal_le k K)
  rw [HopfIdeal.map_toIdeal, Ideal.map_le_iff_le_comap] at h
  intro x hx
  apply RingHom.mem_ker.mpr
  have hx' : (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom.hom x ∈
      (generatedDefiningIdeal K).toIdeal := h hx
  have hz : (generatedCoordinateMap K).hom
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom.hom x) = 0 := by
    apply RingHom.mem_ker.mp
    rwa [generatedCoordinateMap_ker K]
  rw [_root_.CommHopfAlgCat.hom_comp]
  exact hz

/-- The coordinate comparison from the scalar extension of the generated doubled E₆ subgroup
to the subgroup generated over the extension ring. Contravariantly this is a closed immersion;
no flatness assumption on the extension is needed. -/
noncomputable def generatedCoordinateHopfAlgebraBaseChangeHom :
    CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra k) ⟶
      generatedCoordinateHopfAlgebra K :=
  (CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)).map
      (eqToHom (generatedCoordinateHopfAlgebra_def k)) ≫
    (CommHopfAlgCat.quotientBaseChangeIso (K := K) (generatedDefiningIdeal k)).inv ≫
    CommHopfAlgCat.liftQuotient
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal k))
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K) (baseChangeDefiningIdeal_le_comparison_ker k K)

/-- The arbitrary-extension comparison commutes with the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeHom :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k) ≫
        generatedCoordinateHopfAlgebraBaseChangeHom k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K := by
  let F := CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)
  have hbase :
      CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k) ≫
          F.map (eqToHom (generatedCoordinateHopfAlgebra_def k)) =
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient _ (generatedDefiningIdeal k)) := by
    rw [← CommHopfAlgCat.baseChangeFunctor_map, ← F.map_comp,
      generatedCoordinateMap_comp_eqToHom, CommHopfAlgCat.baseChangeFunctor_map]
  have hquot :
      CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient _ (generatedDefiningIdeal k)) ≫
          (CommHopfAlgCat.quotientBaseChangeIso (K := K) (generatedDefiningIdeal k)).inv =
        CommHopfAlgCat.mkQuotient _
          (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal k)) := by
    rw [← cancel_mono
      (CommHopfAlgCat.quotientBaseChangeIso (K := K) (generatedDefiningIdeal k)).hom]
    simp
  rw [generatedCoordinateHopfAlgebraBaseChangeHom, ← Category.assoc, hbase,
    ← Category.assoc, hquot, _root_.CommHopfAlgCat.mkQuotient_comp_liftQuotient]

private instance baseChangedGeneratedCoordinateMap_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k)) :=
  ConcreteCategory.epi_of_surjective _
    (CommHopfAlgCat.baseChangeMap_surjective _ (generatedCoordinateMap_surjective k))

/-- The ambient coordinate square uniquely determines the arbitrary-extension comparison. -/
theorem generatedCoordinateHopfAlgebraBaseChangeHom_unique
    (f : CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra k) ⟶
      generatedCoordinateHopfAlgebra K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K) :
    f = generatedCoordinateHopfAlgebraBaseChangeHom k K := by
  apply (cancel_epi
    (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k))).mp
  rw [hf, baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeHom]

/-- The arbitrary-extension comparison is surjective on coordinate algebras, hence represents
a closed immersion of affine group schemes. -/
theorem generatedCoordinateHopfAlgebraBaseChangeHom_surjective :
    Function.Surjective (generatedCoordinateHopfAlgebraBaseChangeHom k K).hom := by
  have hsurj : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K).hom :=
    (generatedCoordinateMap_surjective K).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom).2
  rw [← baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeHom]
    at hsurj
  exact Function.Surjective.of_comp hsurj

/-- Every numbered root-subgroup and weight-torus coordinate lift commutes with the
arbitrary-extension comparison. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom
    (j : Sum (Fin 6 ⊕ Fin 6) Unit) :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateLift k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso k K j).hom =
      generatedCoordinateHopfAlgebraBaseChangeHom k K ≫ generatedCoordinateLift K j := by
  let F := CommHopfAlgCat.baseChangeFunctor (k := k) (K := K)
  apply (cancel_epi
    (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k))).mp
  calc
    _ = CommHopfAlgCat.baseChangeMap (K := K) (generatorCoordinateMap k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso k K j).hom := by
      rw [← Category.assoc, ← CommHopfAlgCat.baseChangeFunctor_map,
        ← CommHopfAlgCat.baseChangeFunctor_map, ← F.map_comp,
        generatedCoordinateMap_comp_generatedCoordinateLift]
    _ = (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatorCoordinateMap K j :=
      (Iso.inv_comp_eq (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54)).mp
        (generatorCoordinateMap_baseChange k K j)
    _ = _ := by
      rw [
        baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeHom_assoc,
        generatedCoordinateMap_comp_generatedCoordinateLift]

/-- For free extensions, the arbitrary-extension comparison is the existing isomorphism's
forward morphism. This is a rewriting lemma rather than a simp rule, so that inverse
cancellation for the isomorphism remains available to the simplifier. -/
theorem generatedCoordinateHopfAlgebraBaseChangeIso_hom_eq [Module.Free k K] :
    (generatedCoordinateHopfAlgebraBaseChangeIso k K).hom =
      generatedCoordinateHopfAlgebraBaseChangeHom k K :=
  generatedCoordinateHopfAlgebraBaseChangeHom_unique k K _
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom k K)

end TauCeti.E6DoubledMinuscule
