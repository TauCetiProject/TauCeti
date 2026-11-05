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

The construction adapts `TauCeti.Algebra.Lie.E7.Minuscule.Generated.BaseChangeMap`, using
`CommHopfAlgCat.map_baseChangeHopfIdeal_commonKernelHopfIdeal_le` and
`CommHopfAlgCat.baseChangeMapOfLeQuotient`. The generator equations follow
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
  exact CommHopfAlgCat.map_baseChangeHopfIdeal_commonKernelHopfIdeal_le
    (generatorCoordinateMap k)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54)
    (generatorCoordinateAlgebraBaseChangeIso k K) (generatorCoordinateMap K)
    (generatorCoordinateMap_baseChange k K)

/-- The coordinate comparison from the scalar extension of the generated doubled E₆ subgroup
to the subgroup generated over the extension ring. Contravariantly this is a closed immersion;
no flatness assumption on the extension is needed. -/
noncomputable def generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra k) ⟶
      generatedCoordinateHopfAlgebra K :=
  CommHopfAlgCat.baseChangeMapOfLeQuotient (generatedDefiningIdeal k)
    (generatedDefiningIdeal K) (generatedCoordinateHopfAlgebra_def k)
    (generatedCoordinateHopfAlgebra_def K)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54)
    (map_baseChangeHopfIdeal_generatedDefiningIdeal_le k K)

/-- The arbitrary-extension comparison commutes with the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k) ≫
        generatedCoordinateHopfAlgebraBaseChangeMap k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K := by
  apply CommHopfAlgCat.baseChangeMap_comp_baseChangeMapOfLeQuotient
  · exact generatedCoordinateMap_comp_eqToIso_hom k
  · exact generatedCoordinateMap_comp_eqToIso_hom K

private instance baseChangedGeneratedCoordinateMap_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k)) :=
  ConcreteCategory.epi_of_surjective _
    (CommHopfAlgCat.baseChangeMap_surjective _ (generatedCoordinateMap_surjective k))

/-- The ambient coordinate square uniquely determines the arbitrary-extension comparison. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra k) ⟶
      generatedCoordinateHopfAlgebra K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K) :
    f = generatedCoordinateHopfAlgebraBaseChangeMap k K := by
  apply (cancel_epi
    (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap k))).mp
  rw [hf, baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap]

/-- The arbitrary-extension comparison is surjective on coordinate algebras, hence represents
a closed immersion of affine group schemes. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (generatedCoordinateHopfAlgebraBaseChangeMap k K).hom := by
  have hsurj : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom ≫
        generatedCoordinateMap K).hom :=
    (generatedCoordinateMap_surjective K).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 54).hom).2
  rw [← baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap]
    at hsurj
  exact Function.Surjective.of_comp hsurj

/-- Every numbered root-subgroup and weight-torus coordinate lift commutes with the
arbitrary-extension comparison. This is a rewriting lemma rather than a simp rule, leaving
the existing free-extension isomorphism as the simp normal form. -/
@[reassoc]
theorem generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift
    (j : Sum (Fin 6 ⊕ Fin 6) Unit) :
    generatedCoordinateHopfAlgebraBaseChangeMap k K ≫ generatedCoordinateLift K j =
      CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateLift k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso k K j).hom := by
  symm
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
        baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap_assoc,
        generatedCoordinateMap_comp_generatedCoordinateLift]

/-- For free extensions, the arbitrary-extension comparison is the existing isomorphism's
forward morphism. This is a rewriting lemma rather than a simp rule, so that inverse
cancellation for the isomorphism remains available to the simplifier. -/
theorem generatedCoordinateHopfAlgebraBaseChangeIso_hom_eq_baseChangeMap [Module.Free k K] :
    (generatedCoordinateHopfAlgebraBaseChangeIso k K).hom =
      generatedCoordinateHopfAlgebraBaseChangeMap k K :=
  generatedCoordinateHopfAlgebraBaseChangeMap_unique k K _
    (baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom k K)

end TauCeti.E6DoubledMinuscule
