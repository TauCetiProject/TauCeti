/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.BaseChange

/-!
# Specialization of the generated positive type-D spin subgroup

The positive numbered root subgroups and weight torus generate a closed subgroup over each
commutative ground ring. Under arbitrary scalar extension, the subgroup generated after extension
is a closed subgroup of the scalar extension of the original subgroup. The resulting surjective
coordinate map respects the ambient general-linear inclusion and every generating root and torus
map. It agrees with the existing comparison isomorphism for free extensions.

This one-sided comparison applies in particular to reduction modulo a prime. It does not assert
that generation commutes with non-flat base change, or identify the generated positive subgroup
with a Borel subgroup of the pinned simply connected group scheme.

## Main declarations

* `TauCeti.TypeDSpinCarrier.Generated.Positive.coordinateHopfAlgebraBaseChangeMap`: the canonical
  surjective coordinate comparison under arbitrary scalar extension.
* `TauCeti.TypeDSpinCarrier.Generated.Positive.coordinateHopfAlgebraBaseChangeMap_unique`: its
  characterization by the ambient coordinate square.
* `baseChangeMap_commonKernelLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom`:
  compatibility with the positive root subgroups and weight torus.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* J. S. Milne, *Algebraic Groups* (2017), §2.h.

The construction uses the common-kernel base-change inclusion and quotient comparison in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`, together with the type-D generator
comparisons in `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier.Generated.Positive

universe v w

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (k : Type v) (K : Type max v w)
  [CommRing k] [CommRing K] [Algebra k K]

/-- The transported base-changed defining ideal is contained in the defining ideal of the
positive subgroup generated over the extension ring. No flatness hypothesis is needed. -/
theorem map_baseChangeHopfIdeal_definingIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingIdeal n hn k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom ≤
      definingIdeal n hn K := by
  have h := CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le (K := K)
    (generator n hn k)
  have hmap := HopfIdeal.map_mono
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom h
  rw [CommHopfAlgCat.map_commonKernelHopfIdeal,
    ← CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective _
      (fun j ↦ (generatorCoordinateAlgebraBaseChangeIso n k K (generatorIndex n j)).hom)
      (fun j ↦ (ConcreteCategory.bijective_of_isIso
        (generatorCoordinateAlgebraBaseChangeIso n k K (generatorIndex n j)).hom).1)] at hmap
  simp only [Category.assoc, generator_baseChange] at hmap
  exact hmap

private theorem baseChange_definingIdeal_le_ker :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingIdeal n hn k)).toIdeal ≤
      RingHom.ker ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n hn K)).hom.toAlgHom.toRingHom := by
  intro x hx
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr
  exact map_baseChangeHopfIdeal_definingIdeal_le n hn k K
    (HopfIdeal.mem_map_of_mem _ hx)

/-- The surjective coordinate map from the scalar extension of the positive generated subgroup
to the positive subgroup generated after extension. Contravariantly, this is a closed immersion
in the opposite direction, not an asserted isomorphism for arbitrary extensions. -/
def coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra n hn k) ⟶
      coordinateHopfAlgebra n hn K :=
  (CommHopfAlgCat.quotientBaseChangeIso (K := K) (definingIdeal n hn k)).inv ≫
    CommHopfAlgCat.liftQuotient _
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n hn K))
      (baseChange_definingIdeal_le_ker n hn k K)

/-- The arbitrary-extension comparison commutes with the ambient general-linear coordinate maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn k)) ≫
        coordinateHopfAlgebraBaseChangeMap n hn k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n hn K) := by
  have hbase := (Iso.comp_inv_eq
    (CommHopfAlgCat.quotientBaseChangeIso (K := K) (definingIdeal n hn k))).mpr
      (CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom
        (definingIdeal n hn k)).symm
  rw [coordinateHopfAlgebraBaseChangeMap, ← Category.assoc, hbase,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient]

private instance baseChangeQuotient_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K)
      (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn k))) :=
  ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.baseChangeMap_surjective _
    (CommHopfAlgCat.mkQuotient_surjective _ _))

/-- The ambient coordinate square uniquely determines the comparison map. -/
theorem coordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra n hn k) ⟶
      coordinateHopfAlgebra n hn K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn k)) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n hn K)) :
    f = coordinateHopfAlgebraBaseChangeMap n hn k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn k)))).mp
  rw [hf, baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap]

/-- The coordinate comparison is surjective, so the corresponding subgroup map is a closed
immersion for every extension of commutative rings. -/
theorem coordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (coordinateHopfAlgebraBaseChangeMap n hn k K).hom := by
  have h : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n hn K)).hom :=
    (CommHopfAlgCat.mkQuotient_surjective _ (definingIdeal n hn K)).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom).2
  rw [← baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap n hn k K] at h
  exact Function.Surjective.of_comp h

/-- The comparison respects each positive numbered root subgroup and the weight torus. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_commonKernelLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom
    (j : Fin n ⊕ Unit) :
    CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.commonKernelLift (generator n hn k) j) ≫
        (generatorCoordinateAlgebraBaseChangeIso n k K (generatorIndex n j)).hom =
      coordinateHopfAlgebraBaseChangeMap n hn k K ≫
        CommHopfAlgCat.commonKernelLift (generator n hn K) j := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal n hn k)))).mp
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  rw [baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeMap_assoc,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  exact (Iso.inv_comp_eq _).mp (generator_baseChange n hn k K j)

/-- For a free extension the canonical comparison is the existing base-change isomorphism. -/
theorem coordinateHopfAlgebraBaseChangeMap_eq_iso_hom [Module.Free k K] :
    coordinateHopfAlgebraBaseChangeMap n hn k K =
      (coordinateHopfAlgebraBaseChangeIso n hn k K).hom := by
  symm
  apply coordinateHopfAlgebraBaseChangeMap_unique
  exact baseChangeMap_mkQuotient_comp_baseChangeIso_hom n hn k K

end

end TauCeti.TypeDSpinCarrier.Generated.Positive
