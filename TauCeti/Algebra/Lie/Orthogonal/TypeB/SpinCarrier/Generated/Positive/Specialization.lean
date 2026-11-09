/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.BaseChange

/-!
# Specialization of the generated positive type-B spin subgroup

The positive root subgroups and weight torus generate a closed subgroup after every scalar
extension. This subgroup lies in the scalar extension of the subgroup generated over the
original ring. On coordinate algebras the comparison is a surjective Hopf morphism, uniquely
characterized by its square with the ambient general linear group. It respects every positive
numbered root map and the weight-torus map.

This comparison applies, in particular, to reduction modulo a prime. It is not asserted to be
an isomorphism for arbitrary extensions: new equations may appear after non-flat base change.
For free extensions it agrees with the existing base-change isomorphism. These comparisons
allow the positive subgroup used in constructing a Borel and pinning to be followed under
specialization.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* J. S. Milne, *Algebraic Groups* (2017), §2.h.

The construction uses the common-kernel base-change inclusion and quotient comparison in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange`, together with the type-B spin generator
comparisons in `Generated.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeBSpinCarrier.Generated.Positive

universe v w

noncomputable section

variable (n : ℕ) (k : Type v) (K : Type max v w)
  [CommRing k] [CommRing K] [Algebra k K]

/-- Positive root and torus generators commute with scalar extension through the ambient and
parameter-group coordinate identifications. -/
theorem generator_baseChange (j : Fin (n + 1) ⊕ Unit) :
    ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (generator n k j)) ≫
        (TypeBSpinCarrier.generatorCoordinateAlgebraBaseChangeIso n k K (match j with
          | .inl i => .inl (.inl i)
          | .inr u => .inr u)).hom =
      generator n K j := by
  rcases j with i | u
  · simpa only [generator_inl] using
      TypeBSpinCarrier.generatorCoordinateMap_baseChange n k K (.inl (.inl i))
  · cases u
    simpa only [generator_inr] using
      TypeBSpinCarrier.generatorCoordinateMap_baseChange n k K (.inr ())

/-- The subgroup generated after scalar extension lies in the scalar extension of the
positive subgroup, expressed contravariantly on ambient defining ideals. -/
theorem map_baseChangeHopfIdeal_definingIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingIdeal n k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom ≤
      definingIdeal n K := by
  have h := HopfIdeal.map_mono
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom
    (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le (K := K) (generator n k))
  have heq :
      (CommHopfAlgCat.commonKernelHopfIdeal fun j ↦
        CommHopfAlgCat.baseChangeMap (K := K) (generator n k j)).map
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom =
        definingIdeal n K := by
    rw [CommHopfAlgCat.map_commonKernelHopfIdeal]
    rw [← CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective
      (fun j ↦ (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (generator n k j))
      (fun j ↦ (TypeBSpinCarrier.generatorCoordinateAlgebraBaseChangeIso n k K (match j with
        | .inl i => .inl (.inl i)
        | .inr u => .inr u)).hom)
      (fun j ↦ (ConcreteCategory.bijective_of_isIso
        (TypeBSpinCarrier.generatorCoordinateAlgebraBaseChangeIso n k K (match j with
          | .inl i => .inl (.inl i)
          | .inr u => .inr u)).hom).1)]
    exact congrArg CommHopfAlgCat.commonKernelHopfIdeal
      (funext (generator_baseChange n k K))
  exact heq ▸ h

/-- The coordinate comparison from scalar extension of the positive subgroup to the subgroup
of the general linear group generated after extension. It represents a closed immersion in
the opposite direction on group schemes, not an arbitrary-base-change isomorphism. -/
def coordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra n k) ⟶
      coordinateHopfAlgebra n K :=
  (CommHopfAlgCat.quotientBaseChangeIso (K := K) (definingIdeal n k)).inv ≫
    CommHopfAlgCat.liftQuotient
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingIdeal n k))
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n K)) (by
          intro x hx
          exact (CommHopfAlgCat.mkQuotient_eq_zero_iff _ (definingIdeal n K) _).mpr
            ((HopfIdeal.map_le_iff.mp (map_baseChangeHopfIdeal_definingIdeal_le n k K)) hx))

/-- The comparison commutes with the closed inclusions in the ambient general linear group. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_mkQuotient_comp_baseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal n k)) ≫
        coordinateHopfAlgebraBaseChangeMap n k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n K) := by
  rw [coordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    ← CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

private instance baseChangeQuotient_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K)
      (CommHopfAlgCat.mkQuotient _ (definingIdeal n k))) :=
  ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.baseChangeMap_surjective _
    (CommHopfAlgCat.mkQuotient_surjective _ _))

/-- The ambient square uniquely determines the comparison. -/
theorem coordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra n k) ⟶
      coordinateHopfAlgebra n K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.mkQuotient _ (definingIdeal n k)) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n K)) :
    f = coordinateHopfAlgebraBaseChangeMap n k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal n k)))).mp
  rw [hf, baseChangeMap_mkQuotient_comp_baseChangeMap]

/-- The coordinate comparison is surjective, hence represents a closed immersion. -/
theorem coordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (coordinateHopfAlgebraBaseChangeMap n k K).hom := by
  have h : Function.Surjective
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        CommHopfAlgCat.mkQuotient _ (definingIdeal n K)).hom :=
    (CommHopfAlgCat.mkQuotient_surjective _ (definingIdeal n K)).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom).2
  rw [← baseChangeMap_mkQuotient_comp_baseChangeMap n k K] at h
  exact Function.Surjective.of_comp h

/-- The comparison respects every positive numbered root map and the weight-torus map. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp_commonKernelLift (j : Fin (n + 1) ⊕ Unit) :
    coordinateHopfAlgebraBaseChangeMap n k K ≫
        CommHopfAlgCat.commonKernelLift (generator n K) j =
      CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.commonKernelLift (generator n k) j) ≫
        (TypeBSpinCarrier.generatorCoordinateAlgebraBaseChangeIso n k K (match j with
          | .inl i => .inl (.inl i)
          | .inr u => .inr u)).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (CommHopfAlgCat.mkQuotient _ (definingIdeal n k)))).mp
  rw [← Category.assoc, baseChangeMap_mkQuotient_comp_baseChangeMap,
    Category.assoc, CommHopfAlgCat.mkQuotient_comp_commonKernelLift,
    ← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  apply (Iso.eq_inv_comp _).mp
  simpa only [Category.assoc] using (generator_baseChange n k K j).symm

/-- For a free extension the comparison is the existing isomorphism. -/
theorem coordinateHopfAlgebraBaseChangeMap_eq_iso_hom [Module.Free k K] :
    coordinateHopfAlgebraBaseChangeMap n k K =
      (coordinateHopfAlgebraBaseChangeIso n k K).hom := by
  exact (coordinateHopfAlgebraBaseChangeMap_unique n k K _
    (baseChangeMap_mkQuotient_comp_baseChangeIso_hom n k K)).symm

end

end TauCeti.TypeBSpinCarrier.Generated.Positive
