/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ConjugationBaseChange

/-!
# Base change of constant-form subgroup schemes and of congruences

For a morphism of commutative rings `R → K` and a constant form `C` over `R` with image `C'` over
`K`, scalar extension of the coordinate Hopf algebra of the subgroup scheme of `GLₙ` preserving
`C` is the coordinate Hopf algebra of the subgroup scheme preserving `C'`
(`TauCeti.ConstantForm.coordinateHopfAlgebraBaseChangeIso`), compatibly with the quotient maps from
`O(GLₙ)`.

If `P C₁ Pᵀ = C₂`, conjugation by `P` identifies the subgroup schemes preserving `C₁` and `C₂`
(`TauCeti.ConstantForm.coordinateHopfAlgebraCongr`, `TauCeti.ConstantForm.groupSchemeCongr`).
This identification is natural in the base ring: along the base-change isomorphisms, the scalar
extension of the coordinate isomorphism for `P` is the coordinate isomorphism for the image of `P`
over `K` (`TauCeti.ConstantForm.baseChangeMap_coordinateHopfAlgebraCongr_hom_comp`). The proof
reduces, through the quotient maps from `O(GLₙ)`, to the naturality of conjugation on `GLₙ`
(`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`).
-/

public section

open CategoryTheory Matrix

namespace TauCeti.ConstantForm

universe u v

variable {R : Type u} [CommRing R] (K : Type max u v) [CommRing K] [Algebra R K] {n : ℕ}

/-- **Base change of the coordinate Hopf algebra of a constant-form subgroup scheme.** If `C` maps
to `C'` over `K`, scalar extension of the coordinate Hopf algebra of the subgroup scheme preserving
`C` is that of the subgroup scheme preserving `C'`. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso {C : Matrix (Fin n) (Fin n) R}
    {C' : Matrix (Fin n) (Fin n) K} (hC : C.map (algebraMap R K) = C') :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n C) ≅
      coordinateHopfAlgebra K n C' :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq (definingHopfIdeal R n C) (definingHopfIdeal K n C')
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal hC)

/-- The base-change isomorphism is compatible with the quotient maps from `O(GLₙ)`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom
    {C : Matrix (Fin n) (Fin n) R} {C' : Matrix (Fin n) (Fin n) K}
    (hC : C.map (algebraMap R K) = C') :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n C) ≫
        (coordinateHopfAlgebraBaseChangeIso K hC).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫ coordinateMap K n C' := by
  rw [coordinateMap_def, coordinateMap_def, coordinateHopfAlgebraBaseChangeIso]
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom _ _ _ _

/-- The inverse base-change isomorphism is compatible with the quotient maps from `O(GLₙ)`. -/
theorem coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv
    {C : Matrix (Fin n) (Fin n) R} {C' : Matrix (Fin n) (Fin n) K}
    (hC : C.map (algebraMap R K) = C') :
    coordinateMap K n C' ≫ (coordinateHopfAlgebraBaseChangeIso K hC).inv =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n C) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom, Iso.inv_hom_id_assoc]

/-- **Congruence isomorphisms are natural in the base ring.** If `P C₁ Pᵀ = C₂` over `R`, and
`C₁`, `C₂` map to `C₁'`, `C₂'` over `K`, then along the base-change isomorphisms the scalar
extension of the coordinate isomorphism of conjugation by `P` is the coordinate isomorphism of
conjugation by the image of `P`. -/
theorem baseChangeMap_coordinateHopfAlgebraCongr_hom_comp (P : GL (Fin n) R)
    {C₁ C₂ : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C₁ * (P : Matrix (Fin n) (Fin n) R)ᵀ = C₂)
    {C₁' C₂' : Matrix (Fin n) (Fin n) K} (h₁ : C₁.map (algebraMap R K) = C₁')
    (h₂ : C₂.map (algebraMap R K) = C₂')
    (hP' : (GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K) * C₁' *
      (GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K)ᵀ = C₂') :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateHopfAlgebraCongr P hP).hom ≫
        (coordinateHopfAlgebraBaseChangeIso K h₂).hom =
      (coordinateHopfAlgebraBaseChangeIso K h₁).hom ≫
        (coordinateHopfAlgebraCongr (GeneralLinearGroup.map (algebraMap R K) P) hP').hom := by
  rw [← Iso.inv_comp_eq]
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← coordinateMap_def, ← Category.assoc,
    coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.baseChangeMap (coordinateMap R n C₁)),
    ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    coordinateMap_comp_coordinateHopfAlgebraCongr_hom,
    coordinateMap_comp_coordinateHopfAlgebraCongr_hom,
    (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp]
  have hGL := GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp K P⁻¹
  rw [CommHopfAlgCat.baseChangeFunctor_map, CommHopfAlgCat.baseChangeFunctor_map, Category.assoc,
    baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom,
    reassoc_of% hGL, Iso.inv_hom_id_assoc, map_inv]

end TauCeti.ConstantForm
