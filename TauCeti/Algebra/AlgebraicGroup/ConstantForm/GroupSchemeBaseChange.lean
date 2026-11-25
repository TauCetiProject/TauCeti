/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence.BaseChange
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Square

/-!
# Base change of constant-form subgroup schemes

Let `R → K` be a ring map and let `C` be an `n × n` matrix over `R` with image `C'` over `K`. The
scheme-theoretic base change to `K` of the subgroup scheme of `GLₙ` preserving `C` is the subgroup
scheme over `K` preserving `C'` (`TauCeti.ConstantForm.groupSchemeBaseChangeIso`). This is the
scheme-side form of `TauCeti.ConstantForm.coordinateHopfAlgebraBaseChangeIso`.

Along these isomorphisms, the congruence isomorphisms `TauCeti.ConstantForm.groupSchemeCongr`
(conjugation by `P` for `P C₁ Pᵀ = C₂`) are natural in the base ring: the base change of the
isomorphism for `P` is the isomorphism for the image of `P` over `K`
(`TauCeti.ConstantForm.baseChange_map_groupSchemeCongr_hom_comp`). This is the group-scheme form of
`TauCeti.ConstantForm.baseChangeMap_coordinateHopfAlgebraCongr_hom_comp`.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix

namespace TauCeti.ConstantForm

universe u

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

/-- **Base change of a constant-form subgroup scheme.** If `C` maps to `C'` over `K`, the base
change to `K` of the subgroup scheme of `GLₙ` preserving `C` is the subgroup scheme preserving
`C'`. -/
noncomputable def groupSchemeBaseChangeIso {C : Matrix (Fin n) (Fin n) R}
    {C' : Matrix (Fin n) (Fin n) K} (hC : C.map (algebraMap R K) = C') :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj
        (groupScheme R n C) ≅ groupScheme K n C' :=
  AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (coordinateHopfAlgebra R n C) ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso (coordinateHopfAlgebraBaseChangeIso hC).symm.op

/-- The base-change isomorphism is the comparison of Hopf spectra followed by the spectrum of the
base-change isomorphism of coordinate Hopf algebras. -/
theorem groupSchemeBaseChangeIso_def {C : Matrix (Fin n) (Fin n) R}
    {C' : Matrix (Fin n) (Fin n) K} (hC : C.map (algebraMap R K) = C') :
    groupSchemeBaseChangeIso hC =
      (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (coordinateHopfAlgebra R n C) ≪≫
        (hopfSpec (CommRingCat.of K)).mapIso (coordinateHopfAlgebraBaseChangeIso hC).symm.op :
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj
            (groupScheme R n C) ≅ groupScheme K n C') :=
  (rfl)

/-- **Congruence isomorphisms of subgroup schemes are natural in the base ring.** If
`P C₁ Pᵀ = C₂` over `R`, and `C₁`, `C₂` map to `C₁'`, `C₂'` over `K`, then along the base-change
isomorphisms the base change of the isomorphism of conjugation by `P` is the isomorphism of
conjugation by the image of `P`. -/
theorem baseChange_map_groupSchemeCongr_hom_comp (P : GL (Fin n) R)
    {C₁ C₂ : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C₁ * (P : Matrix (Fin n) (Fin n) R)ᵀ = C₂)
    {C₁' C₂' : Matrix (Fin n) (Fin n) K} (h₁ : C₁.map (algebraMap R K) = C₁')
    (h₂ : C₂.map (algebraMap R K) = C₂')
    (hP' : (GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K) * C₁' *
      (GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K)ᵀ = C₂') :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map
          (groupSchemeCongr P hP).hom ≫ (groupSchemeBaseChangeIso h₂).hom =
      (groupSchemeBaseChangeIso h₁).hom ≫
        (groupSchemeCongr (GeneralLinearGroup.map (algebraMap R K) P) hP').hom := by
  have hS := baseChangeMap_coordinateHopfAlgebraCongr_hom_comp K P hP h₁ h₂ hP'
  rw [groupSchemeCongr_def, groupSchemeCongr_def, groupSchemeBaseChangeIso_def,
    groupSchemeBaseChangeIso_def]
  refine AffineGroupSchemeCat.baseChange_map_hopfSpec_comp_baseChangeIso_hom
    (coordinateHopfAlgebraCongr P hP).inv
    (coordinateHopfAlgebraCongr (GeneralLinearGroup.map (algebraMap R K) P) hP').inv
    (coordinateHopfAlgebraBaseChangeIso h₁) (coordinateHopfAlgebraBaseChangeIso h₂) ?_
  -- Invert the coordinate square of the forward isomorphisms.
  change ((CommHopfAlgCat.baseChangeFunctor (K := K)).mapIso
      (coordinateHopfAlgebraCongr P hP)).inv ≫ _ = _
  rw [Iso.inv_comp_eq, ← Category.assoc]
  change _ = (CommHopfAlgCat.baseChangeMap (K := K) (coordinateHopfAlgebraCongr P hP).hom ≫ _) ≫ _
  rw [hS, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end TauCeti.ConstantForm
