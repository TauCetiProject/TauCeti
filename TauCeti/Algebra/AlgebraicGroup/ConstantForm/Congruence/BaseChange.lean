/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Congruence.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.BaseChange

/-!
# Naturality of congruence isomorphisms of constant-form subgroup schemes

If `P C₁ Pᵀ = C₂`, conjugation by `P` identifies the coordinate Hopf algebras of the subgroup
schemes of `GLₙ` preserving `C₁` and `C₂` (`TauCeti.ConstantForm.coordinateHopfAlgebraCongr`).
This coordinate isomorphism is natural in the base ring: along the base-change isomorphisms
`TauCeti.ConstantForm.coordinateHopfAlgebraBaseChangeIso`, the scalar extension of the coordinate
isomorphism for `P` is the coordinate isomorphism for the image of `P` over `K`
(`TauCeti.ConstantForm.baseChangeMap_coordinateHopfAlgebraCongr_hom_comp`). Naturality of the
group-scheme isomorphism `TauCeti.ConstantForm.groupSchemeCongr` is not proved here.

The proof specializes the naturality of quotient isomorphisms under base change
(`TauCeti.CommHopfAlgCat.baseChangeMap_quotientIsoOfComapEq_hom_comp`)
to the naturality of conjugation on `GLₙ`
(`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`).
-/

public section

open CategoryTheory Matrix

namespace TauCeti.ConstantForm

universe u v

variable {R : Type u} [CommRing R] (K : Type max u v) [CommRing K] [Algebra R K] {n : ℕ}

/-- **Congruence isomorphisms are natural in the base ring.** If `P C₁ Pᵀ = C₂` over `R`, and
`C₁`, `C₂` map to `C₁'`, `C₂'` over `K`, then along the base-change isomorphisms the scalar
extension of the coordinate isomorphism of conjugation by `P` is the coordinate isomorphism of
conjugation by the image of `P`. -/
@[reassoc]
theorem baseChangeMap_coordinateHopfAlgebraCongr_hom_comp (P : GL (Fin n) R)
    {C₁ C₂ : Matrix (Fin n) (Fin n) R}
    (hP : (P : Matrix (Fin n) (Fin n) R) * C₁ * (P : Matrix (Fin n) (Fin n) R)ᵀ = C₂)
    {C₁' C₂' : Matrix (Fin n) (Fin n) K} (h₁ : C₁.map (algebraMap R K) = C₁')
    (h₂ : C₂.map (algebraMap R K) = C₂')
    (hP' : (GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K) * C₁' *
      (GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K)ᵀ = C₂') :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateHopfAlgebraCongr P hP).hom ≫
        (coordinateHopfAlgebraBaseChangeIso h₂).hom =
      (coordinateHopfAlgebraBaseChangeIso h₁).hom ≫
        (coordinateHopfAlgebraCongr (GeneralLinearGroup.map (algebraMap R K) P) hP').hom := by
  rw [coordinateHopfAlgebraCongr_def, coordinateHopfAlgebraCongr_def]
  have e₁ := baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom h₁
  have e₂ := baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom h₂
  rw [coordinateMap_def, coordinateMap_def] at e₁ e₂
  refine CommHopfAlgCat.baseChangeMap_quotientIsoOfComapEq_hom_comp _ _ _ _ _ _ e₁ e₂ ?_
  rw [← map_inv]
  exact GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp K P⁻¹

end TauCeti.ConstantForm
