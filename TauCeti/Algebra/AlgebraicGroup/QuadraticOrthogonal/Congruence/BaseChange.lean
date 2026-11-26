/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Congruence.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation.BaseChange

/-!
# Naturality of the transport of orthogonal group schemes along isometries

For an isometry `P` from `q` to `q₀`, conjugation by `P` identifies the coordinate Hopf algebras
of `O(q)` and `O(q₀)` (`TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraCongr`). This coordinate
isomorphism is natural in the base ring: along the base-change isomorphisms
`TauCeti.QuadraticOrthogonal.coordinateHopfAlgebraBaseChangeIso`, the scalar extension of the
coordinate isomorphism for `P` is the coordinate isomorphism for the image of `P` over `K`
(`TauCeti.QuadraticOrthogonal.baseChangeMap_coordinateHopfAlgebraCongr_hom_comp`). The same holds
for the group-scheme isomorphism `TauCeti.QuadraticOrthogonal.groupSchemeCongr` along the
base-change isomorphisms `TauCeti.QuadraticOrthogonal.groupSchemeBaseChangeIso`
(`TauCeti.QuadraticOrthogonal.map_groupSchemeCongr_hom_comp_groupSchemeBaseChangeIso_hom`),
obtained from the coordinate form by
`TauCeti.AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso_trans_hom_naturality_inv`.

The proofs follow `TauCeti.ConstantForm.baseChangeMap_coordinateHopfAlgebraCongr_hom_comp` and
`TauCeti.ConstantForm.map_groupSchemeCongr_hom_comp_groupSchemeBaseChangeIso_hom`: the naturality
of quotient isomorphisms under base change
(`TauCeti.CommHopfAlgCat.baseChangeMap_quotientIsoOfComapEq_hom_comp`) specializes to the
naturality of conjugation on `GLₙ`
(`TauCeti.GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp`).
-/

public section

open AlgebraicGeometry CategoryTheory Matrix
open QuadraticForm (coefficientMatrix)

namespace TauCeti.QuadraticOrthogonal

universe u v

section Coordinate

variable {R : Type u} {K : Type max u v} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}
variable {q : QuadraticForm R (Fin n → R)}

/-- **The coordinate isomorphism of an isometry is natural in the base ring.** If `P` is an
isometry from `q` to `q₀` over `R`, and `q`, `q₀` have the coefficients of `q₁`, `q₂` over `K`,
then along the base-change isomorphisms the scalar extension of the coordinate isomorphism for `P`
is the coordinate isomorphism for the image of `P`, an isometry from `q₁` to `q₂`. -/
@[reassoc]
theorem baseChangeMap_coordinateHopfAlgebraCongr_hom_comp {q₀ : QuadraticForm R (Fin n → R)}
    {q₁ q₂ : QuadraticForm K (Fin n → K)} (P : GL (Fin n) R)
    (hP : ∀ x, q₀ ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x)
    (h₁ : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q₁ (Pi.basisFun K (Fin n)))
    (h₂ : (coefficientMatrix q₀ (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q₂ (Pi.basisFun K (Fin n)))
    (hP' : ∀ x, q₂ ((GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K) *ᵥ x) =
      q₁ x) :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateHopfAlgebraCongr P hP).hom ≫
        (coordinateHopfAlgebraBaseChangeIso h₂).hom =
      (coordinateHopfAlgebraBaseChangeIso h₁).hom ≫
        (coordinateHopfAlgebraCongr (GeneralLinearGroup.map (algebraMap R K) P) hP').hom := by
  rw [coordinateHopfAlgebraCongr_def, coordinateHopfAlgebraCongr_def]
  refine CommHopfAlgCat.baseChangeMap_quotientIsoOfComapEq_hom_comp _ _ _ _ _ _
    (baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_hom h₁)
    (baseChangeMap_mkQuotient_comp_coordinateHopfAlgebraBaseChangeIso_hom h₂) ?_
  rw [← map_inv]
  exact GeneralLinear.baseChangeMap_conjCoordinateIso_hom_comp K P⁻¹

end Coordinate

section GroupScheme

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}
variable {q : QuadraticForm R (Fin n → R)}

/-- **The isomorphism of orthogonal group schemes of an isometry is natural in the base ring.**
If `P` is an isometry from `q` to `q₀` over `R`, and `q`, `q₀` have the coefficients of `q₁`, `q₂`
over `K`, then along the base-change isomorphisms the base change of `groupSchemeCongr P` is
`groupSchemeCongr` of the image of `P`. -/
@[reassoc]
theorem map_groupSchemeCongr_hom_comp_groupSchemeBaseChangeIso_hom
    {q₀ : QuadraticForm R (Fin n → R)} {q₁ q₂ : QuadraticForm K (Fin n → K)} (P : GL (Fin n) R)
    (hP : ∀ x, q₀ ((P : Matrix (Fin n) (Fin n) R) *ᵥ x) = q x)
    (h₁ : (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q₁ (Pi.basisFun K (Fin n)))
    (h₂ : (coefficientMatrix q₀ (Pi.basisFun R (Fin n))).map (algebraMap R K) =
      coefficientMatrix q₂ (Pi.basisFun K (Fin n)))
    (hP' : ∀ x, q₂ ((GeneralLinearGroup.map (algebraMap R K) P : Matrix (Fin n) (Fin n) K) *ᵥ x) =
      q₁ x) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map
          (groupSchemeCongr P hP).hom ≫ (groupSchemeBaseChangeIso h₂).hom =
      (groupSchemeBaseChangeIso h₁).hom ≫
        (groupSchemeCongr (GeneralLinearGroup.map (algebraMap R K) P) hP').hom := by
  have hS := baseChangeMap_coordinateHopfAlgebraCongr_hom_comp P hP h₁ h₂ hP'
  rw [groupSchemeCongr_def, groupSchemeCongr_def, groupSchemeBaseChangeIso_def,
    groupSchemeBaseChangeIso_def, GeneralLinear.hopfIdealBaseChangeIso_def,
    GeneralLinear.hopfIdealBaseChangeIso_def]
  exact AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso_trans_hom_naturality_inv _ _ _ _ hS

end GroupScheme

end TauCeti.QuadraticOrthogonal
