/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant

/-!
# Legendre normal form of a projective Weierstrass model

For an elliptic Weierstrass curve `W` over `R`, sections `P, Q` of `W.projModel` missing
`W.projModelZero` and killed by `2`, and a conormal basis `ω` with
`W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1`, `2` is a unit of `R` and there are a unique `l : R`
with `2l(l - 1)` a unit and a unique pointed isomorphism `(freyCurve 1 (-l)).projModel ≅`
`W.projModel` carrying `(0, 0) ↦ P`, `(1, 0) ↦ Q`, and pulling `ω` back to
`(freyCurve 1 (-l)).weierstrassDifferential` (`existsUnique_legendreNormalForm`,
`legendreNormalForm_iso_ext`, `exists_iso_legendreNormalForm_iff`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Princeton Univ. Press, 1985,
  2.2.4, 2.2.9, and 4.6.2.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.7.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TauCeti
open AlgebraicGeometry.Scheme.Hom (conormalBasisPullbackOfIso conormalBasisPullbackOfIso_congr)

universe u

namespace WeierstrassCurve

noncomputable section

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic]

private theorem conormalBasisPullbackOfIso_eq_weierstrassDifferential_iff
    {W' : WeierstrassCurve R} [W'.IsElliptic] (C : VariableChange R) (hC : C • W = W')
    {e : W'.projModel ≅ W.projModel} (he : e.hom ≫ W.projModelOver = W'.projModelOver)
    (he₀ : W'.projModelZero ≫ e.hom = W.projModelZero)
    (heC : e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    conormalBasisPullbackOfIso W.projModelZero_projModelOver W'.projModelZero_projModelOver
        e he he₀ ω = W'.weierstrassDifferential ↔ C.u = W.weierstrassDifferentialScalar ω := by
  subst hC
  have he' : e.hom = (W.projModelVariableChangeIso C).hom := by simpa using heC
  rw [conormalBasisPullbackOfIso_congr W.projModelZero_projModelOver
    (C • W).projModelZero_projModelOver he' he he₀
    (W.projModelVariableChangeIso_hom_projModelOver C)
    (W.projModelZero_projModelVariableChangeIso_hom C) ω]
  set ω' := conormalBasisPullbackOfIso W.projModelZero_projModelOver
    (C • W).projModelZero_projModelOver (W.projModelVariableChangeIso C)
    (W.projModelVariableChangeIso_hom_projModelOver C)
    (W.projModelZero_projModelVariableChangeIso_hom C) ω
  have hiff : ω' = (C • W).weierstrassDifferential ↔ (C • W).weierstrassDifferentialScalar ω' = 1 :=
    ⟨fun h ↦ by rw [h, weierstrassDifferentialScalar_weierstrassDifferential],
      fun h ↦ by rw [← (C • W).unitSmulIso_weierstrassDifferentialScalar ω', h, map_one,
        Scheme.Modules.unitSmulIso_one]⟩
  rw [hiff,
    W.weierstrassDifferentialScalar_conormalBasisPullbackOfIso_projModelVariableChangeIso C ω,
    mul_inv_eq_one, eq_comm]

section PrivateHelpers

variable {l : R} [(freyCurve 1 (-l)).IsElliptic] {x₁ y₁ x₂ y₂ : R}
  (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
  (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)

private theorem exists_variableChange_of_iso (e : (freyCurve 1 (-l)).projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = (freyCurve 1 (-l)).projModelOver)
    (he₀ : (freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero)
    (heP : (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫ e.hom =
      W.projModelAffinePoint h₁)
    (heQ : (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫ e.hom =
      W.projModelAffinePoint h₂)
    (heω : conormalBasisPullbackOfIso W.projModelZero_projModelOver
      (freyCurve 1 (-l)).projModelZero_projModelOver e he he₀ ω =
      (freyCurve 1 (-l)).weierstrassDifferential) :
    ∃ C : VariableChange R, ∃ hC : C • W = freyCurve 1 (-l),
      e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom ∧
        C.u = W.weierstrassDifferentialScalar ω ∧ C.r = x₁ ∧ C.t = y₁ ∧
        (C.u : R) ^ 2 + C.r = x₂ ∧ (C.u : R) ^ 2 * C.s + C.t = y₂ := by
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  have hCu := (conormalBasisPullbackOfIso_eq_weierstrassDifferential_iff C hC he he₀ heC ω).mp heω
  rw [heC, hpt, projModelAffinePoint_inj] at heP heQ
  exact ⟨C, hC, heC, hCu, by simpa using heP.1, by simpa using heP.2,
    by simpa using heQ.1, by simpa using heQ.2⟩

private theorem exists_iso_of_variableChange (C : VariableChange R) (hC : C • W = freyCurve 1 (-l))
    (hCu : C.u = W.weierstrassDifferentialScalar ω) (hCr : C.r = x₁) (hCt : C.t = y₁)
    (hCx : (C.u : R) ^ 2 + C.r = x₂) (hCy : (C.u : R) ^ 2 * C.s + C.t = y₂) :
    ∃ (e : (freyCurve 1 (-l)).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (freyCurve 1 (-l)).projModelOver)
      (he₀ : (freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero),
      (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫ e.hom =
          W.projModelAffinePoint h₁ ∧
        (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫ e.hom =
          W.projModelAffinePoint h₂ ∧
        conormalBasisPullbackOfIso W.projModelZero_projModelOver
          (freyCurve 1 (-l)).projModelZero_projModelOver e he he₀ ω =
        (freyCurve 1 (-l)).weierstrassDifferential := by
  obtain ⟨he, he₀, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  let e : (freyCurve 1 (-l)).projModel ≅ W.projModel :=
    eqToIso (congrArg projModel hC.symm) ≪≫ W.projModelVariableChangeIso C
  have heC : e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom :=
    by rw [Iso.trans_hom, eqToIso.hom]
  refine ⟨e, heC ▸ he, heC ▸ he₀, ?_, ?_,
    (conormalBasisPullbackOfIso_eq_weierstrassDifferential_iff C hC _ _ heC ω).mpr hCu⟩
  · rw [heC, hpt, projModelAffinePoint_inj]; simp only [mul_zero, zero_add, hCr, hCt, and_self]
  · rw [heC, hpt, projModelAffinePoint_inj]
    simp only [mul_one, mul_zero, zero_add, hCx, hCy, and_self]

end PrivateHelpers

/-- **Legendre normal form of a projective Weierstrass model.** -/
theorem existsUnique_legendreNormalForm {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (hP₂ : P ≫ W.projModelMulBy 2 = W.projModelZero)
    (hQ₂ : Q ≫ W.projModelMulBy 2 = W.projModelZero)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    (hω : W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1) :
    ∃! l : R, ∃ (_ : (freyCurve 1 (-l)).IsElliptic)
      (e : (freyCurve 1 (-l)).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (freyCurve 1 (-l)).projModelOver)
      (he₀ : (freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero),
      (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫ e.hom = P ∧
        (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫ e.hom = Q ∧
        conormalBasisPullbackOfIso W.projModelZero_projModelOver
          (freyCurve 1 (-l)).projModelZero_projModelOver e he he₀ ω =
        (freyCurve 1 (-l)).weierstrassDifferential := by
  obtain ⟨x₁, y₁, h₁, rfl⟩ := W.exists_eq_projModelAffinePoint hP hP₀
  obtain ⟨x₂, y₂, h₂, rfl⟩ := W.exists_eq_projModelAffinePoint hQ hQ₀
  have hψ₁ := (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₁).mp hP₂
  have hψ₂ := (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₂).mp hQ₂
  set u := W.weierstrassDifferentialScalar ω
  have hu := (W.projModelAdaptedXCoord_eq_one_iff_of_eq_projModelAffinePoint
    hP hQ hP₀ hQ₀ ω h₁ h₂ rfl rfl).mp hω
  have h2 := W.isUnit_two_of_evalEval_ψ₂_eq_zero hψ₁ hψ₂ (hu ▸ u.isUnit.pow 2)
  obtain ⟨C, ⟨hCu, hCr, hCt, hCx, hCy, B, hCB⟩, hCuniq⟩ :=
    existsUnique_variableChange_legendre h2 u h₁ h₂ hψ₁ hψ₂ hu
  have hC : C • W = freyCurve 1 (-(-B)) := by rw [neg_neg, hCB]
  have hEll : (freyCurve 1 (-(-B))).IsElliptic := hC ▸ inferInstance
  obtain ⟨e, he, he₀, heP, heQ, heω⟩ :=
    exists_iso_of_variableChange h₁ h₂ ω C hC hCu hCr hCt hCx hCy
  refine ⟨-B, ⟨hEll, e, he, he₀, heP, heQ, heω⟩, ?_⟩
  rintro l ⟨hEll', e', he', he₀', heP', heQ', heω'⟩
  obtain ⟨D, hD, -, hDu, hDr, hDt, hDx, hDy⟩ :=
    exists_variableChange_of_iso h₁ h₂ ω e' he' he₀' heP' heQ' heω'
  obtain rfl : D = C := hCuniq D ⟨hDu, hDr, hDt, hDx, hDy, -l, hD⟩
  have ha₄ : (freyCurve 1 (-l)).a₄ = (freyCurve 1 B).a₄ := congrArg a₄ (hD.symm.trans hCB)
  rw [freyCurve_a₄, freyCurve_a₄] at ha₄; linear_combination ha₄

/-- **Uniqueness of the Legendre normal-form isomorphism.** -/
theorem legendreNormalForm_iso_ext {l : R} [hE : (freyCurve 1 (-l)).IsElliptic]
    {ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf}
    {e e' : (freyCurve 1 (-l)).projModel ≅ W.projModel}
    (he : e.hom ≫ W.projModelOver = (freyCurve 1 (-l)).projModelOver)
    (he₀ : (freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero)
    (he' : e'.hom ≫ W.projModelOver = (freyCurve 1 (-l)).projModelOver)
    (he'₀ : (freyCurve 1 (-l)).projModelZero ≫ e'.hom = W.projModelZero)
    (heP : (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫ e.hom =
      (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫ e'.hom)
    (heω : conormalBasisPullbackOfIso W.projModelZero_projModelOver
      (freyCurve 1 (-l)).projModelZero_projModelOver e he he₀ ω =
      (freyCurve 1 (-l)).weierstrassDifferential)
    (he'ω : conormalBasisPullbackOfIso W.projModelZero_projModelOver
      (freyCurve 1 (-l)).projModelZero_projModelOver e' he' he'₀ ω =
      (freyCurve 1 (-l)).weierstrassDifferential) : e = e' := by
  have h2 : IsUnit (2 : R) := ((isElliptic_freyCurve_iff 1 (-l)).mp hE).1
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨C', ⟨hC', heC'⟩, -⟩ :=
    existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e' he' he'₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  obtain ⟨-, -, hpt'⟩ := eqToHom_projModelVariableChangeIso_hom_spec C' hC'
  have hCu := (conormalBasisPullbackOfIso_eq_weierstrassDifferential_iff C hC he he₀ heC ω).mp heω
  have hC'u := (conormalBasisPullbackOfIso_eq_weierstrassDifferential_iff C' hC' he' he'₀ heC'
    ω).mp he'ω
  rw [heC, heC', hpt, hpt', projModelAffinePoint_inj] at heP
  simp only [mul_zero, zero_add] at heP
  obtain rfl : C = C' :=
    (eq_toLegendre h2 (W.weierstrassDifferentialScalar ω) hCu rfl rfl hC).trans
      (eq_toLegendre h2 (W.weierstrassDifferentialScalar ω) hC'u heP.1.symm heP.2.symm hC').symm
  ext1; exact heC.trans heC'.symm

/-- **Necessity and sufficiency of the Legendre normal-form conditions.** -/
theorem exists_iso_legendreNormalForm_iff {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    (∃ (l : R) (_ : (freyCurve 1 (-l)).IsElliptic)
      (e : (freyCurve 1 (-l)).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (freyCurve 1 (-l)).projModelOver)
      (he₀ : (freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero),
      (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫ e.hom = P ∧
        (freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫ e.hom = Q ∧
        conormalBasisPullbackOfIso W.projModelZero_projModelOver
          (freyCurve 1 (-l)).projModelZero_projModelOver e he he₀ ω =
        (freyCurve 1 (-l)).weierstrassDifferential) ↔
      ∃ (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s),
        P ≫ W.projModelMulBy 2 = W.projModelZero ∧ Q ≫ W.projModelMulBy 2 = W.projModelZero ∧
          (∀ s, Q s ≠ P s) ∧ W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1 := by
  refine ⟨fun ⟨l, hEll, e, he, he₀, heP, heQ, heω⟩ ↦ ?_,
    fun ⟨hP₀, hQ₀, hP₂, hQ₂, _, hω⟩ ↦
      let ⟨l, hl, _⟩ := W.existsUnique_legendreNormalForm hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω; ⟨l, hl⟩⟩
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  have hP_aff := heP.symm.trans (by rw [heC, hpt]); have hQ_aff := heQ.symm.trans (by rw [heC, hpt])
  set h₁ := (Affine.variableChange_equation W C 0 0).mpr (hC ▸ equation_freyCurve_zero (R := R) 1 _)
  set h₂ := (Affine.variableChange_equation W C 1 0).mpr (hC ▸ equation_freyCurve_one_zero (-l))
  have hP₀ := hP_aff ▸ W.projModelAffinePoint_apply_ne_projModelZero h₁
  have hQ₀ := hQ_aff ▸ W.projModelAffinePoint_apply_ne_projModelZero h₂
  obtain ⟨D, hD, -, hDu, hDr, hDt, hDx, hDy⟩ :=
    exists_variableChange_of_iso h₁ h₂ ω e he he₀ (heP.trans hP_aff) (heQ.trans hQ_aff) heω
  obtain ⟨_, _, hψ₁, hψ₂, hu⟩ :=
    (exists_variableChange_legendre_iff (W := W) (W.weierstrassDifferentialScalar ω)).mp
      ⟨D, hDu, hDr, hDt, hDx, hDy, -l, hD⟩
  have hP₂ := hP_aff ▸ (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₁).mpr hψ₁
  have hQ₂ := hQ_aff ▸ (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₂).mpr hψ₂
  have hQP : ∀ s, Q s ≠ P s := fun s ↦ by
    rw [hP_aff, hQ_aff]; exact (W.forall_projModelAffinePoint_apply_ne_iff_isUnit_sub h₁ h₂
      (hP_aff ▸ hP₂)).mpr (hu ▸ (W.weierstrassDifferentialScalar ω).isUnit.pow 2) s
  exact ⟨hP₀, hQ₀, hP₂, hQ₂, hQP, (W.projModelAdaptedXCoord_eq_one_iff_of_eq_projModelAffinePoint
    hP hQ hP₀ hQ₀ ω h₁ h₂ hP_aff hQ_aff).mpr hu⟩

end

end WeierstrassCurve
