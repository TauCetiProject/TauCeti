/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.LevelThreeNormalForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy.ThreeTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Level-three normal form of a projective Weierstrass model with two points of order `3`

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, and let `P` and `Q` be
sections of its projective model `projModel W ⟶ Spec R` which meet the zero section over no point
of `Spec R`, are killed by multiplication by `3`, and such that `Q` is neither `P` nor `-P` over
any point of `Spec R`. Over a field, these conditions say that `(P, Q)` is a basis of the
`3`-torsion. Then there are unique `μ ζ : R` with `ζ² + ζ + 1 = 0` and a unique isomorphism

`projModel (levelThreeNormalForm μ) ≅ projModel W`

over `Spec R` carrying the zero section to the zero section, the point `(0, 0)` of the level-three
normal form `Y² + 3μXY + (μ³ - 1)Y = X³` to `P`, and its point
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` to `Q` (`WeierstrassCurve.existsUnique_levelThreeNormalForm`
and `WeierstrassCurve.levelThreeNormalForm_iso_ext`). Conversely, the images of these two points
under such an isomorphism satisfy the conditions
(`WeierstrassCurve.exists_iso_levelThreeNormalForm_iff`). No hypothesis on `R` is needed: `R` may
be nonreduced, and `3` is not assumed to be a unit, since the conditions force it to be one.

This is the scheme-theoretic form of the equation-level level-three normal form
`WeierstrassCurve.existsUnique_variableChange_levelThreeNormalForm`, whose hypothesis is the
equation-level condition `WeierstrassCurve.IsThreeTorsionBasis`. For two solutions `(x₁, y₁)` and
`(x₂, y₂)` of the affine Weierstrass equation, that condition holds exactly when the points
`P = [x₁ : y₁ : 1]` and `Q = [x₂ : y₂ : 1]` satisfy the conditions above
(`WeierstrassCurve.isThreeTorsionBasis_iff`): `3P = 0` exactly when `Ψ₃(x₁) = 0`
(`WeierstrassCurve.projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff`), and `Q` is
`P` or `-P` over a point `s` exactly when `x₂ ≡ x₁` modulo `s`
(`WeierstrassCurve.projModelAffinePoint_apply_eq_or_eq_projModelNeg_iff`).

## Main results

* `WeierstrassCurve.isThreeTorsionBasis_iff`: two points `[x : y : 1]` satisfy the conditions above
  exactly when their coordinates form a basis of the `3`-torsion in the equation-level sense.
* `WeierstrassCurve.existsUnique_levelThreeNormalForm`: two sections satisfying the conditions are
  the images of the basis points `(0, 0)` and `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` under a pointed
  isomorphism from the projective model of a level-three normal form, for unique `μ` and `ζ`.
* `WeierstrassCurve.levelThreeNormalForm_iso_ext`: such an isomorphism is unique.
* `WeierstrassCurve.exists_iso_levelThreeNormalForm_iff`: such an isomorphism exists exactly when
  the two sections satisfy the conditions.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.10 and 2.2.11 (naive level-three structures as
  rigidifiers).
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix A,
  Proposition 1.3, for the normal form `Y² + a₁XY + a₃Y = X³` at a point of order `3`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

-- The isomorphism `projModel W' ≅ projModel W` induced by a change of variables `C` with
-- `C • W = W'` lies over `Spec R`, carries the zero section to the zero section, and carries
-- `[x : y : 1]` to `[u²x + r : u³y + u²sx + t : 1]`.
private theorem eqToHom_projModelVariableChangeIso_hom_spec {W' : WeierstrassCurve R}
    (C : VariableChange R) (hC : C • W = W') :
    (eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom) ≫
        W.projModelOver = W'.projModelOver ∧
      W'.projModelZero ≫ eqToHom (congrArg projModel hC.symm) ≫
        (W.projModelVariableChangeIso C).hom = W.projModelZero ∧
      ∀ {x y : R} (h : W'.toAffine.Equation x y), W'.projModelAffinePoint h ≫
        eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom =
          W.projModelAffinePoint ((Affine.variableChange_equation W C x y).mpr (hC ▸ h)) := by
  subst hC
  exact ⟨by simp, by simp, fun h ↦ by simp⟩

/-- **Bases of the `3`-torsion of a projective Weierstrass model.** For solutions `(x₁, y₁)` and
`(x₂, y₂)` of the affine equation of an elliptic Weierstrass curve `W`, the coordinates form a basis
of the `3`-torsion in the equation-level sense exactly when the points `P = [x₁ : y₁ : 1]` and
`Q = [x₂ : y₂ : 1]` of `projModel W` are killed by multiplication by `3` and `Q` is neither `P`
nor `-P` over any point of `Spec R`. -/
theorem isThreeTorsionBasis_iff [W.IsElliptic] {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) :
    W.IsThreeTorsionBasis x₁ y₁ x₂ y₂ ↔
      W.projModelAffinePoint h₁ ≫ W.projModelMulBy 3 = W.projModelZero ∧
        W.projModelAffinePoint h₂ ≫ W.projModelMulBy 3 = W.projModelZero ∧
        ∀ s, W.projModelAffinePoint h₂ s ≠ W.projModelAffinePoint h₁ s ∧
          W.projModelAffinePoint h₂ s ≠ (W.projModelAffinePoint h₁ ≫ W.projModelNeg) s := by
  simp_rw [projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff, ← not_or,
    projModelAffinePoint_apply_eq_or_eq_projModelNeg_iff]
  -- an element is a unit exactly when it lies in no prime ideal
  have hunit : IsUnit (x₂ - x₁) ↔ ∀ s : Spec (.of R), x₂ - x₁ ∉ s.asIdeal := by
    refine ⟨fun hu s hs ↦ s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hu), fun H ↦ ?_⟩
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hu)
    exact H ⟨m, hm.isPrime⟩ hmem
  rw [← hunit]
  refine ⟨fun hb ↦ ⟨hb.eval_Ψ₃_fst, hb.eval_Ψ₃_snd, hb.isUnit_sub⟩, fun ⟨hΨ₁, hΨ₂, hsub⟩ ↦
    ⟨isUnit_three_of_eval_Ψ₃_eq_zero hΨ₁ hΨ₂ hsub, h₁, h₂, hΨ₁, hΨ₂,
      isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero h₁ hΨ₁, isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero h₂ hΨ₂,
      hsub⟩⟩

-- A pointed isomorphism over `Spec R` from the projective model of a level-three normal form to
-- that of `W`, carrying the basis points to `[x₁ : y₁ : 1]` and `[x₂ : y₂ : 1]`, is induced by a
-- change of variables to level-three normal form at `(x₁, y₁)` and `(x₂, y₂)`.
private theorem exists_variableChange_of_iso {μ ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (e : (levelThreeNormalForm μ).projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = (levelThreeNormalForm μ).projModelOver)
    (he₀ : (levelThreeNormalForm μ).projModelZero ≫ e.hom = W.projModelZero)
    (heP : (levelThreeNormalForm μ).projModelAffinePoint (equation_levelThreeNormalForm_zero μ) ≫
      e.hom = W.projModelAffinePoint h₁)
    (heQ : (levelThreeNormalForm μ).projModelAffinePoint
      (equation_levelThreeNormalForm_basisPoint μ hζ) ≫ e.hom = W.projModelAffinePoint h₂) :
    ∃ C : VariableChange R, ∃ hC : C • W = levelThreeNormalForm μ,
      e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom ∧
        C.r = x₁ ∧ C.t = y₁ ∧ x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r ∧
        y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t := by
  obtain ⟨C, ⟨hC, hCe⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  rw [hCe, hpt, projModelAffinePoint_inj] at heP heQ
  refine ⟨C, hC, hCe, ?_, ?_, heQ.1.symm, heQ.2.symm⟩
  · simpa using heP.1
  · simpa using heP.2

-- A pointed isomorphism over `Spec R` from the projective model of a level-three normal form to
-- that of `W` carries the two basis points to points `[x₁ : y₁ : 1]` and `[x₂ : y₂ : 1]`.
private theorem exists_projModelAffinePoint_of_iso {μ ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (e : (levelThreeNormalForm μ).projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = (levelThreeNormalForm μ).projModelOver)
    (he₀ : (levelThreeNormalForm μ).projModelZero ≫ e.hom = W.projModelZero) :
    ∃ (x₁ y₁ x₂ y₂ : R) (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂),
      (levelThreeNormalForm μ).projModelAffinePoint (equation_levelThreeNormalForm_zero μ) ≫
          e.hom = W.projModelAffinePoint h₁ ∧
        (levelThreeNormalForm μ).projModelAffinePoint
          (equation_levelThreeNormalForm_basisPoint μ hζ) ≫ e.hom = W.projModelAffinePoint h₂ := by
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  exact ⟨_, _, _, _, _, _, by rw [heC, hpt], by rw [heC, hpt]⟩

variable [W.IsElliptic]

/-- **Level-three normal form of a projective Weierstrass model.** Let `W` be an elliptic
Weierstrass curve over a commutative ring `R`, and let `P` and `Q` be sections of its projective
model over `Spec R` which meet the zero section over no point of `Spec R`, are killed by
multiplication by `3`, and such that `Q` is neither `P` nor `-P` over any point of `Spec R`. Then
there are unique `μ ζ : R` with `ζ² + ζ + 1 = 0` for which some isomorphism
`projModel (levelThreeNormalForm μ) ≅ projModel W` over `Spec R` carries the zero section to the
zero section, the point `(0, 0)` to `P` and the point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` to
`Q`; such an isomorphism is itself unique (`levelThreeNormalForm_iso_ext`). -/
theorem existsUnique_levelThreeNormalForm {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (hP₃ : P ≫ W.projModelMulBy 3 = W.projModelZero)
    (hQ₃ : Q ≫ W.projModelMulBy 3 = W.projModelZero)
    (hQP : ∀ s, Q s ≠ P s ∧ Q s ≠ (P ≫ W.projModelNeg) s) :
    ∃! μζ : R × R, ∃ hζ : μζ.2 ^ 2 + μζ.2 + 1 = 0,
      ∃ e : (levelThreeNormalForm μζ.1).projModel ≅ W.projModel,
        e.hom ≫ W.projModelOver = (levelThreeNormalForm μζ.1).projModelOver ∧
        (levelThreeNormalForm μζ.1).projModelZero ≫ e.hom = W.projModelZero ∧
        (levelThreeNormalForm μζ.1).projModelAffinePoint
          (equation_levelThreeNormalForm_zero μζ.1) ≫ e.hom = P ∧
        (levelThreeNormalForm μζ.1).projModelAffinePoint
          (equation_levelThreeNormalForm_basisPoint μζ.1 hζ) ≫ e.hom = Q := by
  obtain ⟨x₁, y₁, h₁, rfl⟩ := W.exists_eq_projModelAffinePoint hP hP₀
  obtain ⟨x₂, y₂, h₂, rfl⟩ := W.exists_eq_projModelAffinePoint hQ hQ₀
  have hb := (isThreeTorsionBasis_iff h₁ h₂).mpr ⟨hP₃, hQ₃, hQP⟩
  -- the change of variables `toLevelThreeNormalForm hb` induces the isomorphism
  obtain ⟨he, he₀, hpt⟩ :=
    eqToHom_projModelVariableChangeIso_hom_spec _ (toLevelThreeNormalForm_smul hb)
  refine ⟨(levelThreeParameter hb, levelThreeRootOfUnity hb),
    ⟨levelThreeRootOfUnity_sq_add_levelThreeRootOfUnity_add_one hb,
      eqToIso (congrArg projModel (toLevelThreeNormalForm_smul hb).symm) ≪≫
      W.projModelVariableChangeIso (toLevelThreeNormalForm hb), he, he₀, ?_, ?_⟩, ?_⟩
  · rw [Iso.trans_hom, eqToIso.hom, hpt, projModelAffinePoint_inj]
    simp
  · rw [Iso.trans_hom, eqToIso.hom, hpt, projModelAffinePoint_inj, toLevelThreeNormalForm_r,
      toLevelThreeNormalForm_t]
    exact ⟨(toLevelThreeNormalForm_basisPoint_x hb).symm,
      (toLevelThreeNormalForm_basisPoint_y hb).symm⟩
  · -- any such isomorphism is induced by a change of variables, which determines `μ` and `ζ`
    rintro ⟨μ, ζ⟩ ⟨hζ, e, he, he₀, heP, heQ⟩
    obtain ⟨C, hC, -, hr, ht, hx₂, hy₂⟩ := exists_variableChange_of_iso hζ h₁ h₂ e he he₀ heP heQ
    exact Prod.ext (eq_levelThreeParameter hb hr ht hC hx₂ hy₂)
      (eq_levelThreeRootOfUnity hb hr ht hC hx₂ hy₂)

/-- **The hypotheses of the level-three normal form are necessary.** Two sections `P` and `Q` of
the projective model of an elliptic Weierstrass curve `W` over `Spec R` are the images of the
points `(0, 0)` and `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`, for some `μ` and some root `ζ` of
`ζ² + ζ + 1`, under some isomorphism `projModel (levelThreeNormalForm μ) ≅ projModel W` over
`Spec R` carrying the zero section to the zero section exactly when they meet the zero section over
no point of `Spec R`, are killed by multiplication by `3`, and `Q` is neither `P` nor `-P` over any
point of `Spec R`. -/
theorem exists_iso_levelThreeNormalForm_iff {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _) :
    (∃ (μ ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0) (e : (levelThreeNormalForm μ).projModel ≅ W.projModel),
      e.hom ≫ W.projModelOver = (levelThreeNormalForm μ).projModelOver ∧
        (levelThreeNormalForm μ).projModelZero ≫ e.hom = W.projModelZero ∧
        (levelThreeNormalForm μ).projModelAffinePoint (equation_levelThreeNormalForm_zero μ) ≫
          e.hom = P ∧
        (levelThreeNormalForm μ).projModelAffinePoint
          (equation_levelThreeNormalForm_basisPoint μ hζ) ≫ e.hom = Q) ↔
      (∀ s, P s ≠ W.projModelZero s) ∧ (∀ s, Q s ≠ W.projModelZero s) ∧
        P ≫ W.projModelMulBy 3 = W.projModelZero ∧ Q ≫ W.projModelMulBy 3 = W.projModelZero ∧
        ∀ s, Q s ≠ P s ∧ Q s ≠ (P ≫ W.projModelNeg) s := by
  refine ⟨fun ⟨μ, ζ, hζ, e, he, he₀, heP, heQ⟩ ↦ ?_, fun ⟨hP₀, hQ₀, hP₃, hQ₃, hQP⟩ ↦
    let ⟨⟨μ, ζ⟩, he, _⟩ := existsUnique_levelThreeNormalForm hP hQ hP₀ hQ₀ hP₃ hQ₃ hQP
    ⟨μ, ζ, he⟩⟩
  -- the two sections are points `[x₁ : y₁ : 1]` and `[x₂ : y₂ : 1]` forming a basis of the
  -- `3`-torsion, by a change of variables to level-three normal form
  obtain ⟨x₁, y₁, x₂, y₂, h₁, h₂, hP', hQ'⟩ := exists_projModelAffinePoint_of_iso hζ e he he₀
  obtain ⟨C, hC, -, hr, ht, hx₂, hy₂⟩ := exists_variableChange_of_iso hζ h₁ h₂ e he he₀ hP' hQ'
  rw [hP'] at heP
  rw [hQ'] at heQ
  subst heP heQ
  have hb := (exists_variableChange_levelThreeNormalForm_iff (W := W)).mp
    ⟨C, hr, ht, μ, ζ, hζ, hC, hx₂, hy₂⟩
  refine ⟨fun s ↦ ?_, fun s ↦ ?_, (isThreeTorsionBasis_iff h₁ h₂).mp hb⟩ <;>
    exact (ne_projModelZero_iff_mem_basicOpen (by simp) s).mpr
      (projModelAffinePoint_mem_basicOpen _ s)

/-- **Uniqueness of the isomorphism with a level-three normal form.** Two isomorphisms
`projModel (levelThreeNormalForm μ) ≅ projModel W` over `Spec R` which carry the zero section to the
zero section, and the points `(0, 0)` and `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` to the same two
sections of `projModel W`, are equal. -/
theorem levelThreeNormalForm_iso_ext {μ ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0)
    {e e' : (levelThreeNormalForm μ).projModel ≅ W.projModel}
    (he : e.hom ≫ W.projModelOver = (levelThreeNormalForm μ).projModelOver)
    (he₀ : (levelThreeNormalForm μ).projModelZero ≫ e.hom = W.projModelZero)
    (he' : e'.hom ≫ W.projModelOver = (levelThreeNormalForm μ).projModelOver)
    (he'₀ : (levelThreeNormalForm μ).projModelZero ≫ e'.hom = W.projModelZero)
    (heP : (levelThreeNormalForm μ).projModelAffinePoint (equation_levelThreeNormalForm_zero μ) ≫
      e.hom = (levelThreeNormalForm μ).projModelAffinePoint (equation_levelThreeNormalForm_zero μ) ≫
        e'.hom)
    (heQ : (levelThreeNormalForm μ).projModelAffinePoint
      (equation_levelThreeNormalForm_basisPoint μ hζ) ≫ e.hom =
        (levelThreeNormalForm μ).projModelAffinePoint
          (equation_levelThreeNormalForm_basisPoint μ hζ) ≫ e'.hom) :
    e = e' := by
  -- both are induced by changes of variables `C` and `C'` to level-three normal form at the same
  -- basis of the `3`-torsion
  obtain ⟨x₁, y₁, x₂, y₂, h₁, h₂, hP, hQ⟩ := exists_projModelAffinePoint_of_iso hζ e he he₀
  obtain ⟨C, hC, heC, hr, ht, hx₂, hy₂⟩ := exists_variableChange_of_iso hζ h₁ h₂ e he he₀ hP hQ
  obtain ⟨C', hC', heC', hr', ht', hx₂', hy₂'⟩ := exists_variableChange_of_iso hζ h₁ h₂ e' he'
    he'₀ (heP.symm.trans hP) (heQ.symm.trans hQ)
  have hb := (exists_variableChange_levelThreeNormalForm_iff (W := W)).mp
    ⟨C, hr, ht, μ, ζ, hζ, hC, hx₂, hy₂⟩
  have hCC' : C = C' := (eq_toLevelThreeNormalForm hb hr ht hC hx₂ hy₂).trans
    (eq_toLevelThreeNormalForm hb hr' ht' hC' hx₂' hy₂').symm
  subst hCC'
  exact Iso.ext (heC.trans heC'.symm)

end WeierstrassCurve
