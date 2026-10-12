/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateNormalForm
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Tate normal form of a pointed projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R` and let `P` be a section of
its projective model `projModel W ⟶ Spec R`. Suppose that none of `P`, `2P` and `3P` meets the
zero section over any point of `Spec R`. Then there are unique `a b : R` and a unique isomorphism

`projModel (tateNormalForm a b) ≅ projModel W`

over `Spec R` carrying the zero section to the zero section and the point `(0, 0)` of the Tate
normal form `Y² + aXY + bY = X³ + bX²` to `P` (`WeierstrassCurve.existsUnique_tateNormalForm`
and `WeierstrassCurve.tateNormalForm_iso_ext`). Conversely, a section which is the image of
`(0, 0)` under such an isomorphism satisfies the three conditions
(`WeierstrassCurve.exists_iso_tateNormalForm_iff`). No hypothesis on `R` is needed; in
particular `R` may be nonreduced.

This is the scheme-theoretic form of the equation-level Tate normal form
`WeierstrassCurve.existsUnique_variableChange_tateNormalForm`. A section missing the zero section
everywhere is the point `[x : y : 1]` of a solution `(x, y)` of the affine equation
(`WeierstrassCurve.exists_eq_projModelAffinePoint`). Its multiple `nP` misses the zero section
everywhere exactly when the value `ψₙ(x, y)` of the `n`-th division polynomial is a unit
(`WeierstrassCurve.isUnit_evalEval_ψ_iff`), so the conditions on `2P` and `3P` say that `ψ₂(x, y)`
and `Ψ₃(x)` are units. An isomorphism of projective models over `Spec R` preserving the zero
sections is a change of variables
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`), and one carrying
`(0, 0)` to `(x, y)` has `r = x` and `t = y`.

## Main results

* `WeierstrassCurve.existsUnique_tateNormalForm`: a section `P` such that `P`, `2P` and `3P` miss
  the zero section everywhere is the image of `(0, 0)` under a pointed isomorphism from the
  projective model of a Tate normal form, for unique coefficients `a` and `b`.
* `WeierstrassCurve.tateNormalForm_iso_ext`: such an isomorphism is unique.
* `WeierstrassCurve.exists_iso_tateNormalForm_iff`: such an isomorphism exists exactly when `P`,
  `2P` and `3P` miss the zero section everywhere.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 8.13.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

-- The isomorphism `projModel W' ≅ projModel W` induced by a change of variables `C` with
-- `C • W = W'` is pointed, lies over `Spec R`, and carries `[0 : 0 : 1]` to `[r : t : 1]`.
private theorem projModelVariableChangeIso_eqToHom_spec {W' : WeierstrassCurve R}
    (C : VariableChange R) (hC : C • W = W') (h₀ : W'.toAffine.Equation 0 0) :
    (eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom) ≫
        W.projModelOver = W'.projModelOver ∧
      W'.projModelZero ≫ eqToHom (congrArg projModel hC.symm) ≫
        (W.projModelVariableChangeIso C).hom = W.projModelZero ∧
      ∃ hrt : W.toAffine.Equation C.r C.t, W'.projModelAffinePoint h₀ ≫
        eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom =
          W.projModelAffinePoint hrt := by
  subst hC
  have hrt := (Affine.variableChange_equation W C 0 0).mpr h₀
  simp only [mul_zero, zero_add] at hrt
  refine ⟨by simp, by simp, hrt, ?_⟩
  rw [eqToHom_refl, Category.id_comp, projModelAffinePoint_projModelVariableChangeIso_hom,
    projModelAffinePoint_inj]
  simp

-- A pointed isomorphism over `Spec R` from the projective model of `W'` to that of `W` is induced
-- by a change of variables `C` with `C • W = W'`, and it carries `[0 : 0 : 1]` to `[r : t : 1]`.
private theorem exists_variableChange_of_iso {W' : WeierstrassCurve R}
    (h₀ : W'.toAffine.Equation 0 0) (e : W'.projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = W'.projModelOver)
    (he₀ : W'.projModelZero ≫ e.hom = W.projModelZero) :
    ∃ C : VariableChange R, ∃ hC : C • W = W', ∃ hrt : W.toAffine.Equation C.r C.t,
      e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom ∧
        W'.projModelAffinePoint h₀ ≫ e.hom = W.projModelAffinePoint hrt := by
  obtain ⟨C, ⟨hC, hCe⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hrt, hP⟩ := projModelVariableChangeIso_eqToHom_spec C hC h₀
  exact ⟨C, hC, hrt, hCe, hCe ▸ hP⟩

variable [W.IsElliptic]

-- `2P` and `3P` miss the zero section everywhere exactly when `ψ₂(x, y)` and `Ψ₃(x)` are units,
-- for `P` the point `[x : y : 1]`.
private theorem isUnit_ψ₂_and_isUnit_Ψ₃_iff {x y : R} (h : W.toAffine.Equation x y) :
    IsUnit (W.ψ₂.evalEval x y) ∧ IsUnit (W.Ψ₃.eval x) ↔
      (∀ s, (W.projModelAffinePoint h ≫ W.projModelMulBy 2) s ≠ W.projModelZero s) ∧
        ∀ s, (W.projModelAffinePoint h ≫ W.projModelMulBy 3) s ≠ W.projModelZero s := by
  rw [← isUnit_evalEval_ψ_iff h 2, ← isUnit_evalEval_ψ_iff h 3, ψ_two, ψ_three,
    Polynomial.evalEval_C]

/-- **Tate normal form of a pointed projective Weierstrass model.** Let `W` be an elliptic
Weierstrass curve over a commutative ring `R` and `P` a section of its projective model over
`Spec R` such that none of `P`, `2P` and `3P` meets the zero section over any point of `Spec R`.
Then there are unique `a b : R` for which some isomorphism
`projModel (tateNormalForm a b) ≅ projModel W` over `Spec R` carries the zero section to the zero
section and the point `(0, 0)` to `P`; such an isomorphism is itself unique
(`tateNormalForm_iso_ext`). -/
theorem existsUnique_tateNormalForm {P : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (h₁ : ∀ s, P s ≠ W.projModelZero s)
    (h₂ : ∀ s, (P ≫ W.projModelMulBy 2) s ≠ W.projModelZero s)
    (h₃ : ∀ s, (P ≫ W.projModelMulBy 3) s ≠ W.projModelZero s) :
    ∃! ab : R × R, ∃ e : (tateNormalForm ab.1 ab.2).projModel ≅ W.projModel,
      e.hom ≫ W.projModelOver = (tateNormalForm ab.1 ab.2).projModelOver ∧
        (tateNormalForm ab.1 ab.2).projModelZero ≫ e.hom = W.projModelZero ∧
        (tateNormalForm ab.1 ab.2).projModelAffinePoint
          (equation_tateNormalForm_zero ab.1 ab.2) ≫ e.hom = P := by
  obtain ⟨x, y, h, rfl⟩ := W.exists_eq_projModelAffinePoint hP h₁
  -- `2P` and `3P` miss the zero section, so `ψ₂(x, y)` and `Ψ₃(x)` are units
  obtain ⟨hψ₂, hΨ₃⟩ := (isUnit_ψ₂_and_isUnit_Ψ₃_iff h).mpr ⟨h₂, h₃⟩
  have hC := toTateNormalForm_smul hψ₂ hΨ₃ h
  obtain ⟨he, he₀, hrt, heP⟩ := projModelVariableChangeIso_eqToHom_spec _ hC
    (equation_tateNormalForm_zero _ _)
  refine ⟨(_, _), ⟨eqToIso (congrArg projModel hC.symm) ≪≫
    W.projModelVariableChangeIso (toTateNormalForm hψ₂ hΨ₃), he, he₀, ?_⟩, ?_⟩
  · rw [Iso.trans_hom, eqToIso.hom, heP, projModelAffinePoint_inj]
    simp
  · -- any such isomorphism is induced by `toTateNormalForm`, which determines `a` and `b`
    rintro ⟨a, b⟩ ⟨e, he, he₀, heP⟩
    obtain ⟨C, hC', hrt, -, heC⟩ := exists_variableChange_of_iso _ e he he₀
    rw [heC, projModelAffinePoint_inj] at heP
    rw [eq_toTateNormalForm hψ₂ hΨ₃ heP.1 heP.2 hC'] at hC'
    have hCt := hC'.symm.trans hC
    exact Prod.ext (by simpa using congrArg a₁ hCt) (by simpa using congrArg a₃ hCt)

/-- **The hypotheses of the Tate normal form are necessary.** A section `P` of the projective model
of an elliptic Weierstrass curve `W` over `Spec R` is the image of the point `(0, 0)` under some
isomorphism `projModel (tateNormalForm a b) ≅ projModel W` over `Spec R` carrying the zero section
to the zero section exactly when none of `P`, `2P` and `3P` meets the zero section over any point
of `Spec R`. -/
theorem exists_iso_tateNormalForm_iff {P : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) :
    (∃ (a b : R) (e : (tateNormalForm a b).projModel ≅ W.projModel),
      e.hom ≫ W.projModelOver = (tateNormalForm a b).projModelOver ∧
        (tateNormalForm a b).projModelZero ≫ e.hom = W.projModelZero ∧
        (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫ e.hom = P) ↔
      (∀ s, P s ≠ W.projModelZero s) ∧ (∀ s, (P ≫ W.projModelMulBy 2) s ≠ W.projModelZero s) ∧
        ∀ s, (P ≫ W.projModelMulBy 3) s ≠ W.projModelZero s := by
  refine ⟨fun ⟨a, b, e, he, he₀, heP⟩ ↦ ?_, fun ⟨h₁, h₂, h₃⟩ ↦
    let ⟨⟨a, b⟩, he, _⟩ := existsUnique_tateNormalForm hP h₁ h₂ h₃; ⟨a, b, he⟩⟩
  -- `P` is the point `[r : t : 1]` for a change of variables to Tate normal form centred there
  obtain ⟨C, hC, hrt, -, heC⟩ := exists_variableChange_of_iso _ e he he₀
  subst heP
  rw [heC]
  obtain ⟨-, hψ₂, hΨ₃⟩ := (exists_variableChange_tateNormalForm_iff (W := W)).mp
    ⟨C, rfl, rfl, a, b, hC⟩
  exact ⟨fun s ↦ (ne_projModelZero_iff_mem_basicOpen (by simp) s).mpr
    (projModelAffinePoint_mem_basicOpen hrt s), (isUnit_ψ₂_and_isUnit_Ψ₃_iff hrt).mp ⟨hψ₂, hΨ₃⟩⟩

/-- **Uniqueness of the isomorphism with a Tate normal form.** Two isomorphisms
`projModel (tateNormalForm a b) ≅ projModel W` over `Spec R` which carry the zero section to the
zero section and the point `(0, 0)` to the same section of `projModel W` are equal. -/
theorem tateNormalForm_iso_ext {a b : R} {e e' : (tateNormalForm a b).projModel ≅ W.projModel}
    (he : e.hom ≫ W.projModelOver = (tateNormalForm a b).projModelOver)
    (he₀ : (tateNormalForm a b).projModelZero ≫ e.hom = W.projModelZero)
    (he' : e'.hom ≫ W.projModelOver = (tateNormalForm a b).projModelOver)
    (he'₀ : (tateNormalForm a b).projModelZero ≫ e'.hom = W.projModelZero)
    (hee' : (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫ e.hom =
      (tateNormalForm a b).projModelAffinePoint (equation_tateNormalForm_zero a b) ≫ e'.hom) :
    e = e' := by
  -- both are induced by changes of variables `C` and `C'` carrying `(0, 0)` to the same point
  obtain ⟨C, hC, hrt, heC, heP⟩ := exists_variableChange_of_iso _ e he he₀
  obtain ⟨C', hC', hrt', heC', heP'⟩ := exists_variableChange_of_iso _ e' he' he'₀
  rw [heP, heP', projModelAffinePoint_inj] at hee'
  -- at that point `ψ₂` and `Ψ₃` are units, so both are the change of variables to Tate normal form
  obtain ⟨-, hψ₂, hΨ₃⟩ := (exists_variableChange_tateNormalForm_iff (W := W)).mp
    ⟨C, rfl, rfl, a, b, hC⟩
  have hCC' : C = C' := (eq_toTateNormalForm hψ₂ hΨ₃ rfl rfl hC).trans
    (eq_toTateNormalForm hψ₂ hΨ₃ hee'.1.symm hee'.2.symm hC').symm
  subst hCC'
  exact Iso.ext (heC.trans heC'.symm)

end WeierstrassCurve
