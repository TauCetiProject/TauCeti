/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The Bosma–Lenstra addition morphism commutes with changes of variables

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `C` be a change of
variables over `R`, and let `S = Spec R`. The change of variables induces the isomorphism
`WeierstrassCurve.projModelVariableChangeIso W C : projModel (C • W) ≅ projModel W` over `S`, which
preserves the zero section. This file shows that it also carries the Bosma–Lenstra addition
morphism `WeierstrassCurve.additionMorphism` of `C • W` to that of `W`. This is what compares the
addition morphisms of two local Weierstrass models of an elliptic curve, once the pointed
isomorphism between them is known to be induced by a change of variables.

Over a Noetherian integral domain, the fibre product `projModel (C • W) ×_S projModel (C • W)` is
reduced and `projModel W` is separated, so the two morphisms are compared on points with values in
fields. Such a point is a pair of points with homogeneous coordinates `P` and `Q`. The isomorphism
sends the point with homogeneous coordinates `P` to the point with homogeneous coordinates
`C.toMatrix *ᵥ P`, and the addition morphism sends a pair of points to the point with homogeneous
coordinates the sum `add P Q` of Mathlib's addition of point representatives. The two resulting
points agree because `C.toMatrix *ᵥ add P Q` and `add (C.toMatrix *ᵥ P) (C.toMatrix *ᵥ Q)` are
equivalent (`WeierstrassCurve.Projective.toMatrix_mulVec_add_equiv`).

An elliptic Weierstrass curve `W` over an arbitrary commutative ring is the base change of one,
`W₀`, over a Noetherian integral domain `R₀` (`WeierstrassCurve.exists_map_eq_of_isElliptic`).
Adjoining to `R₀` the coefficients `u`, `r`, `s` and `t` of a universal change of variables, with
`u` inverted, gives a Noetherian integral domain `R₁`, and the pair `(W, C)` is the base change of
a pair over `R₁` (`WeierstrassCurve.exists_map_eq_and_map_eq_of_isElliptic`). The compatibility
passes to base changes, because the addition morphism and the isomorphism induced by a change of
variables both commute with base change
(`WeierstrassCurve.additionMorphism_projModelBaseChange` and
`WeierstrassCurve.projModelVariableChangeIso_hom_projModelBaseChange`).

## Main results

* `WeierstrassCurve.additionMorphism_projModelVariableChangeIso_hom`: the addition morphism of
  `C • W` followed by the isomorphism `projModel (C • W) ≅ projModel W` is the isomorphism on both
  factors followed by the addition morphism of `W`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

section Field

open Matrix Projective

-- The addition morphism and the isomorphism induced by `C` commute on every point of
-- `projModel (C • W) ×_S projModel (C • W)` with values in a field.
private theorem comp_additionMorphism_projModelVariableChangeIso_hom [W.IsElliptic]
    {K : Type u} [Field K]
    (p : Spec (.of K) ⟶ pullback (C • W).projModelOver (C • W).projModelOver) :
    p ≫ (C • W).additionMorphism ≫ (W.projModelVariableChangeIso C).hom =
      p ≫ pullback.map _ _ _ _ (W.projModelVariableChangeIso C).hom
        (W.projModelVariableChangeIso C).hom (𝟙 _) (by simp) (by simp) ≫ W.additionMorphism := by
  -- `p` is the pair of the points with homogeneous coordinates `P` and `Q`
  obtain ⟨g, P, Q, hP, hQ, i, j, hi, hj, rfl⟩ := (C • W).exists_eq_lift_projModelPoint p
  -- a solution with a nonzero coordinate on an elliptic curve over a field is nonsingular
  have hP' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨i, hi.ne_zero⟩)).mp hP
  have hQ' := (equation_iff_nonsingular_of_ne_zero (Function.ne_iff.mpr ⟨j, hj.ne_zero⟩)).mp hQ
  -- read on `C.map g • W.map g`, which is `(C • W).map g`
  have hP₁ : (C.map g • W.map g).toProjective.Nonsingular P := by
    simpa only [map_variableChange] using hP'
  have hQ₁ : (C.map g • W.map g).toProjective.Nonsingular Q := by
    simpa only [map_variableChange] using hQ'
  -- the images of `P`, `Q` and of their sum under the change of variables are nonsingular, so
  -- each of them, and the sum of the first two, has a unit coordinate
  have hMP := (nonsingular_variableChange _ _ P).mp hP₁
  have hMQ := (nonsingular_variableChange _ _ Q).mp hQ₁
  have hMS := (nonsingular_variableChange _ _ _).mp (nonsingular_add hP₁ hQ₁)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular hMP)
  obtain ⟨l, hl⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular hMQ)
  obtain ⟨m, hm⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hP' hQ'))
  obtain ⟨n, hn⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular hMS)
  obtain ⟨o, ho⟩ := Function.ne_iff.mp (ne_zero_of_nonsingular (nonsingular_add hMP hMQ))
  -- on the left, the sum `add P Q` is carried to `C.toMatrix *ᵥ add P Q`
  rw [reassoc_of% ((C • W).lift_projModelPoint_additionMorphism_eq_add hi hj hm.isUnit),
    projModelPoint_projModelVariableChangeIso_hom hm.isUnit (j := n)
      (by simpa only [map_variableChange] using hn.isUnit)]
  -- on the right, `P` and `Q` are carried to `C.toMatrix *ᵥ P` and `C.toMatrix *ᵥ Q`, and then
  -- to their sum
  have hpair : pullback.lift ((C • W).projModelPoint g hP hi) ((C • W).projModelPoint g hQ hj)
      ((projModelPoint_projModelOver _ g hP hi).trans
        (projModelPoint_projModelOver _ g hQ hj).symm) ≫
      pullback.map _ _ _ _ (W.projModelVariableChangeIso C).hom
        (W.projModelVariableChangeIso C).hom (𝟙 _) (by simp) (by simp) =
      pullback.lift (W.projModelPoint g hMP.1 hk.isUnit) (W.projModelPoint g hMQ.1 hl.isUnit)
        ((projModelPoint_projModelOver _ g _ _).trans
          (projModelPoint_projModelOver _ g _ _).symm) := by
    apply pullback.hom_ext <;>
      simp [projModelPoint_projModelVariableChangeIso_hom hi hk.isUnit,
        projModelPoint_projModelVariableChangeIso_hom hj hl.isUnit]
  rw [reassoc_of% hpair, W.lift_projModelPoint_additionMorphism_eq_add hk.isUnit hl.isUnit
    ho.isUnit, projModelPoint_eq_projModelPoint_iff]
  -- and the two sums are equivalent
  obtain ⟨v, hv⟩ := toMatrix_mulVec_add_equiv (C.map g) hP₁ hQ₁
  refine ⟨rfl, v, ?_⟩
  simpa only [map_variableChange] using hv.symm

end Field

-- The addition morphism commutes with the isomorphism induced by `C` whenever
-- `projModel (C • W) ×_S projModel (C • W)` is reduced, as it is over a Noetherian integral
-- domain: `projModel W` is a separated scheme, so it suffices that the two sides agree on the
-- points with values in its residue fields.
private theorem additionMorphism_projModelVariableChangeIso_hom_of_isReduced [W.IsElliptic]
    [IsReduced (pullback (C • W).projModelOver (C • W).projModelOver)] :
    (C • W).additionMorphism ≫ (W.projModelVariableChangeIso C).hom =
      pullback.map _ _ _ _ (W.projModelVariableChangeIso C).hom
        (W.projModelVariableChangeIso C).hom (𝟙 _) (by simp) (by simp) ≫ W.additionMorphism :=
  ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ dense_univ
    (fun x _ ↦ W.comp_additionMorphism_projModelVariableChangeIso_hom C
      (Scheme.fromSpecResidueField _ x))
    (terminal.hom_ext _ _)

section Transport

variable {V V' : WeierstrassCurve R}

-- If a morphism `e : projModel V ⟶ projModel W` over the base carries the addition morphism of
-- `V` to that of `W`, then so does a morphism `e'` over the base between the base changes along
-- `f : R →+* R'` which lies over `e`.
private theorem additionMorphism_comp_map_of_additionMorphism_comp [V.IsElliptic] [W.IsElliptic]
    {R' : Type u} [CommRing R'] (f : R →+* R') {e : V.projModel ⟶ W.projModel}
    (he : e ≫ W.projModelOver = V.projModelOver)
    (h : V.additionMorphism ≫ e = pullback.map _ _ _ _ e e (𝟙 _) (by simp [he]) (by simp [he]) ≫
      W.additionMorphism)
    {e' : (V.map f).projModel ⟶ (W.map f).projModel}
    (he' : e' ≫ (W.map f).projModelOver = (V.map f).projModelOver)
    (hbc : e' ≫ W.projModelBaseChange f = V.projModelBaseChange f ≫ e) :
    (V.map f).additionMorphism ≫ e' = pullback.map _ _ _ _ e' e' (𝟙 _) (by simp [he'])
      (by simp [he']) ≫ (W.map f).additionMorphism := by
  -- a morphism to `projModel (W.map f)`, the base change of `projModel W` along `Spec f`, is
  -- determined by its composites with the base change morphism and with the structure morphism
  refine (W.isPullback_projModelBaseChange f).hom_ext ?_ ?_
  · -- both addition morphisms commute with base change, and `e'` lies over `e`
    simp only [Category.assoc]
    rw [hbc, additionMorphism_projModelBaseChange_assoc, h, additionMorphism_projModelBaseChange,
      ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [hbc]
  · -- both sides lie over `Spec R'`
    simp [he', pullback.condition]

-- The compatibility of the addition morphisms with a morphism `e` survives replacing the source
-- curve `V` by an equal curve `V'`.
private theorem additionMorphism_eqToHom_comp [V.IsElliptic] [V'.IsElliptic] [W.IsElliptic]
    (hV : V' = V) {e : V.projModel ⟶ W.projModel} (he : e ≫ W.projModelOver = V.projModelOver)
    (h : V.additionMorphism ≫ e = pullback.map _ _ _ _ e e (𝟙 _) (by simp [he]) (by simp [he]) ≫
      W.additionMorphism) :
    V'.additionMorphism ≫ eqToHom (congrArg projModel hV) ≫ e =
      pullback.map _ _ _ _ (eqToHom (congrArg projModel hV) ≫ e)
        (eqToHom (congrArg projModel hV) ≫ e) (𝟙 _) (by subst hV; simp [he])
        (by subst hV; simp [he]) ≫ W.additionMorphism := by
  subst hV
  simpa using h

end Transport

/-- **The addition morphism commutes with changes of variables.** Let `W` be an elliptic
Weierstrass curve over `R` and `C` a change of variables, and write `S = Spec R`. The
Bosma–Lenstra addition morphism of `C • W`, followed by the isomorphism
`projModel (C • W) ≅ projModel W` induced by `C`, is the isomorphism on both factors
`projModel (C • W) ×_S projModel (C • W) ⟶ projModel W ×_S projModel W`, followed by the addition
morphism of `W`. -/
@[reassoc (attr := simp)]
theorem additionMorphism_projModelVariableChangeIso_hom [W.IsElliptic] :
    (C • W).additionMorphism ≫ (W.projModelVariableChangeIso C).hom =
      pullback.map _ _ _ _ (W.projModelVariableChangeIso C).hom
        (W.projModelVariableChangeIso C).hom (𝟙 _) (by simp) (by simp) ≫ W.additionMorphism := by
  -- `(W, C)` is the base change of a pair `(W₁, C₁)` over a Noetherian integral domain, over which
  -- the fibre product is reduced
  obtain ⟨R₁, _, _, _, W₁, _, C₁, g, rfl, rfl⟩ := W.exists_map_eq_and_map_eq_of_isElliptic C
  -- the isomorphism induced by `C₁.map g` lies over the one induced by `C₁`, through the
  -- identification of `C₁.map g • W₁.map g` with `(C₁ • W₁).map g`
  have hV := map_variableChange W₁ C₁ g
  -- the identification lies over `Spec R`
  have hVo : eqToHom (congrArg projModel hV.symm) ≫ (C₁.map g • W₁.map g).projModelOver =
      ((C₁ • W₁).map g).projModelOver := by
    simpa using (eqToHom_naturality (fun V : WeierstrassCurve R ↦ V.projModelOver) hV.symm).symm
  have h := additionMorphism_comp_map_of_additionMorphism_comp W₁ g (V := C₁ • W₁) (by simp)
    (W₁.additionMorphism_projModelVariableChangeIso_hom_of_isReduced C₁)
    (e' := eqToHom (congrArg projModel hV.symm) ≫
      ((W₁.map g).projModelVariableChangeIso (C₁.map g)).hom) (by simp [hVo])
    (by rw [Category.assoc, projModelVariableChangeIso_hom_projModelBaseChange,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp])
  simpa using (W₁.map g).additionMorphism_eqToHom_comp hV (by simp [hVo]) h

end WeierstrassCurve
