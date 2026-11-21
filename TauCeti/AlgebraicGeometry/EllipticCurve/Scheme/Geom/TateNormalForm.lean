/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.TateNormalForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange

/-!
# The universal Tate normal form over a scheme

Let `E` be an elliptic curve over a scheme `S` and let `P` be a section of `E` such that none of
`P`, `2P` and `3P` meets the zero section over any point of `S`. Then `(E, P)` is the pullback of
the universal Tate normal form

`Y² + AXY + BY = X³ + BX²`

over `Spec ℤ[A, B][Δ⁻¹]`, with its point `(0, 0)`, along exactly one morphism
`S ⟶ Spec ℤ[A, B][Δ⁻¹]`, and by exactly one cartesian morphism from `E` carrying the zero section
to the zero section and `P` to `(0, 0)` (`EllipticCurveGeom.existsUnique_tateNormalForm`).
Conversely, a point which is such a pullback of `(0, 0)` satisfies the three conditions: it is a
Tate point (`EllipticCurveGeom.exists_tateNormalForm_iff`). So `Spec ℤ[A, B][Δ⁻¹]` is a fine moduli
scheme for elliptic curves with a section `P` such that `P`, `2P` and `3P` are nowhere the zero
section, with universal family the projective model of the universal Tate normal form. No hypothesis
on `S` is needed; in particular `S` may be nonreduced or non-affine. By the uniqueness of the
classifying morphism, an automorphism of `E` over `S` fixing the zero section and `P` is the
identity (`EllipticCurveGeom.eq_id_of_isPullback_of_comp_eq`).

The sections to which the Tate normal form applies are the **Tate points**
(`EllipticCurveGeom.IsTatePoint`): those lying at every point of `S` in the **Tate locus**
(`EllipticCurveGeom.tateLocus`), the open subset of points `e` of `E` such that none of `e`, `2e`
and `3e` lies on the zero section. Tate points are stable under base change, and on a base change
they are read off the Tate locus of the original curve
(`EllipticCurveGeom.isTatePoint_iff_of_isPullback`).

The coefficient ring `ℤ[A, B][Δ⁻¹]` (`WeierstrassCurve.UniversalTate.Ring`) lies in `Type`. For
schemes in an arbitrary universe the universal Tate normal form is read over its copy
`ULift.{u} ℤ[A, B][Δ⁻¹]` (`WeierstrassCurve.UniversalTate.curveULift`).

## Main definitions

* `WeierstrassCurve.UniversalTate.point`: the point `(0, 0)` of the projective model of the
  universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]`.
* `TauCeti.AlgebraicGeometry.UniversalTate.curveGeom`: the universal Tate normal form as an
  elliptic curve over `Spec ℤ[A, B][Δ⁻¹]`.
* `TauCeti.AlgebraicGeometry.UniversalTate.pointHom`: its point `(0, 0)`, with values in the base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.tateLocus`: the open subset of points `e` of `E`
  such that none of `e`, `2e` and `3e` lies on the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsTatePoint`: a section of `E` lying in the Tate
  locus at every point of the base.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_tateNormalForm`: a section `P` such
  that `P`, `2P` and `3P` miss the zero section everywhere is the pullback of `(0, 0)` along a
  unique cartesian pointed morphism to the universal Tate normal form.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_tateNormalForm_iff`: such a morphism exists
  exactly when `P` is a Tate point, that is, `P`, `2P` and `3P` miss the zero section everywhere.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_id_of_isPullback_of_comp_eq`: an automorphism
  of `E` over `S` fixing such a section `P` is the identity.

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_tateNormalForm_curveGeom`: the same
  universal property, with the universal Tate normal form read as the elliptic curve `curveGeom`.
* `WeierstrassCurve.UniversalTate.smoothOfRelativeDimension_terminal_from`: the base
  `Spec ℤ[A, B][Δ⁻¹]` of the universal Tate normal form is smooth of relative dimension two over
  `Spec ℤ`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isTatePoint_iff`: a Tate point is a section `P`
  such that none of `P`, `2P` and `3P` meets the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isTatePoint_iff_of_isPullback` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsTatePoint.pointsPullback`: Tate points of a base
  change, and their stability under base change.
* `TauCeti.AlgebraicGeometry.UniversalTate.isTatePoint_pointHom`: the point `(0, 0)` of the
  universal Tate normal form is a Tate point.
* `WeierstrassCurve.UniversalTate.point_ne_projModelZero`,
  `WeierstrassCurve.UniversalTate.point_projModelMulBy_two_ne_projModelZero` and
  `WeierstrassCurve.UniversalTate.point_projModelMulBy_three_ne_projModelZero`: the universal point
  satisfies the three conditions.

## References

* D. Loeffler, *Modular Curves*, lecture notes, §3.3, for Tate normal form and `Y₁(N)`.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 8.13.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Chapter 4, for fine moduli schemes of elliptic curves with
  level structure.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve.UniversalTate

/-- The point `(0, 0)` of the universal Tate normal form. -/
noncomputable def point : Spec (.of (ULift.{u} Ring)) ⟶ curveULift.{u}.projModel :=
  curveULift.projModelAffinePoint equation_curveULift_zero

/-- The universal point is the point `[0 : 0 : 1]` of the projective model. -/
@[simp]
theorem point_def :
    point.{u} = curveULift.projModelAffinePoint equation_curveULift_zero :=
  (rfl)

/-- The universal point is a section of the projective model of the universal Tate normal form. -/
-- Not `@[simp]`: `simp` proves it from `point_def` and `projModelAffinePoint_projModelOver`.
@[reassoc]
theorem point_projModelOver : point.{u} ≫ curveULift.projModelOver = 𝟙 _ := by
  rw [point_def, projModelAffinePoint_projModelOver]

-- The universal point satisfies the three conditions of the Tate normal form: it is the image of
-- `(0, 0)` under the identity of the universal Tate normal form.
private theorem point_conditions :
    (∀ s, point.{u} s ≠ curveULift.projModelZero s) ∧
      (∀ s, (point.{u} ≫ curveULift.projModelMulBy 2) s ≠ curveULift.projModelZero s) ∧
        ∀ s, (point.{u} ≫ curveULift.projModelMulBy 3) s ≠ curveULift.projModelZero s := by
  -- `curveULift` is opaque, so the identity of a Tate normal form is applied through its
  -- characterization `curveULift_eq_tateNormalForm`
  have key {W : WeierstrassCurve (ULift.{u} Ring)} [W.IsElliptic]
      (hW : W = tateNormalForm curveULift.a₁ curveULift.a₃) (h : W.toAffine.Equation 0 0) :
      (∀ s, W.projModelAffinePoint h s ≠ W.projModelZero s) ∧
        (∀ s, (W.projModelAffinePoint h ≫ W.projModelMulBy 2) s ≠ W.projModelZero s) ∧
          ∀ s, (W.projModelAffinePoint h ≫ W.projModelMulBy 3) s ≠ W.projModelZero s := by
    subst hW
    exact (exists_iso_tateNormalForm_iff (projModelAffinePoint_projModelOver _)).mp
      ⟨_, _, Iso.refl _, by simp, by simp, by simp⟩
  rw [point_def]
  exact key curveULift_eq_tateNormalForm equation_curveULift_zero

/-- The universal point `(0, 0)` misses the zero section at every point of the base. -/
theorem point_ne_projModelZero (s) : point.{u} s ≠ curveULift.projModelZero s :=
  point_conditions.1 s

/-- Twice the universal point misses the zero section at every point of the base. -/
theorem point_projModelMulBy_two_ne_projModelZero (s) :
    (point.{u} ≫ curveULift.projModelMulBy 2) s ≠ curveULift.projModelZero s :=
  point_conditions.2.1 s

/-- Three times the universal point misses the zero section at every point of the base. -/
theorem point_projModelMulBy_three_ne_projModelZero (s) :
    (point.{u} ≫ curveULift.projModelMulBy 3) s ≠ curveULift.projModelZero s :=
  point_conditions.2.2 s

/-! ### Smoothness of the base -/

/-- The base `Spec ℤ[A, B][Δ⁻¹]` of the universal Tate normal form is smooth of relative dimension
two over `Spec ℤ`, the terminal scheme: it is an open subscheme of the affine plane. -/
instance smoothOfRelativeDimension_terminal_from :
    SmoothOfRelativeDimension 2 (terminal.from (Spec (.of (ULift.{u} Ring)))) := by
  let e₁ : ULift.{u} ℤ ≃+* ℤ := ULift.ringEquiv
  let e₂ : Ring ≃+* ULift.{u} Ring := ULift.ringEquiv.symm
  let f : ULift.{u} ℤ →+* ULift.{u} Ring :=
    (e₂ : Ring →+* ULift.{u} Ring).comp ((algebraMap ℤ Ring).comp (e₁ : ULift.{u} ℤ →+* ℤ))
  -- `ℤ[A, B][Δ⁻¹]` is a localisation away from one element of the polynomial ring `ℤ[A, B]`
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) ℤ) Ring :=
    .localization_away polyCurve.Δ
  have : Algebra.IsStandardSmoothOfRelativeDimension 2 ℤ Ring :=
    .trans (n := 2) (m := 0) ℤ (MvPolynomial (Fin 2) ℤ) Ring
  have hf : f.IsStandardSmoothOfRelativeDimension (0 + (2 + 0)) :=
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₂).comp
      (((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 2).mpr inferInstance).comp
        (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₁))
  have : SmoothOfRelativeDimension 2 (Spec.map (CommRingCat.ofHom f)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hf
  have e := specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal
  rw [terminal.hom_ext (terminal.from _) (Spec.map (CommRingCat.ofHom f) ≫ e.hom)]
  exact inferInstanceAs (SmoothOfRelativeDimension (2 + 0) _)

/-- The base `Spec ℤ[A, B][Δ⁻¹]` of the universal Tate normal form is smooth over `Spec ℤ`, the
terminal scheme. -/
instance smooth_terminal_from : Smooth (terminal.from (Spec (.of (ULift.{u} Ring)))) :=
  SmoothOfRelativeDimension.smooth 2 _

end WeierstrassCurve.UniversalTate

namespace TauCeti.AlgebraicGeometry.UniversalTate

open WeierstrassCurve MonoidalCategory

/-! ### The universal Tate normal form as an elliptic curve -/

/-- The universal Tate normal form `Y² + AXY + BY = X³ + BX²` as an elliptic curve over
`Spec ℤ[A, B][Δ⁻¹]`, whose total space is the projective model of `curveULift`. -/
noncomputable abbrev curveGeom : EllipticCurveGeom (Spec (.of (ULift.{u} UniversalTate.Ring))) :=
  toEllipticCurveGeom UniversalTate.curveULift

/-- The point `(0, 0)` of the universal Tate normal form, as a point with values in the base of
the elliptic curve `curveGeom`. -/
noncomputable def pointHom :
    𝟙_ (Over (Spec (.of (ULift.{u} UniversalTate.Ring)))) ⟶ Over.mk curveGeom.{u}.structureMap :=
  Over.homMk (UniversalTate.point ≫ (toEllipticCurveGeomIso UniversalTate.curveULift).inv) <| by
    simp [← toEllipticCurveGeomIso_hom_projModelOver]

/-- On the projective model, the point `(0, 0)` of `curveGeom` is `point`. -/
@[simp]
theorem pointHom_left :
    pointHom.{u}.left =
      UniversalTate.point ≫ (toEllipticCurveGeomIso UniversalTate.curveULift).inv :=
  (rfl)

end TauCeti.AlgebraicGeometry.UniversalTate

namespace TauCeti.AlgebraicGeometry

open WeierstrassCurve UniversalTate

/-! ### Classifying pairs -/

-- `(f, g)` classifies the pointed curve `(π, zero, P)`: `g` exhibits `X` as the base change of the
-- universal Tate normal form along `f`, carrying `zero` to the zero section and `P` to `(0, 0)`.
private def IsTate {X T : Scheme.{u}} (π : X ⟶ T) (zero P : T ⟶ X)
    (f : T ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) (g : X ⟶ curveULift.{u}.projModel) :
    Prop :=
  IsPullback g π curveULift.projModelOver f ∧ zero ≫ g = f ≫ curveULift.projModelZero ∧
    P ≫ g = f ≫ point

-- Classifying pairs pull back along cartesian squares.
private theorem IsTate.comp {X T X' T' : Scheme.{u}} {π : X ⟶ T} {zero P : T ⟶ X}
    {f : T ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))} {g : X ⟶ curveULift.{u}.projModel}
    (h : IsTate π zero P f g) {π' : X' ⟶ T'} {zero' P' : T' ⟶ X'} {a : X' ⟶ X} {b : T' ⟶ T}
    (hab : IsPullback a π' π b) (h₀ : zero' ≫ a = b ≫ zero) (hP : P' ≫ a = b ≫ P) :
    IsTate π' zero' P' (b ≫ f) (a ≫ g) :=
  ⟨hab.paste_horiz h.1, by simp [reassoc_of% h₀, h.2.1], by simp [reassoc_of% hP, h.2.2]⟩

/-! ### Over an affine base -/

section Affine

variable {R : Type u} [CommRing R]

-- The base change morphism to the universal Tate normal form along `φ`, read on a curve `W'` equal
-- to the base change `curveULift.map φ`, is cartesian over `Spec φ`, pointed, and carries `(0, 0)`
-- to the universal point.
private theorem isTate_eqToHom_projModelBaseChange (φ : ULift.{u} UniversalTate.Ring →+* R)
    {W' : WeierstrassCurve R} (hW' : curveULift.map φ = W') (h : W'.toAffine.Equation 0 0) :
    IsTate W'.projModelOver W'.projModelZero (W'.projModelAffinePoint h)
      (Spec.map (CommRingCat.ofHom φ))
      (eqToHom (congrArg projModel hW'.symm) ≫ curveULift.projModelBaseChange φ) := by
  subst hW'
  refine ⟨by simpa using curveULift.isPullback_projModelBaseChange φ, by simp, ?_⟩
  have h' : (curveULift.map φ).projModelAffinePoint h =
      (curveULift.map φ).projModelAffinePoint (equation_curveULift_zero.map φ) :=
    (projModelAffinePoint_inj h).mpr ⟨(map_zero φ).symm, (map_zero φ).symm⟩
  rw [h', point_def, eqToHom_refl, Category.id_comp, projModelAffinePoint_projModelBaseChange]

-- The classifying homomorphism `ULift ℤ[A, B][Δ⁻¹] →+* R` of an elliptic Tate normal form.
private noncomputable def liftULift {a b : R} (h : IsUnit (tateNormalForm a b).Δ) :
    ULift.{u} UniversalTate.Ring →+* R :=
  (lift h).comp ULift.ringEquiv.toRingHom

private theorem map_liftULift {a b : R} (h : IsUnit (tateNormalForm a b).Δ) :
    curveULift.map (liftULift h) = tateNormalForm a b := by
  simp [liftULift, ULift.ringEquiv]

-- A ring homomorphism out of `ULift ℤ[A, B][Δ⁻¹]` is the classifying homomorphism of the Tate
-- normal form with the images of `A` and `B` as coefficients.
private theorem eq_liftULift (φ : ULift.{u} UniversalTate.Ring →+* R) :
    ∃ h : IsUnit (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).Δ, φ = liftULift h := by
  have hφ : curveULift.map φ = tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃) := by simp
  have h : IsUnit (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).Δ := by
    rw [← hφ, map_Δ]
    exact curveULift.isUnit_Δ.map φ
  refine ⟨h, ?_⟩
  have := eq_lift h (f := φ.comp (ULift.ringEquiv.symm : _ ≃+* ULift.{u} _).toRingHom) <| by
    rw [← map_map, ← curveULift_eq, hφ]
  ext x
  simpa [liftULift, ULift.ringEquiv] using congr($this x.down)

private theorem liftULift_congr {a b a' b' : R} (h : IsUnit (tateNormalForm a b).Δ)
    (h' : IsUnit (tateNormalForm a' b').Δ) (ha : a = a') (hb : b = b') :
    liftULift h = liftULift h' := by
  subst ha hb
  rfl

variable {W : WeierstrassCurve R} {P : Spec (.of R) ⟶ W.projModel}

-- A Tate normal form pointed-isomorphic to the projective model of an elliptic curve is elliptic.
private theorem isUnit_Δ_of_iso [W.IsElliptic] {a b : R}
    (e : (tateNormalForm a b).projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = (tateNormalForm a b).projModelOver)
    (he₀ : (tateNormalForm a b).projModelZero ≫ e.hom = W.projModelZero) :
    IsUnit (tateNormalForm a b).Δ := by
  obtain ⟨C, ⟨hC, -⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  rw [← hC]
  exact (C • W).isUnit_Δ

variable (hP : P ≫ W.projModelOver = 𝟙 _)

include hP

-- A classifying pair of `(W, P)` over `Spec φ` is the base change morphism along `φ`, composed
-- with a pointed isomorphism from `projModel W` to the Tate normal form with the images of `A` and
-- `B` as coefficients, carrying `P` to `(0, 0)`.
private theorem exists_iso_of_isTate
    {φ : ULift.{u} UniversalTate.Ring →+* R} {g : W.projModel ⟶ curveULift.projModel}
    (hg : IsTate W.projModelOver W.projModelZero P (Spec.map (CommRingCat.ofHom φ)) g) :
    ∃ e : (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).projModel ≅ W.projModel,
      e.hom ≫ W.projModelOver = (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).projModelOver ∧
        (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).projModelZero ≫ e.hom =
          W.projModelZero ∧
        (tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).projModelAffinePoint
          (equation_tateNormalForm_zero _ _) ≫ e.hom = P ∧
        g = e.inv ≫ eqToHom (congrArg projModel (by simp)) ≫ curveULift.projModelBaseChange φ := by
  -- `g` and the base change morphism are two pullbacks of the same cospan
  have hT := isTate_eqToHom_projModelBaseChange φ
    (W' := tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)) (by simp)
    (equation_tateNormalForm_zero _ _)
  let e := hg.1.isoIsPullback _ _ hT.1
  have he : e.hom ≫ _ = g := hg.1.isoIsPullback_hom_fst _ _ hT.1
  have he' : e.hom ≫ _ = W.projModelOver := hg.1.isoIsPullback_hom_snd _ _ hT.1
  refine ⟨e.symm, by simp [← he'], ?_, ?_, by simp [← he]⟩
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    refine hT.1.hom_ext ?_ ?_
    · rw [Category.assoc, he, hg.2.1, hT.2.1]
    · simp [he']
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    refine hT.1.hom_ext ?_ ?_
    · rw [Category.assoc, he, hg.2.2, hT.2.2]
    · simp [he', hP]

variable [W.IsElliptic]

-- Over an affine base, a classifying pair is determined by its base.
private theorem IsTate.total_eq {f : Spec (.of R) ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g g' : W.projModel ⟶ curveULift.projModel}
    (hg : IsTate W.projModelOver W.projModelZero P f g)
    (hg' : IsTate W.projModelOver W.projModelZero P f g') : g = g' := by
  obtain ⟨⟨φ⟩, rfl⟩ := Spec.map_surjective f
  obtain ⟨e, he, he₀, heP, rfl⟩ := exists_iso_of_isTate hP hg
  obtain ⟨e', he', he₀', heP', rfl⟩ := exists_iso_of_isTate hP hg'
  rw [tateNormalForm_iso_ext he he₀ he' he₀' (heP.trans heP'.symm)]

variable (h₁ : ∀ s, P s ≠ W.projModelZero s)
  (h₂ : ∀ s, (P ≫ W.projModelMulBy 2) s ≠ W.projModelZero s)
  (h₃ : ∀ s, (P ≫ W.projModelMulBy 3) s ≠ W.projModelZero s)

include h₁ h₂ h₃

-- Over an affine base, a section `P` satisfying the conditions of the Tate normal form has a
-- classifying pair.
private theorem exists_isTate :
    ∃ f g, IsTate W.projModelOver W.projModelZero P f g := by
  obtain ⟨⟨a, b⟩, ⟨e, he, he₀, heP⟩, -⟩ := W.existsUnique_tateNormalForm hP h₁ h₂ h₃
  have hΔ := isUnit_Δ_of_iso e he he₀
  have hT := isTate_eqToHom_projModelBaseChange (liftULift hΔ) (map_liftULift hΔ)
    (equation_tateNormalForm_zero a b)
  have he₀' : W.projModelZero ≫ e.inv = (tateNormalForm a b).projModelZero :=
    (Iso.comp_inv_eq e).mpr he₀.symm
  have heP' : P ≫ e.inv = (tateNormalForm a b).projModelAffinePoint
      (equation_tateNormalForm_zero a b) := (Iso.comp_inv_eq e).mpr heP.symm
  have hsq : IsPullback e.inv W.projModelOver (tateNormalForm a b).projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [← he]⟩
  exact ⟨_, _, by simpa using hsq.paste_horiz hT.1, by rw [reassoc_of% he₀', hT.2.1],
    by rw [reassoc_of% heP', hT.2.2]⟩

-- Over an affine base, the base of a classifying pair is unique.
private theorem IsTate.base_eq {f f' : Spec (.of R) ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g g' : W.projModel ⟶ curveULift.projModel}
    (hg : IsTate W.projModelOver W.projModelZero P f g)
    (hg' : IsTate W.projModelOver W.projModelZero P f' g') : f = f' := by
  obtain ⟨⟨φ⟩, rfl⟩ := Spec.map_surjective f
  obtain ⟨⟨φ'⟩, rfl⟩ := Spec.map_surjective f'
  obtain ⟨e, he, he₀, heP, -⟩ := exists_iso_of_isTate hP hg
  obtain ⟨e', he', he₀', heP', -⟩ := exists_iso_of_isTate hP hg'
  -- both Tate normal forms are the unique one for `P`, so `φ` and `φ'` agree on `A` and `B`
  have hab := (W.existsUnique_tateNormalForm hP h₁ h₂ h₃).unique
    (y₁ := (φ curveULift.a₁, φ curveULift.a₃)) (y₂ := (φ' curveULift.a₁, φ' curveULift.a₃))
    ⟨e, he, he₀, heP⟩ ⟨e', he', he₀', heP'⟩
  obtain ⟨hΔ, hφ⟩ := eq_liftULift φ
  obtain ⟨hΔ', hφ'⟩ := eq_liftULift φ'
  rw [hφ, hφ', liftULift_congr hΔ hΔ' (congrArg Prod.fst hab) (congrArg Prod.snd hab)]

end Affine

/-! ### Restriction to the pointed Weierstrass charts -/

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : S ⟶ E.carrier}
  (hP : P ≫ E.structureMap = 𝟙 S)

section Chart

variable (c : PointedWeierstrassChart E.structureMap E.zero)

-- The restriction of `E` to the base of `c`, read through `modelIso`, is a pointed cartesian
-- square from the projective model of the equation of `c` to `E`.
private theorem isPullback_chart : IsPullback (c.modelIso.inv ≫ c.toTotal)
    c.equation.projModelOver E.structureMap (c.baseIso.inv ≫ c.baseMap) :=
  c.isPullback.of_iso c.modelIso (.refl _) c.baseIso (.refl _) (by simp) c.modelIso_over.symm
    (by simp) (by simp)

private theorem modelPoint_mulBy_ne {n : ℤ} (hn : ∀ s, (P ≫ (E.mulBy n).left) s ≠ E.zero s)
    (s : Spec c.ring) :
    (c.modelPoint hP ≫ c.equation.projModelMulBy n) s ≠ c.equation.projModelZero s := fun hs ↦
  hn ((c.baseIso.inv ≫ c.baseMap) s) (by
    simpa only [← Scheme.Hom.comp_apply, Category.assoc,
      (c.equation.projModelMulBy_comp_of_isPullback (isPullback_chart c)
        c.projModelZero_modelIso_inv_toTotal),
      c.modelPoint_modelIso_inv_toTotal_assoc hP, c.projModelZero_modelIso_inv_toTotal] using
      congrArg (c.modelIso.inv ≫ c.toTotal) hs)

-- A classifying pair of `(E, P)` restricts to a classifying pair of the model of every chart.
private theorem isTate_chart {f : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g : E.carrier ⟶ curveULift.projModel} (hg : IsTate E.structureMap E.zero P f g) :
    IsTate c.equation.projModelOver c.equation.projModelZero (c.modelPoint hP)
      ((c.baseIso.inv ≫ c.baseMap) ≫ f) ((c.modelIso.inv ≫ c.toTotal) ≫ g) :=
  hg.comp (isPullback_chart c) c.projModelZero_modelIso_inv_toTotal
    (c.modelPoint_modelIso_inv_toTotal hP)

end Chart

/-! ### The universal Tate normal form as an elliptic curve -/

-- Reading the universal Tate normal form on its projective model through `toEllipticCurveGeomIso`
-- identifies classifying pairs into `curveGeom` with the classifying pairs of
-- `existsUnique_tateNormalForm`.
private theorem isTate_curveGeom_iff {f : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g : E.carrier ⟶ curveGeom.{u}.carrier} :
    (IsPullback g E.structureMap curveGeom.structureMap f ∧ E.zero ≫ g = f ≫ curveGeom.zero ∧
      P ≫ g = f ≫ pointHom.left) ↔
    (IsPullback (g ≫ (toEllipticCurveGeomIso curveULift).hom) E.structureMap
        curveULift.projModelOver f ∧
      E.zero ≫ g ≫ (toEllipticCurveGeomIso curveULift).hom = f ≫ curveULift.projModelZero ∧
      P ≫ g ≫ (toEllipticCurveGeomIso curveULift).hom = f ≫ point) := by
  have hiso : IsPullback (toEllipticCurveGeomIso curveULift.{u}).hom curveGeom.structureMap
      curveULift.projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩
  refine and_congr ⟨fun hg ↦ by simpa using hg.paste_horiz hiso, fun hg ↦ ?_⟩ ?_
  · exact IsPullback.of_right (by simpa using hg) (by simpa using hg.w) hiso
  · refine and_congr ?_ ?_
    · rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom]
      simp
    · rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom]
      simp

/-! ### The classifying pair -/

section Classifying

variable (h₁ : ∀ s, P s ≠ E.zero s) (h₂ : ∀ s, (P ≫ (E.mulBy 2).left) s ≠ E.zero s)
  (h₃ : ∀ s, (P ≫ (E.mulBy 3).left) s ≠ E.zero s)

include hP h₁ h₂ h₃

-- A classifying pair of `(E, P)` is unique: by the affine case, on the charts of an atlas.
private theorem IsTate.unique {f f' : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g g' : E.carrier ⟶ curveULift.projModel} (hg : IsTate E.structureMap E.zero P f g)
    (hg' : IsTate E.structureMap E.zero P f' g') : f = f' ∧ g = g' := by
  obtain ⟨A⟩ := E.localModel
  obtain rfl : f = f' := A.openCover.hom_ext _ _ fun i ↦ by
    dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
    have := IsTate.base_eq ((A.chart i).modelPoint_projModelOver hP)
      ((A.chart i).modelPoint_apply_ne hP h₁) (modelPoint_mulBy_ne hP _ h₂)
      (modelPoint_mulBy_ne hP _ h₃) (isTate_chart hP (A.chart i) hg)
      (isTate_chart hP (A.chart i) hg')
    rw [← cancel_epi (A.chart i).baseIso.inv]
    simpa using this
  refine ⟨rfl, A.hom_ext_of_toTotal g g' fun i ↦ ?_⟩
  have := IsTate.total_eq ((A.chart i).modelPoint_projModelOver hP)
    (isTate_chart hP (A.chart i) hg)
    (isTate_chart hP (A.chart i) hg')
  rw [← cancel_epi (A.chart i).modelIso.inv]
  simpa using this

section Glue

variable (c : PointedWeierstrassChart E.structureMap E.zero)

private theorem exists_isTate_chart :
    ∃ f g, IsTate c.equation.projModelOver c.equation.projModelZero (c.modelPoint hP) f g :=
  exists_isTate (c.modelPoint_projModelOver hP) (c.modelPoint_apply_ne hP h₁)
    (modelPoint_mulBy_ne hP c h₂) (modelPoint_mulBy_ne hP c h₃)

-- The base of a chosen classifying pair of the model of `c`.
private noncomputable def chartBase : Spec c.ring ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  (exists_isTate_chart hP h₁ h₂ h₃ c).choose

-- The total morphism of a chosen classifying pair of the model of `c`.
private noncomputable def chartTotal : c.equation.projModel ⟶ curveULift.projModel :=
  (exists_isTate_chart hP h₁ h₂ h₃ c).choose_spec.choose

private theorem isTate_chartBase :
    IsTate c.equation.projModelOver c.equation.projModelZero (c.modelPoint hP)
      (chartBase hP h₁ h₂ h₃ c) (chartTotal hP h₁ h₂ h₃ c) :=
  (exists_isTate_chart hP h₁ h₂ h₃ c).choose_spec.choose_spec

-- The classifying morphism of the chosen classifying pair of `c`, on the part of `S` over its base.
private noncomputable def pieceBase :
    pullback (𝟙 S) c.baseMap ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ chartBase hP h₁ h₂ h₃ c

-- The total morphism of the chosen classifying pair of `c`, on the part of `E` over its base.
private noncomputable def pieceTotal : pullback E.structureMap c.baseMap ⟶ curveULift.projModel :=
  c.isPullback.isoPullback.inv ≫ c.modelIso.hom ≫ chartTotal hP h₁ h₂ h₃ c

section Compat

variable {c} {k : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap)

include hh

-- The chosen classifying pair of `c` restricts along a morphism of chart bases to the chosen
-- classifying pair of `k`, by uniqueness over an affine base.
private theorem isTate_projModelMap :
    IsTate k.equation.projModelOver k.equation.projModelZero (k.modelPoint hP)
      ((k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ chartBase hP h₁ h₂ h₃ c)
      (PointedWeierstrassChart.projModelMap hh ≫ chartTotal hP h₁ h₂ h₃ c) :=
  (isTate_chartBase hP h₁ h₂ h₃ c).comp (PointedWeierstrassChart.isPullback_projModelMap hh)
    (PointedWeierstrassChart.projModelZero_projModelMap hh)
    (PointedWeierstrassChart.modelPoint_projModelMap hP hh)

private theorem chartBase_comp :
    (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ chartBase hP h₁ h₂ h₃ c = chartBase hP h₁ h₂ h₃ k :=
  IsTate.base_eq (k.modelPoint_projModelOver hP) (k.modelPoint_apply_ne hP h₁)
    (modelPoint_mulBy_ne hP k h₂) (modelPoint_mulBy_ne hP k h₃)
    (isTate_projModelMap hP h₁ h₂ h₃ hh) (isTate_chartBase hP h₁ h₂ h₃ k)

private theorem chartTotal_comp :
    PointedWeierstrassChart.projModelMap hh ≫ chartTotal hP h₁ h₂ h₃ c =
      chartTotal hP h₁ h₂ h₃ k :=
  IsTate.total_eq (k.modelPoint_projModelOver hP)
    (chartBase_comp hP h₁ h₂ h₃ hh ▸ isTate_projModelMap hP h₁ h₂ h₃ hh)
    (isTate_chartBase hP h₁ h₂ h₃ k)

private theorem map_pieceBase :
    pullback.map (𝟙 S) k.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceBase hP h₁ h₂ h₃ c = pieceBase hP h₁ h₂ h₃ k := by
  simp [pieceBase, ← chartBase_comp hP h₁ h₂ h₃ hh]

private theorem map_pieceTotal :
    pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _) (by simp)
      (by simp [hh]) ≫ pieceTotal hP h₁ h₂ h₃ c = pieceTotal hP h₁ h₂ h₃ k := by
  have key : pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _)
      (by simp) (by simp [hh]) ≫ c.isPullback.isoPullback.inv =
      k.isPullback.isoPullback.inv ≫ PointedWeierstrassChart.pullbackCarrierMap hh :=
    c.isPullback.hom_ext (by simp) (by simp)
  rw [pieceTotal, pieceTotal, reassoc_of% key, ← chartTotal_comp hP h₁ h₂ h₃ hh]
  simp

end Compat

-- The classifying morphism of `(E, P)`, glued from the chosen classifying pairs of the charts.
private noncomputable def tateBase : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  glueMorphisms (pieceBase hP h₁ h₂ h₃) (map_pieceBase hP h₁ h₂ h₃)

-- The morphism to the universal Tate normal form, glued from the chosen classifying pairs of the
-- charts.
private noncomputable def tateTotal : E.carrier ⟶ curveULift.projModel :=
  glueMorphisms (pieceTotal hP h₁ h₂ h₃) (map_pieceTotal hP h₁ h₂ h₃)

@[reassoc]
private theorem baseMap_tateBase :
    c.baseMap ≫ tateBase hP h₁ h₂ h₃ = c.baseIso.hom ≫ chartBase hP h₁ h₂ h₃ c := by
  simpa [tateBase, pieceBase, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
      fst_glueMorphisms (pieceBase hP h₁ h₂ h₃) (map_pieceBase hP h₁ h₂ h₃) c

private theorem toTotal_tateTotal :
    c.toTotal ≫ tateTotal hP h₁ h₂ h₃ = c.modelIso.hom ≫ chartTotal hP h₁ h₂ h₃ c := by
  simpa [tateTotal, pieceTotal, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    c.isPullback.isoPullback.hom ≫=
      fst_glueMorphisms (pieceTotal hP h₁ h₂ h₃) (map_pieceTotal hP h₁ h₂ h₃) c

-- The glued pair classifies `(E, P)`: this is checked over the charts of an atlas.
private theorem isTate_tate :
    IsTate E.structureMap E.zero P (tateBase hP h₁ h₂ h₃) (tateTotal hP h₁ h₂ h₃) := by
  obtain ⟨A⟩ := E.localModel
  refine ⟨?_, A.openCover.hom_ext _ _ fun i ↦ ?_, A.openCover.hom_ext _ _ fun i ↦ ?_⟩
  · -- cartesian, checked over the cover of `S` by the chart bases of `A`
    refine (Scheme.isPullback_of_openCover _ _ _ _ A.openCover fun i ↦ ?_).flip
    -- the maps of `A.openCover` are the chart base maps, and those of its pullback along
    -- `E.structureMap` are the projections; `simp` does not see through the pullback cover here
    change IsPullback (pullback.snd E.structureMap (A.chart i).baseMap)
      (pullback.fst E.structureMap (A.chart i).baseMap ≫ tateTotal hP h₁ h₂ h₃)
      ((A.chart i).baseMap ≫ tateBase hP h₁ h₂ h₃) curveULift.projModelOver
    -- over the base of a chart, this is the cartesian square of the chosen classifying pair
    rw [baseMap_tateBase, ← (A.chart i).isPullback.isoPullback_inv_fst, Category.assoc,
      toTotal_tateTotal]
    exact (isTate_chartBase hP h₁ h₂ h₃ (A.chart i)).1.flip.of_iso
      ((A.chart i).modelIso.symm ≪≫ (A.chart i).isPullback.isoPullback) (A.chart i).baseIso.symm
      (.refl _) (.refl _)
      (by simp [Iso.eq_inv_comp]) (by simp) (by simp)
      (by simp)
  · dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
    rw [← (A.chart i).pulledZero_toTotal_assoc, toTotal_tateTotal,
      (A.chart i).modelIso_zero_assoc, (isTate_chartBase hP h₁ h₂ h₃ _).2.1,
      baseMap_tateBase_assoc]
  · dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
    rw [← PointedWeierstrassChart.chartPoint_toTotal_assoc _ hP, toTotal_tateTotal,
      reassoc_of% PointedWeierstrassChart.chartPoint_modelIso_hom _ hP,
      (isTate_chartBase hP h₁ h₂ h₃ _).2.2, baseMap_tateBase_assoc]

end Glue

/-! ### The universal property -/

section Explicit

variable (E)

/-- **The universal Tate normal form.** Let `E` be an elliptic curve over a scheme `S` and `P` a
section of `E` such that none of `P`, `2P` and `3P` meets the zero section over any point of `S`.
Then there is a unique pair of a morphism `f : S ⟶ Spec ℤ[A, B][Δ⁻¹]` and a morphism `g` from `E`
to the projective model of the universal Tate normal form `Y² + AXY + BY = X³ + BX²` such that `g`
exhibits `E` as the base change of the universal Tate normal form along `f`, carrying the zero
section of `E` to the zero section and `P` to the point `(0, 0)`. Conversely, such a pair exists
only if `P`, `2P` and `3P` miss the zero section everywhere (`exists_tateNormalForm_iff`). -/
theorem existsUnique_tateNormalForm :
    ∃! fg : (S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) × (E.carrier ⟶ curveULift.projModel),
      IsPullback fg.2 E.structureMap curveULift.projModelOver fg.1 ∧
        E.zero ≫ fg.2 = fg.1 ≫ curveULift.projModelZero ∧ P ≫ fg.2 = fg.1 ≫ point :=
  ⟨(tateBase hP h₁ h₂ h₃, tateTotal hP h₁ h₂ h₃), isTate_tate hP h₁ h₂ h₃, fun _ hfg ↦
    have h := IsTate.unique hP h₁ h₂ h₃ hfg (isTate_tate hP h₁ h₂ h₃)
    Prod.ext h.1 h.2⟩

/-- **The universal Tate normal form as an elliptic curve.** The universal property
`existsUnique_tateNormalForm`, with the universal Tate normal form read as the elliptic curve
`curveGeom` and its point `(0, 0)` as `pointHom`: there is a unique pair of a morphism
`f : S ⟶ Spec ℤ[A, B][Δ⁻¹]` and a morphism `g` from `E` to `curveGeom` exhibiting `E` as the
pullback of `curveGeom` along `f`, carrying the zero section to the zero section and `P` to
`(0, 0)`. -/
theorem existsUnique_tateNormalForm_curveGeom :
    ∃! fg : (S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) × (E.carrier ⟶ curveGeom.{u}.carrier),
      IsPullback fg.2 E.structureMap curveGeom.structureMap fg.1 ∧
        E.zero ≫ fg.2 = fg.1 ≫ curveGeom.zero ∧ P ≫ fg.2 = fg.1 ≫ pointHom.left := by
  obtain ⟨⟨f, g⟩, hfg, huniq⟩ := E.existsUnique_tateNormalForm hP h₁ h₂ h₃
  refine ⟨(f, g ≫ (toEllipticCurveGeomIso curveULift).inv),
    isTate_curveGeom_iff.mpr (by simpa using hfg), fun ⟨f', g'⟩ hfg' ↦ ?_⟩
  have := huniq (f', g' ≫ (toEllipticCurveGeomIso curveULift).hom) (isTate_curveGeom_iff.mp hfg')
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (by simp [← this.2])

end Explicit

/-- **Automorphisms fixing a point of order at least four are trivial.** Let `P` be a section of
`E` such that none of `P`, `2P` and `3P` meets the zero section over any point of `S`. An
automorphism `τ` of `E` over `S`, given as a cartesian square over the identity of `S`, which fixes
the zero section and `P` is the identity. The cartesian hypothesis cannot be dropped: if `P` is
killed by `N`, multiplication by `N + 1` fixes the zero section and `P`. -/
theorem eq_id_of_isPullback_of_comp_eq {τ : E.carrier ⟶ E.carrier}
    (hτ : IsPullback τ E.structureMap E.structureMap (𝟙 S)) (h0 : E.zero ≫ τ = E.zero)
    (hPτ : P ≫ τ = P) : τ = 𝟙 _ := by
  -- composing the classifying morphism of `(E, P)` with `τ` gives a second classifying morphism
  obtain ⟨⟨f, g⟩, ⟨hg, hg0, hgP⟩, huniq⟩ := E.existsUnique_tateNormalForm hP h₁ h₂ h₃
  have hτg : τ ≫ g = g := congrArg Prod.snd <| huniq (f, τ ≫ g)
    ⟨by simpa using hτ.paste_horiz hg, by simp [reassoc_of% h0, hg0],
      by simp [reassoc_of% hPτ, hgP]⟩
  exact hg.hom_ext (by simpa using hτg) (by simpa using hτ.w)

end Classifying

/-! ### The Tate locus -/

section TateLocus

open MonoidalCategory

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The Tate locus** of an elliptic curve `E` over `S`: the set of points `e` of `E` such that
none of `e`, `2e` and `3e` lies on the zero section. Its points with values in a scheme over `S`
are the points of `E` to which the Tate normal form applies (`isTatePoint_iff_of_isPullback`). -/
def tateLocus : Set E.carrier :=
  {e | e ≠ E.zero (E.structureMap e) ∧ (E.mulBy 2).left e ≠ E.zero (E.structureMap e) ∧
    (E.mulBy 3).left e ≠ E.zero (E.structureMap e)}

variable {E} in
/-- The defining condition of the Tate locus. -/
@[simp]
theorem mem_tateLocus_iff {e : E.carrier} :
    e ∈ E.tateLocus ↔ e ≠ E.zero (E.structureMap e) ∧
      (E.mulBy 2).left e ≠ E.zero (E.structureMap e) ∧
        (E.mulBy 3).left e ≠ E.zero (E.structureMap e) :=
  Iff.rfl

/-- The Tate locus is open: it is the complement of the preimages under `[1]`, `[2]` and `[3]` of
the closed image of the zero section. -/
theorem isOpen_tateLocus : IsOpen E.tateLocus := by
  have h (x : Over.mk E.structureMap ⟶ Over.mk E.structureMap) :
      IsOpen {e | x.left e ≠ E.zero (E.structureMap e)} := by
    have hx : {e | x.left e ≠ E.zero (E.structureMap e)} = (x.left ⁻¹' Set.range E.zero)ᶜ := by
      ext e
      exact (left_apply_mem_range_zero_iff x e).not.symm
    rw [hx]
    exact (E.zero.isClosedEmbedding.isClosed_range.preimage x.left.continuous).isOpen_compl
  exact (h (𝟙 _)).inter ((h (E.mulBy 2)).inter (h (E.mulBy 3)))

/-- The Tate locus as an open subscheme of `E`. -/
def tateLocusOpens : E.carrier.Opens :=
  ⟨E.tateLocus, E.isOpen_tateLocus⟩

@[simp]
theorem coe_tateLocusOpens : (E.tateLocusOpens : Set E.carrier) = E.tateLocus :=
  (rfl)

/-- An `S`-point `P` of `E` is a **Tate point** if it lies in the Tate locus at every point of
`S`, that is, none of `P`, `2P` and `3P` meets the zero section (`isTatePoint_iff`). These are the
points to which the Tate normal form applies (`existsUnique_tateNormalForm`). -/
def IsTatePoint (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) : Prop :=
  ∀ s : S, P.left s ∈ E.tateLocus

variable {E}

/-- A Tate point lies in the Tate locus at every point of the base. -/
theorem IsTatePoint.mem_tateLocus {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (h : E.IsTatePoint P) (s : S) : P.left s ∈ E.tateLocus :=
  h s

/-- A Tate point is a point `P` such that none of `P`, `2P` and `3P` meets the zero section. -/
theorem isTatePoint_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} :
    E.IsTatePoint P ↔ (∀ s : S, P.left s ≠ E.zero s) ∧
      (∀ s : S, (P.left ≫ (E.mulBy 2).left) s ≠ E.zero s) ∧
        ∀ s : S, (P.left ≫ (E.mulBy 3).left) s ≠ E.zero s := by
  have hP (s : S) : E.structureMap (P.left s) = s := by
    rw [← Scheme.Hom.comp_apply, left_comp_structureMap]
    rfl
  refine ⟨fun h ↦ ⟨fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩, fun ⟨h₁, h₂, h₃⟩ s ↦ ?_⟩
  · simpa only [hP] using (h s).1
  · simpa only [hP, Scheme.Hom.comp_apply] using (h s).2.1
  · simpa only [hP, Scheme.Hom.comp_apply] using (h s).2.2
  · rw [mem_tateLocus_iff, hP]
    simp only [Scheme.Hom.comp_apply] at h₂ h₃
    exact ⟨h₁ s, h₂ s, h₃ s⟩

/-- **The conditions of the Tate normal form are necessary.** An `S`-point `P` of an elliptic curve
`E` over `S` is the pullback of the point `(0, 0)` of the universal Tate normal form along a
cartesian morphism from `E` carrying the zero section to the zero section exactly when it is a
Tate point. -/
theorem exists_tateNormalForm_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} :
    (∃ (f : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) (g : E.carrier ⟶ curveULift.projModel),
      IsPullback g E.structureMap curveULift.projModelOver f ∧
        E.zero ≫ g = f ≫ curveULift.projModelZero ∧ P.left ≫ g = f ≫ point) ↔
      E.IsTatePoint P := by
  rw [isTatePoint_iff]
  refine ⟨fun ⟨f, g, hg, h₀, hgP⟩ ↦ ?_, fun ⟨h₁, h₂, h₃⟩ ↦
    let ⟨⟨f, g⟩, h, _⟩ := E.existsUnique_tateNormalForm (left_comp_structureMap P) h₁ h₂ h₃
    ⟨f, g, h⟩⟩
  -- `g` carries `P`, `2P` and `3P` to the corresponding multiples of `(0, 0)`, which satisfy the
  -- conditions, and multiplication by `n` commutes with `g`
  have hn (n : ℤ) (s : S) (hs : (P.left ≫ (E.mulBy n).left) s = E.zero s) :
      (point ≫ curveULift.projModelMulBy n) (f s) = curveULift.projModelZero (f s) := by
    simpa only [← Scheme.Hom.comp_apply, Category.assoc,
      ← curveULift.comp_projModelMulBy_of_isPullback hg h₀, reassoc_of% hgP, h₀] using
      congrArg g hs
  exact ⟨fun s hs ↦ point_ne_projModelZero (f s) (by
      simpa only [← Scheme.Hom.comp_apply, hgP, h₀] using congrArg g hs),
    fun s hs ↦ point_projModelMulBy_two_ne_projModelZero (f s) (hn 2 s hs),
    fun s hs ↦ point_projModelMulBy_three_ne_projModelZero (f s) (hn 3 s hs)⟩

section BaseChange

variable {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- **Tate points of a base change.** Let `g : E' ⟶ E` lie over `f : S' ⟶ S`, exhibiting `E'` as
the base change of `E` and carrying the zero section to the zero section. An `S'`-point `P'` of
`E'` is a Tate point exactly when its image under `g`, a point of `E` with values in `S'`, lies in
the Tate locus of `E` at every point of `S'`. -/
theorem isTatePoint_iff_of_isPullback (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    E'.IsTatePoint P' ↔ ∀ s' : S', g (P'.left s') ∈ E.tateLocus := by
  have hP (s' : S') : E.structureMap (g (P'.left s')) = f s' := by
    rw [← Scheme.Hom.comp_apply, hg.w, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply P'.left,
      left_comp_structureMap]
    rfl
  -- `g` carries `nP'` to `n` times the image of `P'`
  have hn (n : ℤ) (s' : S') :
      ((P'.left ≫ (E'.mulBy n).left) s' = E'.zero s') ↔
        (E.mulBy n).left (g (P'.left s')) = E.zero (f s') := by
    rw [← Over.comp_left, left_apply_eq_zero_iff_of_isPullback hg h0, Over.comp_left,
      ← Scheme.Hom.comp_apply, Category.assoc, mulBy_left_comp_of_isPullback hg h0,
      ← Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [isTatePoint_iff]
  simp only [mem_tateLocus_iff, hP]
  refine ⟨fun ⟨h₁, h₂, h₃⟩ s' ↦ ⟨?_, (hn 2 s').not.mp (h₂ s'), (hn 3 s').not.mp (h₃ s')⟩,
    fun h ↦ ⟨fun s' ↦ ?_, fun s' ↦ (hn 2 s').not.mpr (h s').2.1,
      fun s' ↦ (hn 3 s').not.mpr (h s').2.2⟩⟩
  · exact (left_apply_eq_zero_iff_of_isPullback hg h0 P' s').not.mp (h₁ s')
  · exact (left_apply_eq_zero_iff_of_isPullback hg h0 P' s').not.mpr (h s').1

include hg h0 in
/-- **Tate points are stable under base change.** -/
theorem IsTatePoint.pointsPullback {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (h : E.IsTatePoint P) : E'.IsTatePoint (pointsPullback hg h0 P) := by
  rw [isTatePoint_iff_of_isPullback hg h0]
  intro s'
  rw [← Scheme.Hom.comp_apply, pointsPullback_left_comp, Scheme.Hom.comp_apply]
  exact h (f s')

end BaseChange

end TateLocus

end EllipticCurveGeom

namespace UniversalTate

open MonoidalCategory

/-- The point `(0, 0)` of the universal Tate normal form is a Tate point: none of `(0, 0)`,
`2 (0, 0)` and `3 (0, 0)` meets the zero section. -/
theorem isTatePoint_pointHom : curveGeom.{u}.IsTatePoint pointHom := by
  have hiso : IsPullback (toEllipticCurveGeomIso curveULift.{u}).hom curveGeom.structureMap
      curveULift.projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩
  exact curveGeom.exists_tateNormalForm_iff.mp
    ⟨𝟙 _, (toEllipticCurveGeomIso curveULift).hom, hiso, by simp, by simp⟩

end UniversalTate

end TauCeti.AlgebraicGeometry
