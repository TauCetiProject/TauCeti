/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.TateNormalForm
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
Conversely, a section which is such a pullback of `(0, 0)` satisfies the three conditions
(`EllipticCurveGeom.exists_tateNormalForm_iff`). So `Spec ℤ[A, B][Δ⁻¹]` is a fine moduli scheme
for elliptic curves with a section `P` such that `P`, `2P` and `3P` are nowhere the zero section,
with universal family the projective model of the universal Tate normal form. No hypothesis on `S`
is needed; in particular `S` may be nonreduced or non-affine.

The coefficient ring `ℤ[A, B][Δ⁻¹]` (`WeierstrassCurve.UniversalTate.Ring`) lies in `Type`. For
schemes in an arbitrary universe the universal Tate normal form is read over its copy
`ULift.{u} ℤ[A, B][Δ⁻¹]` (`WeierstrassCurve.UniversalTate.curveULift`).

## Main definitions

* `WeierstrassCurve.UniversalTate.point`: the point `(0, 0)` of the projective model of the
  universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]`.
* `TauCeti.AlgebraicGeometry.UniversalTate.curveGeom`: the universal Tate normal form as an
  elliptic curve over `Spec ℤ[A, B][Δ⁻¹]`.
* `TauCeti.AlgebraicGeometry.UniversalTate.pointHom`: its point `(0, 0)`, with values in the base.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_tateNormalForm`: a section `P` such
  that `P`, `2P` and `3P` miss the zero section everywhere is the pullback of `(0, 0)` along a
  unique cartesian pointed morphism to the universal Tate normal form.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_tateNormalForm_iff`: such a morphism exists
  exactly when `P`, `2P` and `3P` miss the zero section everywhere.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_tateNormalForm_curveGeom`: the same
  universal property, with the universal Tate normal form read as the elliptic curve `curveGeom`.
* `WeierstrassCurve.UniversalTate.point_ne_projModelZero`,
  `WeierstrassCurve.UniversalTate.point_projModelMulBy_two_ne_projModelZero` and
  `WeierstrassCurve.UniversalTate.point_projModelMulBy_three_ne_projModelZero`: the universal point
  satisfies the three conditions.

## References

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

-- A classifying pair of `(W, P)` over `Spec φ` is the base change morphism along `φ`, composed
-- with a pointed isomorphism from `projModel W` to the Tate normal form with the images of `A` and
-- `B` as coefficients, carrying `P` to `(0, 0)`.
private theorem exists_iso_of_isTate (hP : P ≫ W.projModelOver = 𝟙 _)
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

variable [W.IsElliptic] (hP : P ≫ W.projModelOver = 𝟙 _)
  (h₁ : ∀ s, P s ≠ W.projModelZero s) (h₂ : ∀ s, (P ≫ W.projModelMulBy 2) s ≠ W.projModelZero s)
  (h₃ : ∀ s, (P ≫ W.projModelMulBy 3) s ≠ W.projModelZero s)

include hP h₁ h₂ h₃ in
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

include hP h₁ h₂ h₃ in
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

include hP in
-- Over an affine base, a classifying pair is determined by its base.
private theorem IsTate.total_eq {f : Spec (.of R) ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g g' : W.projModel ⟶ curveULift.projModel}
    (hg : IsTate W.projModelOver W.projModelZero P f g)
    (hg' : IsTate W.projModelOver W.projModelZero P f g') : g = g' := by
  obtain ⟨⟨φ⟩, rfl⟩ := Spec.map_surjective f
  obtain ⟨e, he, he₀, heP, rfl⟩ := exists_iso_of_isTate hP hg
  obtain ⟨e', he', he₀', heP', rfl⟩ := exists_iso_of_isTate hP hg'
  rw [tateNormalForm_iso_ext he he₀ he' he₀' (heP.trans heP'.symm)]

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

-- Morphisms out of `S` are determined on the bases of the charts of an atlas.
private theorem hom_ext_baseMap (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {Z : Scheme.{u}} {x y : S ⟶ Z} (h : ∀ i, (A.chart i).baseMap ≫ x = (A.chart i).baseMap ≫ y) :
    x = y :=
  A.hom_ext (𝟙 S) x y fun i ↦ by
    have hc : pullback.fst (𝟙 S) (A.chart i).baseMap = pullback.snd _ _ ≫ (A.chart i).baseMap := by
      simpa using pullback.condition (f := 𝟙 S) (g := (A.chart i).baseMap)
    rw [hc, Category.assoc, Category.assoc, h]

variable (h₁ : ∀ s, P s ≠ E.zero s) (h₂ : ∀ s, (P ≫ (E.mulBy 2).left) s ≠ E.zero s)
  (h₃ : ∀ s, (P ≫ (E.mulBy 3).left) s ≠ E.zero s)

include hP h₁ h₂ h₃ in
-- A classifying pair of `(E, P)` is unique: by the affine case, on the charts of an atlas.
private theorem IsTate.unique {f f' : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))}
    {g g' : E.carrier ⟶ curveULift.projModel} (hg : IsTate E.structureMap E.zero P f g)
    (hg' : IsTate E.structureMap E.zero P f' g') : f = f' ∧ g = g' := by
  obtain ⟨A⟩ := E.localModel
  obtain rfl : f = f' := hom_ext_baseMap A fun i ↦ by
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

include h₁ h₂ h₃ in
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

variable {c} {k : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap)

-- The chosen classifying pair of `c` restricts along a morphism of chart bases to the chosen
-- classifying pair of `k`, by uniqueness over an affine base.
private theorem isTate_projModelMap :
    IsTate k.equation.projModelOver k.equation.projModelZero (k.modelPoint hP)
      ((k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ chartBase hP h₁ h₂ h₃ c)
      (PointedWeierstrassChart.projModelMap hh ≫ chartTotal hP h₁ h₂ h₃ c) :=
  (isTate_chartBase hP h₁ h₂ h₃ c).comp (PointedWeierstrassChart.isPullback_projModelMap hh)
    (PointedWeierstrassChart.projModelZero_projModelMap hh)
    (PointedWeierstrassChart.modelPoint_projModelMap hP hh)

include hh in
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

variable (c) in
-- The classifying morphism of the chosen classifying pair of `c`, on the part of `S` over its base.
private noncomputable def pieceBase :
    pullback (𝟙 S) c.baseMap ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ chartBase hP h₁ h₂ h₃ c

private theorem map_pieceBase :
    pullback.map (𝟙 S) k.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceBase hP h₁ h₂ h₃ c = pieceBase hP h₁ h₂ h₃ k := by
  simp [pieceBase, ← chartBase_comp hP h₁ h₂ h₃ hh]

variable (c) in
-- The total morphism of the chosen classifying pair of `c`, on the part of `E` over its base.
private noncomputable def pieceTotal : pullback E.structureMap c.baseMap ⟶ curveULift.projModel :=
  c.isPullback.isoPullback.inv ≫ c.modelIso.hom ≫ chartTotal hP h₁ h₂ h₃ c

private theorem map_pieceTotal :
    pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _) (by simp)
      (by simp [hh]) ≫ pieceTotal hP h₁ h₂ h₃ c = pieceTotal hP h₁ h₂ h₃ k := by
  have key : pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _)
      (by simp) (by simp [hh]) ≫ c.isPullback.isoPullback.inv =
      k.isPullback.isoPullback.inv ≫ PointedWeierstrassChart.pullbackCarrierMap hh :=
    c.isPullback.hom_ext (by simp) (by simp)
  rw [pieceTotal, pieceTotal, reassoc_of% key, ← chartTotal_comp hP h₁ h₂ h₃ hh]
  simp

-- The classifying morphism of `(E, P)`, glued from the chosen classifying pairs of the charts.
private noncomputable def tateBase : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring)) :=
  glueMorphisms (pieceBase hP h₁ h₂ h₃) (map_pieceBase hP h₁ h₂ h₃)

-- The morphism to the universal Tate normal form, glued from the chosen classifying pairs of the
-- charts.
private noncomputable def tateTotal : E.carrier ⟶ curveULift.projModel :=
  glueMorphisms (pieceTotal hP h₁ h₂ h₃) (map_pieceTotal hP h₁ h₂ h₃)

variable (c) in
@[reassoc]
private theorem baseMap_tateBase :
    c.baseMap ≫ tateBase hP h₁ h₂ h₃ = c.baseIso.hom ≫ chartBase hP h₁ h₂ h₃ c := by
  simpa [tateBase, pieceBase, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
      fst_glueMorphisms (pieceBase hP h₁ h₂ h₃) (map_pieceBase hP h₁ h₂ h₃) c

variable (c) in
private theorem toTotal_tateTotal :
    c.toTotal ≫ tateTotal hP h₁ h₂ h₃ = c.modelIso.hom ≫ chartTotal hP h₁ h₂ h₃ c := by
  simpa [tateTotal, pieceTotal, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    c.isPullback.isoPullback.hom ≫=
      fst_glueMorphisms (pieceTotal hP h₁ h₂ h₃) (map_pieceTotal hP h₁ h₂ h₃) c

-- The glued pair classifies `(E, P)`: this is checked over the charts of an atlas.
private theorem isTate_tate :
    IsTate E.structureMap E.zero P (tateBase hP h₁ h₂ h₃) (tateTotal hP h₁ h₂ h₃) := by
  obtain ⟨A⟩ := E.localModel
  refine ⟨?_, hom_ext_baseMap A fun i ↦ ?_, hom_ext_baseMap A fun i ↦ ?_⟩
  · -- cartesian, checked over the cover of `S` by the chart bases of `A`
    let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers A.index (fun i ↦ (A.chart i).base)
      (fun i ↦ (A.chart i).baseMap) A.covers
    refine (Scheme.isPullback_of_openCover _ _ _ _ 𝒰 fun i ↦ ?_).flip
    -- the maps of `𝒰` are the chart base maps, and those of its pullback along `E.structureMap`
    -- are the projections; `simp` does not see through `Scheme.Cover.mkOfCovers` here
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
  · rw [← (A.chart i).pulledZero_toTotal_assoc, toTotal_tateTotal,
      (A.chart i).modelIso_zero_assoc, (isTate_chartBase hP h₁ h₂ h₃ _).2.1,
      baseMap_tateBase_assoc]
  · rw [← PointedWeierstrassChart.chartPoint_toTotal_assoc _ hP, toTotal_tateTotal,
      reassoc_of% PointedWeierstrassChart.chartPoint_modelIso_hom _ hP,
      (isTate_chartBase hP h₁ h₂ h₃ _).2.2, baseMap_tateBase_assoc]

end Glue

/-! ### The universal property -/

include hP h₁ h₂ h₃ in
variable (E) in
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

include hP in
variable (E) in
/-- **The conditions of the Tate normal form are necessary.** A section `P` of an elliptic curve `E`
over `S` is the pullback of the point `(0, 0)` of the universal Tate normal form along a cartesian
morphism from `E` carrying the zero section to the zero section exactly when none of `P`, `2P` and
`3P` meets the zero section over any point of `S`. -/
theorem exists_tateNormalForm_iff :
    (∃ (f : S ⟶ Spec (.of (ULift.{u} UniversalTate.Ring))) (g : E.carrier ⟶ curveULift.projModel),
      IsPullback g E.structureMap curveULift.projModelOver f ∧
        E.zero ≫ g = f ≫ curveULift.projModelZero ∧ P ≫ g = f ≫ point) ↔
      (∀ s, P s ≠ E.zero s) ∧ (∀ s, (P ≫ (E.mulBy 2).left) s ≠ E.zero s) ∧
        ∀ s, (P ≫ (E.mulBy 3).left) s ≠ E.zero s := by
  refine ⟨fun ⟨f, g, hg, h₀, hgP⟩ ↦ ?_, fun ⟨h₁, h₂, h₃⟩ ↦
    let ⟨⟨f, g⟩, h, _⟩ := E.existsUnique_tateNormalForm hP h₁ h₂ h₃; ⟨f, g, h⟩⟩
  -- `g` carries `P`, `2P` and `3P` to the corresponding multiples of `(0, 0)`, which satisfy the
  -- conditions, and multiplication by `n` commutes with `g`
  have hn (n : ℤ) (s : S) (hs : (P ≫ (E.mulBy n).left) s = E.zero s) :
      (point ≫ curveULift.projModelMulBy n) (f s) = curveULift.projModelZero (f s) := by
    simpa only [← Scheme.Hom.comp_apply, Category.assoc,
      ← curveULift.comp_projModelMulBy_of_isPullback hg h₀, reassoc_of% hgP, h₀] using
      congrArg g hs
  exact ⟨fun s hs ↦ point_ne_projModelZero (f s) (by
      simpa only [← Scheme.Hom.comp_apply, hgP, h₀] using congrArg g hs),
    fun s hs ↦ point_projModelMulBy_two_ne_projModelZero (f s) (hn 2 s hs),
    fun s hs ↦ point_projModelMulBy_three_ne_projModelZero (f s) (hn 3 s hs)⟩

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

include hP h₁ h₂ h₃ in
variable (E) in
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

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
