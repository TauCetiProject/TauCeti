/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw

/-!
# The universal Legendre normal form over a scheme

Let `E` be an elliptic curve over a scheme `S`, let `P` and `Q` be sections of `E` which meet the
zero section over no point of `S` and are killed by multiplication by `2`, and let `ω` be a
nowhere-vanishing invariant differential on `E/S` such that the `ω`-adapted `x`-coordinate of
`(P, Q)` equals `1` (`E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1`). Over a field (or whenever `2` is
invertible, which the conditions force automatically), these conditions say that `(P, Q)` is a basis
of `E[2]` and `ω` is adjusted so that in the Weierstrass coordinates normalized by `x(P) = 0` and
`dx / (2y + a₁x + a₃) = ω`, one has `x(Q) = 1` (Katz–Mazur 2.2.9).

Then `(E, P, Q, ω)` is the pullback of the universal Legendre curve

`Y² = X(X - 1)(X - λ)`

over `Spec ℤ[1/2][λ, 1/λ(λ - 1)]`, equipped with its `2`-torsion basis `(0, 0)`, `(1, 0)` and its
canonical Weierstrass differential `dX / 2Y`, along a unique morphism
`S ⟶ Spec ℤ[1/2][λ, 1/λ(λ - 1)]` and by a unique pointed cartesian morphism from `E` carrying `P` to
`(0, 0)`, `Q` to `(1, 0)` and pulling `dX / 2Y` back to `ω`
(`EllipticCurveGeom.existsUnique_legendreNormalForm`). Conversely, any tuple `(P, Q, ω)` obtained by
such a pullback satisfies the conditions (`EllipticCurveGeom.exists_legendreNormalForm_iff`). No
hypothesis on `S` is needed: `S` may be nonreduced or non-affine, and `2` is not assumed invertible
on `S` beforehand.

Over an affine base this is `WeierstrassCurve.existsUnique_legendreNormalForm`, and the passage to
an arbitrary base glues the affine classifying pairs along the pointed Weierstrass charts of `E`
using `EllipticCurveGeom.glueMorphisms` and `EllipticCurveGeom.invariantDifferential_ext_of_atlas`.

The coefficient ring `ℤ[1/2][λ, 1/λ(λ - 1)]` (`WeierstrassCurve.UniversalLegendre.Ring`) lies in
`Type`. For schemes in `Scheme.{u}` the universal Legendre curve is read over
`ULift.{u} ℤ[1/2][λ, 1/λ(λ - 1)]` (`WeierstrassCurve.UniversalLegendre.curveULift`).

## Main definitions

* `WeierstrassCurve.UniversalLegendre.curveULift`: the universal Legendre curve over
  `ULift.{u} ℤ[1/2][λ, 1/λ(λ - 1)]`.
* `WeierstrassCurve.UniversalLegendre.firstPoint` and
  `WeierstrassCurve.UniversalLegendre.secondPoint`: the `2`-torsion points `(0, 0)` and `(1, 0)` of
  its projective model.
* `TauCeti.AlgebraicGeometry.UniversalLegendre.curveGeom`: the universal Legendre curve as an
  elliptic curve over `Spec ℤ[1/2][λ, 1/λ(λ - 1)]`, with `2`-torsion points
  `TauCeti.AlgebraicGeometry.UniversalLegendre.firstPointHom`,
  `TauCeti.AlgebraicGeometry.UniversalLegendre.secondPointHom` and canonical invariant differential
  `TauCeti.AlgebraicGeometry.UniversalLegendre.curveGeomDifferential`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_legendreNormalForm`: sections `P`, `Q`
  and an invariant differential `ω` satisfying the Legendre conditions are the pullback of the
  universal Legendre tuple along a unique pointed cartesian morphism.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_legendreNormalForm_iff`: such a morphism
  exists if and only if `(P, Q, ω)` satisfies the Legendre conditions.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_legendreNormalForm_curveGeom`: the same
  universal property read on `UniversalLegendre.curveGeom`.
* `TauCeti.AlgebraicGeometry.UniversalLegendre.adaptedXCoord_curveGeom` and siblings: the universal
  tuple on `curveGeom` satisfies the Legendre conditions.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.9 and 4.6.2.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve.UniversalLegendre

/-! ### The universal Legendre curve in an arbitrary universe -/

/-- The parameter `λ` in `ULift.{u} ℤ[1/2][λ, 1/λ(λ - 1)]`. -/
noncomputable def paramULift : ULift.{u} Ring :=
  .up param

/-- The universal Legendre curve `Y² = X(X - 1)(X - λ)` over `ULift.{u} ℤ[1/2][λ, 1/λ(λ - 1)]`. -/
noncomputable def curveULift : WeierstrassCurve (ULift.{u} Ring) :=
  TauCeti.freyCurve 1 (-paramULift)

/-- `curveULift` is `freyCurve 1 (-paramULift)`. -/
theorem curveULift_eq_freyCurve : curveULift.{u} = TauCeti.freyCurve 1 (-paramULift) :=
  (rfl)

/-- `curveULift` is the base change of `UniversalLegendre.curve` along `Ring ≃+* ULift.{u} Ring`. -/
theorem curveULift_eq :
    curveULift.{u} = curve.map (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom := by
  rw [curve_def, TauCeti.map_freyCurve, map_one, map_neg]
  rfl

/-- Base change of `curveULift` along `φ` gives `freyCurve 1 (-(φ paramULift))`. -/
@[simp]
theorem map_curveULift {A : Type*} [CommRing A] (φ : ULift.{u} Ring →+* A) :
    curveULift.map φ = TauCeti.freyCurve 1 (-(φ paramULift)) := by
  rw [curveULift_eq_freyCurve, TauCeti.map_freyCurve, map_one, map_neg]

/-- The universal Legendre curve over `ULift.{u} ℤ[1/2][λ, 1/λ(λ - 1)]` is elliptic. -/
instance : curveULift.{u}.IsElliptic := by
  rw [curveULift_eq]
  infer_instance

/-- The point `(0, 0)` lies on `curveULift`. -/
theorem equation_curveULift_zero : curveULift.{u}.toAffine.Equation 0 0 := by
  rw [curveULift_eq_freyCurve]
  exact equation_freyCurve_zero 1 (-paramULift)

/-- The point `(1, 0)` lies on `curveULift`. -/
theorem equation_curveULift_one_zero : curveULift.{u}.toAffine.Equation 1 0 := by
  rw [curveULift_eq_freyCurve]
  exact equation_freyCurve_one_zero (-paramULift)

/-- The point `(0, 0)` of the projective model of `curveULift`. -/
noncomputable def firstPoint : Spec (.of (ULift.{u} Ring)) ⟶ curveULift.{u}.projModel :=
  curveULift.projModelAffinePoint equation_curveULift_zero

/-- The point `(1, 0)` of the projective model of `curveULift`. -/
noncomputable def secondPoint : Spec (.of (ULift.{u} Ring)) ⟶ curveULift.{u}.projModel :=
  curveULift.projModelAffinePoint equation_curveULift_one_zero

/-- `firstPoint` is the affine point `(0, 0)` of `curveULift.projModel`. -/
theorem firstPoint_def :
    firstPoint.{u} = curveULift.projModelAffinePoint equation_curveULift_zero :=
  (rfl)

/-- `secondPoint` is the affine point `(1, 0)` of `curveULift.projModel`. -/
theorem secondPoint_def :
    secondPoint.{u} = curveULift.projModelAffinePoint equation_curveULift_one_zero :=
  (rfl)

/-- `firstPoint` is a section of `curveULift.projModelOver`. -/
@[reassoc (attr := simp)]
theorem firstPoint_projModelOver : firstPoint.{u} ≫ curveULift.projModelOver = 𝟙 _ :=
  projModelAffinePoint_projModelOver _

/-- `secondPoint` is a section of `curveULift.projModelOver`. -/
@[reassoc (attr := simp)]
theorem secondPoint_projModelOver : secondPoint.{u} ≫ curveULift.projModelOver = 𝟙 _ :=
  projModelAffinePoint_projModelOver _

-- The universal Legendre tuple satisfies all conditions of `exists_iso_legendreNormalForm_iff`,
-- witnessed by the identity isomorphism of `curveULift.projModel`.
private theorem basis_conditions :
    ∃ (hP₀ : ∀ s, firstPoint.{u} s ≠ curveULift.projModelZero s)
      (hQ₀ : ∀ s, secondPoint.{u} s ≠ curveULift.projModelZero s),
      firstPoint.{u} ≫ curveULift.projModelMulBy 2 = curveULift.projModelZero ∧
        secondPoint.{u} ≫ curveULift.projModelMulBy 2 = curveULift.projModelZero ∧
        (∀ s, secondPoint.{u} s ≠ firstPoint.{u} s) ∧
        curveULift.{u}.projModelAdaptedXCoord firstPoint_projModelOver secondPoint_projModelOver
          hP₀ hQ₀ curveULift.weierstrassDifferential = 1 := by
  have key {W : WeierstrassCurve (ULift.{u} Ring)} [hE : W.IsElliptic]
      (hW : W = TauCeti.freyCurve 1 (-paramULift)) (h₁ : W.toAffine.Equation 0 0)
      (h₂ : W.toAffine.Equation 1 0) :
      ∃ (hP₀ : ∀ s, W.projModelAffinePoint h₁ s ≠ W.projModelZero s)
        (hQ₀ : ∀ s, W.projModelAffinePoint h₂ s ≠ W.projModelZero s),
        W.projModelAffinePoint h₁ ≫ W.projModelMulBy 2 = W.projModelZero ∧
          W.projModelAffinePoint h₂ ≫ W.projModelMulBy 2 = W.projModelZero ∧
          (∀ s, W.projModelAffinePoint h₂ s ≠ W.projModelAffinePoint h₁ s) ∧
          W.projModelAdaptedXCoord (projModelAffinePoint_projModelOver h₁)
            (projModelAffinePoint_projModelOver h₂) hP₀ hQ₀ W.weierstrassDifferential = 1 := by
    subst hW
    exact (exists_iso_legendreNormalForm_iff (projModelAffinePoint_projModelOver h₁)
      (projModelAffinePoint_projModelOver h₂)
      (TauCeti.freyCurve 1 (-paramULift)).weierstrassDifferential).mp
      ⟨paramULift, hE, Iso.refl _, by simp, by simp, by simp, by simp, by simp⟩
  exact key curveULift_eq_freyCurve _ _

/-- `firstPoint` misses the zero section at every point of the base. -/
theorem firstPoint_ne_projModelZero (s) : firstPoint.{u} s ≠ curveULift.projModelZero s :=
  basis_conditions.choose s

/-- `secondPoint` misses the zero section at every point of the base. -/
theorem secondPoint_ne_projModelZero (s) : secondPoint.{u} s ≠ curveULift.projModelZero s :=
  basis_conditions.choose_spec.choose s

/-- `firstPoint` is killed by `2`. -/
@[reassoc (attr := simp)]
theorem firstPoint_projModelMulBy_two :
    firstPoint.{u} ≫ curveULift.projModelMulBy 2 = curveULift.projModelZero :=
  basis_conditions.choose_spec.choose_spec.1

/-- `secondPoint` is killed by `2`. -/
@[reassoc (attr := simp)]
theorem secondPoint_projModelMulBy_two :
    secondPoint.{u} ≫ curveULift.projModelMulBy 2 = curveULift.projModelZero :=
  basis_conditions.choose_spec.choose_spec.2.1

/-- `secondPoint` differs from `firstPoint` at every point of the base. -/
theorem secondPoint_ne_firstPoint (s) : secondPoint.{u} s ≠ firstPoint.{u} s :=
  basis_conditions.choose_spec.choose_spec.2.2.1 s

/-- The `weierstrassDifferential`-adapted `x`-coordinate of `(firstPoint, secondPoint)` on
`curveULift` equals `1`. -/
@[simp]
theorem projModelAdaptedXCoord_weierstrassDifferential :
    curveULift.{u}.projModelAdaptedXCoord firstPoint_projModelOver secondPoint_projModelOver
      firstPoint_ne_projModelZero secondPoint_ne_projModelZero
      curveULift.weierstrassDifferential = 1 :=
  basis_conditions.choose_spec.choose_spec.2.2.2

end WeierstrassCurve.UniversalLegendre

namespace TauCeti.AlgebraicGeometry.UniversalLegendre

open WeierstrassCurve

/-! ### The universal Legendre curve as an elliptic curve -/

/-- The universal Legendre curve `Y² = X(X - 1)(X - λ)` as an elliptic curve over
`Spec ℤ[1/2][λ, 1/λ(λ - 1)]`, whose total space is the projective model of `curveULift`. -/
noncomputable abbrev curveGeom :
    EllipticCurveGeom (Spec (.of (ULift.{u} UniversalLegendre.Ring))) :=
  toEllipticCurveGeom UniversalLegendre.curveULift

/-- The point `(0, 0)` of the universal Legendre curve, as a base-valued point of `curveGeom`. -/
noncomputable def firstPointHom : 𝟙_ (Over (Spec (.of (ULift.{u} UniversalLegendre.Ring)))) ⟶
    Over.mk curveGeom.{u}.structureMap :=
  Over.homMk (UniversalLegendre.firstPoint ≫
    (toEllipticCurveGeomIso UniversalLegendre.curveULift).inv) <| by
      simp [← toEllipticCurveGeomIso_hom_projModelOver]

/-- The point `(1, 0)` of the universal Legendre curve, as a base-valued point of `curveGeom`. -/
noncomputable def secondPointHom : 𝟙_ (Over (Spec (.of (ULift.{u} UniversalLegendre.Ring)))) ⟶
    Over.mk curveGeom.{u}.structureMap :=
  Over.homMk (UniversalLegendre.secondPoint ≫
    (toEllipticCurveGeomIso UniversalLegendre.curveULift).inv) <| by
      simp [← toEllipticCurveGeomIso_hom_projModelOver]

/-- The canonical Weierstrass differential `dX / 2Y` on `curveGeom`. -/
noncomputable def curveGeomDifferential : curveGeom.{u}.InvariantDifferential :=
  UniversalLegendre.curveULift.toEllipticCurveGeomDifferential

/-- On the projective model, `firstPointHom` is `UniversalLegendre.firstPoint`. -/
@[simp]
theorem firstPointHom_left :
    firstPointHom.{u}.left =
      UniversalLegendre.firstPoint ≫
        (toEllipticCurveGeomIso UniversalLegendre.curveULift).inv :=
  (rfl)

/-- On the projective model, `secondPointHom` is `UniversalLegendre.secondPoint`. -/
@[simp]
theorem secondPointHom_left :
    secondPointHom.{u}.left =
      UniversalLegendre.secondPoint ≫
        (toEllipticCurveGeomIso UniversalLegendre.curveULift).inv :=
  (rfl)

/-- `firstPointHom` misses the zero section of `curveGeom` at every point of the base. -/
theorem firstPointHom_left_ne_zero (s) : firstPointHom.{u}.left s ≠ curveGeom.zero s := fun hs ↦
  UniversalLegendre.firstPoint_ne_projModelZero s <| by
    have h := congrArg (toEllipticCurveGeomIso UniversalLegendre.curveULift).hom hs
    simpa only [← Scheme.Hom.comp_apply, firstPointHom_left, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, zero_toEllipticCurveGeomIso_hom] using h

/-- `secondPointHom` misses the zero section of `curveGeom` at every point of the base. -/
theorem secondPointHom_left_ne_zero (s) : secondPointHom.{u}.left s ≠ curveGeom.zero s := fun hs ↦
  UniversalLegendre.secondPoint_ne_projModelZero s <| by
    have h := congrArg (toEllipticCurveGeomIso UniversalLegendre.curveULift).hom hs
    simpa only [← Scheme.Hom.comp_apply, secondPointHom_left, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, zero_toEllipticCurveGeomIso_hom] using h

/-- The `curveGeomDifferential`-adapted `x`-coordinate of `(firstPointHom, secondPointHom)` on
`curveGeom` equals `1`. -/
@[simp]
theorem adaptedXCoord_curveGeom :
    curveGeom.{u}.adaptedXCoord (Over.w firstPointHom) (Over.w secondPointHom)
      firstPointHom_left_ne_zero secondPointHom_left_ne_zero curveGeomDifferential = 1 := by
  have hcongr {W : WeierstrassCurve (ULift.{u} UniversalLegendre.Ring)} [W.IsElliptic]
      {P₁ P₂ Q₁ Q₂ : Spec (.of (ULift.{u} UniversalLegendre.Ring)) ⟶ W.projModel}
      (eP : P₁ = P₂) (eQ : Q₁ = Q₂) (hP₁) (hQ₁) (hP₁₀) (hQ₁₀) (hP₂) (hQ₂) (hP₂₀) (hQ₂₀) (ω) :
      W.projModelAdaptedXCoord (P := P₁) (Q := Q₁) hP₁ hQ₁ hP₁₀ hQ₁₀ ω =
        W.projModelAdaptedXCoord (P := P₂) (Q := Q₂) hP₂ hQ₂ hP₂₀ hQ₂₀ ω := by
    subst eP eQ
    rfl
  rw [UniversalLegendre.curveULift.adaptedXCoord_toEllipticCurveGeom]
  have hω : Scheme.Hom.conormalBasisPullback
      (f := 𝟙 (Spec (.of (ULift.{u} UniversalLegendre.Ring))))
      (g := (toEllipticCurveGeomIso UniversalLegendre.curveULift).inv)
      UniversalLegendre.curveULift.toEllipticCurveGeom.zero_comp
      UniversalLegendre.curveULift.projModelZero_projModelOver
      (IsPullback.of_horiz_isIso
        ⟨by rw [toEllipticCurveGeomIso_inv_structureMap, Category.comp_id]⟩)
      (by rw [projModelZero_toEllipticCurveGeomIso_inv, Category.id_comp])
      curveGeomDifferential = UniversalLegendre.curveULift.weierstrassDifferential := by
    rw [curveGeomDifferential, toEllipticCurveGeomDifferential_def,
      Scheme.Hom.conormalBasisPullback_comp,
      Scheme.Hom.conormalBasisPullback_congr
        UniversalLegendre.curveULift.projModelZero_projModelOver
        UniversalLegendre.curveULift.projModelZero_projModelOver
        (Category.id_comp _) (Iso.inv_hom_id _) _ _ (.of_horiz_isIso ⟨by simp⟩) (by simp)]
    simp
  rw [hω, hcongr (by simp) (by simp) _ _ _ _ UniversalLegendre.firstPoint_projModelOver
    UniversalLegendre.secondPoint_projModelOver UniversalLegendre.firstPoint_ne_projModelZero
    UniversalLegendre.secondPoint_ne_projModelZero,
    UniversalLegendre.projModelAdaptedXCoord_weierstrassDifferential, map_one]

end TauCeti.AlgebraicGeometry.UniversalLegendre

namespace TauCeti.AlgebraicGeometry

open WeierstrassCurve UniversalLegendre

/-! ### Classifying pairs over an affine base -/

-- `(f, g)` classifies `(π, zero, P, Q, ω)`: `g` exhibits `X` as the base change of `curveULift`
-- along `f`, carrying `zero`, `P`, `Q` to `projModelZero`, `firstPoint`, `secondPoint` and pulling
-- `curveULift.weierstrassDifferential` back to `ω`.
private def IsLegendre {X T : Scheme.{u}} (π : X ⟶ T) [IsSeparated π]
    [SmoothOfRelativeDimension 1 π] {zero : T ⟶ X} (hzero : zero ≫ π = 𝟙 T)
    (P Q : T ⟶ X) (ω : 𝟙_ T.Modules ≅ zero.conormalSheaf)
    (f : T ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring)))
    (g : X ⟶ curveULift.{u}.projModel) : Prop :=
  ∃ (hg : IsPullback g π curveULift.projModelOver f)
    (h₀ : zero ≫ g = f ≫ curveULift.projModelZero),
    P ≫ g = f ≫ firstPoint ∧ Q ≫ g = f ≫ secondPoint ∧
      Scheme.Hom.conormalBasisPullback curveULift.projModelZero_projModelOver hzero hg h₀
        curveULift.weierstrassDifferential = ω

-- `IsLegendre` pulls back along pointed cartesian squares.
private theorem IsLegendre.comp {X T X' T' : Scheme.{u}} {π : X ⟶ T} [IsSeparated π]
    [SmoothOfRelativeDimension 1 π] {zero : T ⟶ X} {hzero : zero ≫ π = 𝟙 T}
    {P Q : T ⟶ X} {ω : 𝟙_ T.Modules ≅ zero.conormalSheaf}
    {f : T ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))} {g : X ⟶ curveULift.{u}.projModel}
    (h : IsLegendre π hzero P Q ω f g)
    {π' : X' ⟶ T'} [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    {zero' : T' ⟶ X'} (hzero' : zero' ≫ π' = 𝟙 T') {P' Q' : T' ⟶ X'}
    {a : X' ⟶ X} {b : T' ⟶ T} (hab : IsPullback a π' π b) (h₀ : zero' ≫ a = b ≫ zero)
    (hP : P' ≫ a = b ≫ P) (hQ : Q' ≫ a = b ≫ Q) :
    IsLegendre π' hzero' P' Q'
      (Scheme.Hom.conormalBasisPullback hzero hzero' hab h₀ ω) (b ≫ f) (a ≫ g) := by
  obtain ⟨hg, hz, hgP, hgQ, hgω⟩ := h
  refine ⟨hab.paste_horiz hg, by simp [reassoc_of% h₀, hz], by simp [reassoc_of% hP, hgP],
    by simp [reassoc_of% hQ, hgQ], ?_⟩
  rw [← hgω, Scheme.Hom.conormalBasisPullback_comp]

section Affine

variable {R : Type u} [CommRing R]

-- Ring homomorphisms out of `ULift ℤ[1/2][λ, 1/λ(λ - 1)]` are determined by the image of `λ`.
private theorem ringHom_ext_ULift {φ φ' : ULift.{u} UniversalLegendre.Ring →+* R}
    (hl : φ paramULift = φ' paramULift) : φ = φ' := by
  have : φ.comp (ULift.ringEquiv.symm : UniversalLegendre.Ring ≃+* ULift.{u} _).toRingHom =
      φ'.comp (ULift.ringEquiv.symm : UniversalLegendre.Ring ≃+* ULift.{u} _).toRingHom :=
    UniversalLegendre.Ring.ringHom_ext hl
  ext x
  exact congr($this x.down)

-- The classifying homomorphism `ULift ℤ[1/2][λ, 1/λ(λ - 1)] →+* R` of an element `l : R` with
-- `2l(l - 1)` a unit.
private noncomputable def liftULift {l : R} (h : IsUnit (2 * l * (l - 1))) :
    ULift.{u} UniversalLegendre.Ring →+* R :=
  (UniversalLegendre.lift h).comp ULift.ringEquiv.toRingHom

private theorem liftULift_paramULift {l : R} (h : IsUnit (2 * l * (l - 1))) :
    liftULift h paramULift = l :=
  UniversalLegendre.lift_param h

-- Base change along `φ : ULift Ring →+* R` classifies
-- `(W', (0, 0), (1, 0), W'.weierstrassDifferential)` when `curveULift.map φ = W'`.
private theorem isLegendre_eqToHom_projModelBaseChange
    (φ : ULift.{u} UniversalLegendre.Ring →+* R) {W' : WeierstrassCurve R} [W'.IsElliptic]
    (hW' : curveULift.map φ = W') {x₁ y₁ x₂ y₂ : R} (h₁ : W'.toAffine.Equation x₁ y₁)
    (h₂ : W'.toAffine.Equation x₂ y₂) (hx₁ : x₁ = 0) (hy₁ : y₁ = 0)
    (hx₂ : x₂ = 1) (hy₂ : y₂ = 0) :
    IsLegendre W'.projModelOver W'.projModelZero_projModelOver
      (W'.projModelAffinePoint h₁) (W'.projModelAffinePoint h₂) W'.weierstrassDifferential
      (Spec.map (CommRingCat.ofHom φ))
      (eqToHom (congrArg projModel hW'.symm) ≫ curveULift.projModelBaseChange φ) := by
  subst hW'
  have h₁' : (curveULift.map φ).projModelAffinePoint h₁ =
      (curveULift.map φ).projModelAffinePoint (equation_curveULift_zero.map φ) :=
    (projModelAffinePoint_inj h₁).mpr ⟨hx₁.trans (map_zero φ).symm, hy₁.trans (map_zero φ).symm⟩
  have h₂' : (curveULift.map φ).projModelAffinePoint h₂ =
      (curveULift.map φ).projModelAffinePoint (equation_curveULift_one_zero.map φ) :=
    (projModelAffinePoint_inj h₂).mpr ⟨hx₂.trans (map_one φ).symm, hy₂.trans (map_zero φ).symm⟩
  refine ⟨by simpa using curveULift.isPullback_projModelBaseChange φ, by simp, ?_, ?_, ?_⟩
  · rw [h₁', eqToHom_refl, Category.id_comp, projModelAffinePoint_projModelBaseChange]
    rfl
  · rw [h₂', eqToHom_refl, Category.id_comp, projModelAffinePoint_projModelBaseChange]
    rfl
  · rw [Scheme.Hom.conormalBasisPullback_congr curveULift.projModelZero_projModelOver
      (curveULift.map φ).projModelZero_projModelOver rfl
      (by rw [eqToHom_refl, Category.id_comp]) _ _
      (curveULift.isPullback_projModelBaseChange φ)
      (curveULift.projModelZero_projModelBaseChange φ)]
    exact curveULift.conormalBasisPullback_weierstrassDifferential_projModelBaseChange φ

variable {W : WeierstrassCurve R} [W.IsElliptic] {P Q : Spec (.of R) ⟶ W.projModel}

private instance isElliptic_freyCurve_paramULift {A : Type*} [CommRing A]
    (φ : ULift.{u} UniversalLegendre.Ring →+* A) :
    (TauCeti.freyCurve 1 (-(φ paramULift))).IsElliptic := by
  rw [← map_curveULift φ]
  infer_instance

-- Any `IsLegendre` pair `(Spec.map φ, g)` factors through a pointed isomorphism from
-- `freyCurve 1 (-(φ paramULift))` carrying `(0, 0)`, `(1, 0)` to `P`, `Q` and pulling `ω` back to
-- `weierstrassDifferential`.
private theorem exists_iso_of_isLegendre (hP : P ≫ W.projModelOver = 𝟙 _)
    (hQ : Q ≫ W.projModelOver = 𝟙 _) (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    {φ : ULift.{u} UniversalLegendre.Ring →+* R} {g : W.projModel ⟶ curveULift.projModel}
    (hg : IsLegendre W.projModelOver W.projModelZero_projModelOver P Q ω
      (Spec.map (CommRingCat.ofHom φ)) g) :
    ∃ (e : (TauCeti.freyCurve 1 (-(φ paramULift))).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-(φ paramULift))).projModelOver)
      (he₀ : (TauCeti.freyCurve 1 (-(φ paramULift))).projModelZero ≫ e.hom = W.projModelZero),
      (TauCeti.freyCurve 1 (-(φ paramULift))).projModelAffinePoint
          (equation_freyCurve_zero 1 _) ≫ e.hom = P ∧
        (TauCeti.freyCurve 1 (-(φ paramULift))).projModelAffinePoint
          (equation_freyCurve_one_zero _) ≫ e.hom = Q ∧
        Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
          W.projModelZero_projModelOver
          (TauCeti.freyCurve 1 (-(φ paramULift))).projModelZero_projModelOver
          (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
          (by rw [he₀, Category.id_comp]) ω =
        (TauCeti.freyCurve 1 (-(φ paramULift))).weierstrassDifferential ∧
        g = e.inv ≫ eqToHom (congrArg projModel (map_curveULift φ).symm) ≫
          curveULift.projModelBaseChange φ := by
  obtain ⟨hg_sq, hg_0, hg_P, hg_Q, hg_ω⟩ := hg
  obtain ⟨hT_sq, hT_0, hT_P, hT_Q, hT_ω⟩ := isLegendre_eqToHom_projModelBaseChange φ
    (map_curveULift φ) (equation_freyCurve_zero 1 _) (equation_freyCurve_one_zero _) rfl rfl rfl rfl
  let e := hg_sq.isoIsPullback _ _ hT_sq
  have he : e.hom ≫ _ = g := hg_sq.isoIsPullback_hom_fst _ _ hT_sq
  have he' : e.hom ≫ _ = W.projModelOver := hg_sq.isoIsPullback_hom_snd _ _ hT_sq
  have hesymm : e.symm.hom ≫ W.projModelOver =
      (TauCeti.freyCurve 1 (-(φ paramULift))).projModelOver := by simp [← he']
  have hesymm₀ : (TauCeti.freyCurve 1 (-(φ paramULift))).projModelZero ≫ e.symm.hom =
      W.projModelZero := by
    rw [Iso.symm_hom, Iso.comp_inv_eq]
    exact hT_sq.hom_ext (by rw [Category.assoc, he, hg_0, hT_0]) (by simp [he'])
  refine ⟨e.symm, hesymm, hesymm₀, ?_, ?_, ?_, by simp [← he]⟩
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    exact hT_sq.hom_ext (by rw [Category.assoc, he, hg_P, hT_P]) (by simp [he', hP])
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    exact hT_sq.hom_ext (by rw [Category.assoc, he, hg_Q, hT_Q]) (by simp [he', hQ])
  · rw [← hg_ω, Scheme.Hom.conormalBasisPullback_comp]
    refine (Scheme.Hom.conormalBasisPullback_congr curveULift.projModelZero_projModelOver
      (TauCeti.freyCurve 1 (-(φ paramULift))).projModelZero_projModelOver
      (Category.id_comp _) ?_ _ _ hT_sq hT_0 _).trans hT_ω
    rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]

variable (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
  (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
  (hP₂ : P ≫ W.projModelMulBy 2 = W.projModelZero)
  (hQ₂ : Q ≫ W.projModelMulBy 2 = W.projModelZero)
  (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
  (hω : W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1)

include hP hQ hP₀ hQ₀ hP₂ hQ₂ hω

-- Existence of a classifying pair over `Spec R`.
private theorem exists_isLegendre :
    ∃ f g, IsLegendre W.projModelOver W.projModelZero_projModelOver P Q ω f g := by
  obtain ⟨l, ⟨hEll, e, he, he₀, heP, heQ, heω⟩, -⟩ :=
    W.existsUnique_legendreNormalForm hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω
  have hl : IsUnit (2 * l * (l - 1)) := (TauCeti.isElliptic_freyCurve_one_neg_iff (l := l)).mp hEll
  have hT := isLegendre_eqToHom_projModelBaseChange (liftULift hl)
    (by rw [map_curveULift, liftULift_paramULift]) (equation_freyCurve_zero 1 (-l))
    (equation_freyCurve_one_zero (-l)) rfl rfl rfl rfl
  have he₀' : W.projModelZero ≫ e.inv = (TauCeti.freyCurve 1 (-l)).projModelZero :=
    (Iso.comp_inv_eq e).mpr he₀.symm
  have heP' : P ≫ e.inv =
      (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) :=
    (Iso.comp_inv_eq e).mpr heP.symm
  have heQ' : Q ≫ e.inv =
      (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) :=
    (Iso.comp_inv_eq e).mpr heQ.symm
  have hsq : IsPullback e.inv W.projModelOver (TauCeti.freyCurve 1 (-l)).projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [← he]⟩
  have hcomp := hT.comp W.projModelZero_projModelOver hsq (by rw [he₀', Category.id_comp])
    (by rw [heP', Category.id_comp]) (by rw [heQ', Category.id_comp])
  obtain ⟨hc_sq, hc_0, hc_P, hc_Q, hc_ω⟩ := hcomp
  refine ⟨Spec.map (CommRingCat.ofHom (liftULift hl)), _,
    by simpa using hc_sq, by simpa using hc_0, by simpa using hc_P, by simpa using hc_Q, ?_⟩
  have hω_inv : Scheme.Hom.conormalBasisPullback
      (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver W.projModelZero_projModelOver hsq
      (by rw [he₀', Category.id_comp]) (TauCeti.freyCurve 1 (-l)).weierstrassDifferential = ω := by
    rw [← heω, Scheme.Hom.conormalBasisPullback_comp]
    exact (Scheme.Hom.conormalBasisPullback_congr W.projModelZero_projModelOver
      W.projModelZero_projModelOver (Category.id_comp _) (Iso.inv_hom_id e) _ _
      (.of_horiz_isIso ⟨by simp⟩) (by simp) ω).trans
      (Scheme.Hom.conormalBasisPullback_id W.projModelZero_projModelOver _ _ ω)
  refine (Scheme.Hom.conormalBasisPullback_congr curveULift.projModelZero_projModelOver
    W.projModelZero_projModelOver (Category.id_comp _).symm rfl _ _ hc_sq hc_0 _).trans ?_
  exact hc_ω.trans hω_inv

-- Existence and uniqueness of a classifying pair over `Spec R`.
private theorem existsUnique_isLegendre :
    ∃! fg : (Spec (.of R) ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))) ×
      (W.projModel ⟶ curveULift.projModel),
      IsLegendre W.projModelOver W.projModelZero_projModelOver P Q ω fg.1 fg.2 := by
  obtain ⟨f, g, hfg⟩ := exists_isLegendre hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω
  refine ⟨(f, g), hfg, fun ⟨f', g'⟩ hfg' ↦ ?_⟩
  obtain ⟨⟨φ⟩, rfl⟩ := Spec.map_surjective f
  obtain ⟨⟨φ'⟩, rfl⟩ := Spec.map_surjective f'
  obtain ⟨e, he, he₀, heP, heQ, heω, rfl⟩ := exists_iso_of_isLegendre hP hQ ω hfg
  obtain ⟨e', he', he₀', heP', heQ', heω', rfl⟩ := exists_iso_of_isLegendre hP hQ ω hfg'
  have hl := (W.existsUnique_legendreNormalForm hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω).unique
    (y₁ := φ' paramULift) (y₂ := φ paramULift)
    ⟨inferInstance, e', he', he₀', heP', heQ', heω'⟩
    ⟨inferInstance, e, he, he₀, heP, heQ, heω⟩
  obtain rfl : φ' = φ := ringHom_ext_ULift hl
  rw [legendreNormalForm_iso_ext he' he₀' he he₀ (heP'.trans heP.symm) heω' heω]

end Affine

/-! ### Gluing Legendre classifying pairs over an arbitrary scheme -/

namespace EllipticCurveGeom

open PointedWeierstrassChart

section Glue

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P Q : S ⟶ E.carrier}
  (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)

-- Along a morphism of chart bases over `S`, `projModelMap hh` pulls `c.modelDifferential ω` back to
-- `k.modelDifferential ω`.
private theorem conormalBasisPullback_projModelMap
    {k c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap) (ω : E.InvariantDifferential) :
    Scheme.Hom.conormalBasisPullback c.equation.projModelZero_projModelOver
        k.equation.projModelZero_projModelOver (isPullback_projModelMap hh)
        (projModelZero_projModelMap hh) (c.modelDifferential ω) =
      k.modelDifferential ω := by
  rw [modelDifferential_def, modelDifferential_def, Scheme.Hom.conormalBasisPullback_comp]
  refine Scheme.Hom.conormalBasisPullback_congr E.zero_comp
    k.equation.projModelZero_projModelOver ?_ ?_ _ _ _ _ ω
  · simp [hh]
  · rw [← cancel_epi k.modelIso.hom, modelIso_hom_projModelMap_assoc, Iso.hom_inv_id_assoc,
      pullbackCarrierMap_toTotal, Iso.hom_inv_id_assoc]

-- Restricting a global `IsLegendre` pair `(f, g)` of `E` to a chart `c`.
private theorem isLegendre_chart (ω : E.InvariantDifferential)
    (c : PointedWeierstrassChart E.structureMap E.zero)
    {f : S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))} {g : E.carrier ⟶ curveULift.projModel}
    (hg : IsLegendre E.structureMap E.zero_comp P Q ω f g) :
    IsLegendre c.equation.projModelOver c.equation.projModelZero_projModelOver
      (c.modelPoint hP) (c.modelPoint hQ) (c.modelDifferential ω)
      ((c.baseIso.inv ≫ c.baseMap) ≫ f) ((c.modelIso.inv ≫ c.toTotal) ≫ g) := by
  rw [modelDifferential_def]
  exact hg.comp c.equation.projModelZero_projModelOver c.isPullback_modelIso_inv_toTotal
    c.projModelZero_modelIso_inv_toTotal (c.modelPoint_modelIso_inv_toTotal hP)
    (c.modelPoint_modelIso_inv_toTotal hQ)

variable (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
  (hP₂ : P ≫ (E.mulBy 2).left = E.zero) (hQ₂ : Q ≫ (E.mulBy 2).left = E.zero)
  (ω : E.InvariantDifferential) (hω : E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1)

include hP hQ hP₀ hQ₀ hω in
-- On every chart `c`, `E.adaptedXCoord = 1` implies `c.equation.projModelAdaptedXCoord = 1`.
private theorem projModelAdaptedXCoord_eq_one_of_chart
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.equation.projModelAdaptedXCoord (c.modelPoint_projModelOver hP)
      (c.modelPoint_projModelOver hQ) (c.modelPoint_apply_ne hP hP₀)
      (c.modelPoint_apply_ne hQ hQ₀) (c.modelDifferential ω) = 1 := by
  have h := E.baseMap_appTop_adaptedXCoord hP hQ hP₀ hQ₀ ω c
  rw [hω, map_one] at h
  have h1 := congrArg c.baseIso.inv.appTop h.symm
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop,
    CommRingCat.id_apply, map_one] at h1
  simpa using congrArg (Scheme.ΓSpecIso c.ring).hom h1

include hP hQ hP₀ hQ₀ hP₂ hQ₂ hω

-- Every chart `c` of `E` has a unique Legendre classifying pair.
private theorem existsUnique_chartIsLegendre
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    ∃! fg : (Spec c.ring ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))) ×
      (c.equation.projModel ⟶ curveULift.projModel),
      IsLegendre c.equation.projModelOver c.equation.projModelZero_projModelOver
        (c.modelPoint hP) (c.modelPoint hQ) (c.modelDifferential ω) fg.1 fg.2 :=
  existsUnique_isLegendre (c.modelPoint_projModelOver hP) (c.modelPoint_projModelOver hQ)
    (c.modelPoint_apply_ne hP hP₀) (c.modelPoint_apply_ne hQ hQ₀)
    (by simpa [hP₂] using (E.modelPoint_mulBy c hP 2).symm)
    (by simpa [hQ₂] using (E.modelPoint_mulBy c hQ 2).symm)
    (c.modelDifferential ω) (projModelAdaptedXCoord_eq_one_of_chart hP hQ hP₀ hQ₀ ω hω c)

private noncomputable def chartBase (c : PointedWeierstrassChart E.structureMap E.zero) :
    Spec c.ring ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring)) :=
  (existsUnique_chartIsLegendre hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c).exists.choose.1

private noncomputable def chartTotal (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.equation.projModel ⟶ curveULift.{u}.projModel :=
  (existsUnique_chartIsLegendre hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c).exists.choose.2

private theorem isLegendre_chartBase (c : PointedWeierstrassChart E.structureMap E.zero) :
    IsLegendre c.equation.projModelOver c.equation.projModelZero_projModelOver
      (c.modelPoint hP) (c.modelPoint hQ) (c.modelDifferential ω)
      (chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c) (chartTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c) :=
  (existsUnique_chartIsLegendre hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c).exists.choose_spec

-- Compatibility of `(chartBase, chartTotal)` along morphisms of chart bases.
private theorem chartBase_comp_and_chartTotal_comp
    {k c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap) :
    (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c =
        chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω k ∧
      projModelMap hh ≫ chartTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c =
        chartTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω k := by
  have hpull := (isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c).comp
    k.equation.projModelZero_projModelOver (isPullback_projModelMap hh)
    (projModelZero_projModelMap hh) (modelPoint_projModelMap hP hh) (modelPoint_projModelMap hQ hh)
  rw [conormalBasisPullback_projModelMap hh ω] at hpull
  exact Prod.ext_iff.mp <| (existsUnique_chartIsLegendre hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω k).unique
    (y₁ := (_, _)) (y₂ := (_, _)) hpull (isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω k)

private noncomputable def pieceBase (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback (𝟙 S) c.baseMap ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring)) :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c

private theorem map_pieceBase {k c : PointedWeierstrassChart E.structureMap E.zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap) :
    pullback.map (𝟙 S) k.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c = pieceBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω k := by
  simp [pieceBase, ← (chartBase_comp_and_chartTotal_comp hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω hh).1]

private noncomputable def pieceTotal (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback E.structureMap c.baseMap ⟶ curveULift.{u}.projModel :=
  c.isPullback.isoPullback.inv ≫ c.modelIso.hom ≫ chartTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c

private theorem map_pieceTotal {k c : PointedWeierstrassChart E.structureMap E.zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap) :
    pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _) (by simp)
      (by simp [hh]) ≫ pieceTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c =
      pieceTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω k := by
  have key : pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _)
      (by simp) (by simp [hh]) ≫ c.isPullback.isoPullback.inv =
      k.isPullback.isoPullback.inv ≫ pullbackCarrierMap hh :=
    c.isPullback.hom_ext (by simp) (by simp)
  rw [pieceTotal, pieceTotal, reassoc_of% key,
    ← (chartBase_comp_and_chartTotal_comp hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω hh).2]
  simp

private noncomputable def glueBase : S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring)) :=
  glueMorphisms (pieceBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) (map_pieceBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)

private noncomputable def glueTotal : E.carrier ⟶ curveULift.{u}.projModel :=
  glueMorphisms (pieceTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) (map_pieceTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)

@[reassoc]
private theorem baseMap_glueBase (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap ≫ glueBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω =
      c.baseIso.hom ≫ chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c := by
  simpa [glueBase, pieceBase, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
      fst_glueMorphisms (pieceBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)
        (map_pieceBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) c

private theorem toTotal_glueTotal (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.toTotal ≫ glueTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω =
      c.modelIso.hom ≫ chartTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω c := by
  simpa [glueTotal, pieceTotal, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    c.isPullback.isoPullback.hom ≫=
      fst_glueMorphisms (pieceTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)
        (map_pieceTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) c

-- The glued pair satisfies `IsLegendre` over `S`.
private theorem isLegendre_glue :
    IsLegendre E.structureMap E.zero_comp P Q ω
      (glueBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) (glueTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) := by
  obtain ⟨A⟩ := E.localModel
  have hsq : IsPullback (glueTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) E.structureMap
      curveULift.projModelOver (glueBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω) := by
    refine (Scheme.isPullback_of_openCover _ _ _ _ A.openCover fun i ↦ ?_).flip
    -- the maps of `A.openCover` are the chart base maps, and those of its pullback along
    -- `E.structureMap` are the projections; `simp` does not see through the pullback cover here
    change IsPullback (pullback.snd E.structureMap (A.chart i).baseMap)
      (pullback.fst E.structureMap (A.chart i).baseMap ≫
        glueTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)
      ((A.chart i).baseMap ≫ glueBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)
      curveULift.projModelOver
    rw [baseMap_glueBase, ← (A.chart i).isPullback.isoPullback_inv_fst, Category.assoc,
      toTotal_glueTotal]
    exact (isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω (A.chart i)).choose.flip.of_iso
      ((A.chart i).modelIso.symm ≪≫ (A.chart i).isPullback.isoPullback) (A.chart i).baseIso.symm
      (.refl _) (.refl _) (by simp [Iso.eq_inv_comp]) (by simp) (by simp) (by simp)
  have h₀ : E.zero ≫ glueTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω =
      glueBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω ≫ curveULift.projModelZero :=
    A.openCover.hom_ext _ _ fun i ↦ by
      dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
      rw [← (A.chart i).pulledZero_toTotal_assoc, toTotal_glueTotal,
        (A.chart i).modelIso_zero_assoc,
        (isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω (A.chart i)).choose_spec.choose,
        baseMap_glueBase_assoc]
  refine ⟨hsq, h₀, A.openCover.hom_ext _ _ fun i ↦ ?_, A.openCover.hom_ext _ _ fun i ↦ ?_,
    E.invariantDifferential_ext_of_atlas A fun i ↦ ?_⟩
  · dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
    rw [← chartPoint_toTotal_assoc _ hP, toTotal_glueTotal,
      reassoc_of% chartPoint_modelIso_hom _ hP,
      (isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω (A.chart i)).choose_spec.choose_spec.1,
      baseMap_glueBase_assoc]
  · dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
    rw [← chartPoint_toTotal_assoc _ hQ, toTotal_glueTotal,
      reassoc_of% chartPoint_modelIso_hom _ hQ,
      (isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω (A.chart i)).choose_spec.choose_spec.2.1,
      baseMap_glueBase_assoc]
  · obtain ⟨hc_sq, hc_0, -, -, hc_ω⟩ :=
      isLegendre_chartBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω (A.chart i)
    rw [modelDifferential_def, Scheme.Hom.conormalBasisPullback_comp]
    refine (Scheme.Hom.conormalBasisPullback_congr curveULift.projModelZero_projModelOver
      (A.chart i).equation.projModelZero_projModelOver ?_ ?_ _ _ hc_sq hc_0 _).trans hc_ω
    · rw [Category.assoc, baseMap_glueBase, Iso.inv_hom_id_assoc]
    · rw [Category.assoc, toTotal_glueTotal, Iso.inv_hom_id_assoc]

-- Uniqueness of a global `IsLegendre` pair over `S`.
private theorem isLegendre_unique
    {f f' : S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))}
    {g g' : E.carrier ⟶ curveULift.projModel}
    (hg : IsLegendre E.structureMap E.zero_comp P Q ω f g)
    (hg' : IsLegendre E.structureMap E.zero_comp P Q ω f' g') : f = f' ∧ g = g' := by
  obtain ⟨A⟩ := E.localModel
  have key (i) := Prod.ext_iff.mp <|
    (existsUnique_chartIsLegendre hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω (A.chart i)).unique
      (y₁ := (_, _)) (y₂ := (_, _))
      (isLegendre_chart hP hQ ω (A.chart i) hg) (isLegendre_chart hP hQ ω (A.chart i) hg')
  refine ⟨A.openCover.hom_ext _ _ fun i ↦ ?_, A.hom_ext_of_toTotal g g' fun i ↦ ?_⟩
  · dsimp only [PointedWeierstrassAtlas.openCover_X, PointedWeierstrassAtlas.openCover_f]
    rw [← cancel_epi (A.chart i).baseIso.inv]
    simpa using (key i).1
  · rw [← cancel_epi (A.chart i).modelIso.inv]
    simpa using (key i).2

end Glue

/-! ### The universal property -/

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {P Q : S ⟶ E.carrier}
  (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)

section Universal

variable (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
  (hP₂ : P ≫ (E.mulBy 2).left = E.zero) (hQ₂ : Q ≫ (E.mulBy 2).left = E.zero)
  (ω : E.InvariantDifferential) (hω : E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1)

include hP hQ hP₀ hQ₀ hP₂ hQ₂ hω in
/-- **The universal Legendre normal form over a scheme** (Katz–Mazur 2.2.9). Let `E` be an elliptic
curve over a scheme `S`, `P` and `Q` sections of `E` missing the zero section at every point of `S`
and killed by `2`, and `ω` an invariant differential on `E` with
`E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1`. Then there is a unique pair of a morphism
`f : S ⟶ Spec ℤ[1/2][λ, 1/λ(λ - 1)]` and a morphism `g` from `E` to the projective model of the
universal Legendre curve `Y² = X(X - 1)(X - λ)` exhibiting `E` as the pullback of the universal
curve along `f`, carrying the zero section to the zero section, `P` to `(0, 0)`, `Q` to `(1, 0)`,
and pulling `dX / 2Y` back to `ω`. -/
theorem existsUnique_legendreNormalForm :
    ∃! fg : (S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))) ×
      (E.carrier ⟶ curveULift.projModel),
      ∃ (hg : IsPullback fg.2 E.structureMap curveULift.projModelOver fg.1)
        (h₀ : E.zero ≫ fg.2 = fg.1 ≫ curveULift.projModelZero),
        P ≫ fg.2 = fg.1 ≫ firstPoint ∧ Q ≫ fg.2 = fg.1 ≫ secondPoint ∧
          Scheme.Hom.conormalBasisPullback curveULift.projModelZero_projModelOver E.zero_comp
            hg h₀ curveULift.weierstrassDifferential = ω :=
  ⟨(glueBase hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω, glueTotal hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω),
    isLegendre_glue hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω, fun _ hfg ↦
      have h := isLegendre_unique hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω hfg
        (isLegendre_glue hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω)
      Prod.ext h.1 h.2⟩

end Universal

/-! ### Reading the universal Legendre curve as `curveGeom` -/

-- Translating classifying pairs between `curveGeom` and `curveULift.projModel` through
-- `toEllipticCurveGeomIso`.
private theorem isLegendre_curveGeom_iff (ω : E.InvariantDifferential)
    {f : S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))}
    {g : E.carrier ⟶ curveGeom.{u}.carrier} :
    (∃ (hg : IsPullback g E.structureMap curveGeom.structureMap f)
      (h₀ : E.zero ≫ g = f ≫ curveGeom.zero),
      P ≫ g = f ≫ firstPointHom.left ∧ Q ≫ g = f ≫ secondPointHom.left ∧
        invariantDifferentialPullback hg h₀ curveGeomDifferential = ω) ↔
    IsLegendre E.structureMap E.zero_comp P Q ω f
      (g ≫ (toEllipticCurveGeomIso curveULift).hom) := by
  have hiso : IsPullback (toEllipticCurveGeomIso curveULift.{u}).hom curveGeom.structureMap
      curveULift.projModelOver (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩
  constructor
  · rintro ⟨hg, h₀, hgP, hgQ, hgω⟩
    have hg' : IsPullback (g ≫ (toEllipticCurveGeomIso curveULift).hom) E.structureMap
        curveULift.projModelOver f := by simpa using hg.paste_horiz hiso
    have h₀' : E.zero ≫ g ≫ (toEllipticCurveGeomIso curveULift).hom =
        f ≫ curveULift.projModelZero := by
      rw [← Category.assoc, h₀, Category.assoc, zero_toEllipticCurveGeomIso_hom]
    refine ⟨hg', h₀', by simp [reassoc_of% hgP], by simp [reassoc_of% hgQ], ?_⟩
    rw [← hgω, invariantDifferentialPullback_def, curveGeomDifferential,
      toEllipticCurveGeomDifferential_def, Scheme.Hom.conormalBasisPullback_comp]
    exact Scheme.Hom.conormalBasisPullback_congr curveULift.projModelZero_projModelOver
      E.zero_comp (Category.comp_id f).symm rfl hg' h₀' _ _ _
  · rintro ⟨hg', h₀', hgP', hgQ', hgω'⟩
    have hg : IsPullback g E.structureMap curveGeom.structureMap f :=
      IsPullback.of_right (by simpa using hg') (by simpa using hg'.w) hiso
    have h₀ : E.zero ≫ g = f ≫ curveGeom.zero := by
      rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom]
      simpa using h₀'
    refine ⟨hg, h₀, ?_, ?_, ?_⟩
    · rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom]
      simpa using hgP'
    · rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom]
      simpa using hgQ'
    · rw [← hgω', invariantDifferentialPullback_def, curveGeomDifferential,
        toEllipticCurveGeomDifferential_def, Scheme.Hom.conormalBasisPullback_comp]
      exact Scheme.Hom.conormalBasisPullback_congr curveULift.projModelZero_projModelOver
        E.zero_comp (Category.comp_id f) rfl _ _ hg' h₀' _

include hP hQ in
/-- **Necessity and sufficiency of the Legendre conditions.** Sections `P`, `Q` and an invariant
differential `ω` on `E` arise by pullback from the universal Legendre curve along a pointed
cartesian square if and only if `P` and `Q` miss the zero section everywhere, are killed by `2`,
differ at every point of `S`, and satisfy `E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1`. -/
theorem exists_legendreNormalForm_iff (ω : E.InvariantDifferential) :
    (∃ (f : S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring)))
      (g : E.carrier ⟶ curveULift.projModel)
      (hg : IsPullback g E.structureMap curveULift.projModelOver f)
      (h₀ : E.zero ≫ g = f ≫ curveULift.projModelZero),
      P ≫ g = f ≫ firstPoint ∧ Q ≫ g = f ≫ secondPoint ∧
        Scheme.Hom.conormalBasisPullback curveULift.projModelZero_projModelOver E.zero_comp hg h₀
          curveULift.weierstrassDifferential = ω) ↔
      ∃ (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s),
        P ≫ (E.mulBy 2).left = E.zero ∧ Q ≫ (E.mulBy 2).left = E.zero ∧
          (∀ s, Q s ≠ P s) ∧ E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1 := by
  refine ⟨fun ⟨f, g, hg, h₀, hgP, hgQ, hgω⟩ ↦ ?_,
    fun ⟨hP₀, hQ₀, hP₂, hQ₂, _, hω⟩ ↦
      let ⟨⟨f, g⟩, h, _⟩ := E.existsUnique_legendreNormalForm hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω
      ⟨f, g, h⟩⟩
  have hne {R₁ R₂ : S ⟶ E.carrier} {pt₁ pt₂ : _ ⟶ curveULift.projModel} (h₁ : R₁ ≫ g = f ≫ pt₁)
      (h₂ : R₂ ≫ g = f ≫ pt₂) (hpt : ∀ s, pt₁ s ≠ pt₂ s) (s : S) : R₁ s ≠ R₂ s := fun hs ↦
    hpt (f s) (by simpa only [← Scheme.Hom.comp_apply, h₁, h₂] using congrArg g hs)
  have h₂ {R' : S ⟶ E.carrier} (hR' : R' ≫ E.structureMap = 𝟙 S) {pt : _ ⟶ curveULift.projModel}
      (hpt : R' ≫ g = f ≫ pt) (hpt₂ : pt ≫ curveULift.projModelMulBy 2 = curveULift.projModelZero) :
      R' ≫ (E.mulBy 2).left = E.zero :=
    hg.hom_ext (by rw [Category.assoc, ← curveULift.comp_projModelMulBy_of_isPullback hg h₀,
      reassoc_of% hpt, hpt₂, h₀]) (by simp [hR'])
  have hP₀ := hne hgP h₀ firstPoint_ne_projModelZero
  have hQ₀ := hne hgQ h₀ secondPoint_ne_projModelZero
  refine ⟨hP₀, hQ₀, h₂ hP hgP firstPoint_projModelMulBy_two,
    h₂ hQ hgQ secondPoint_projModelMulBy_two, hne hgQ hgP secondPoint_ne_firstPoint, ?_⟩
  obtain ⟨hg', h₀', hgP', hgQ', hgω'⟩ :=
    (isLegendre_curveGeom_iff E ω (P := P) (Q := Q) (f := f)
      (g := g ≫ (toEllipticCurveGeomIso curveULift).inv)).mpr
      (by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]; exact ⟨hg, h₀, hgP, hgQ, hgω⟩)
  have hx := curveGeom.appTop_adaptedXCoord_of_isPullback hg' h₀'
    (Over.w firstPointHom) (Over.w secondPointHom)
    firstPointHom_left_ne_zero secondPointHom_left_ne_zero hP hQ hP₀ hQ₀ hgP' hgQ'
    curveGeomDifferential
  rw [adaptedXCoord_curveGeom, map_one, hgω'] at hx
  exact hx.symm

section CurveGeom

variable (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
  (hP₂ : P ≫ (E.mulBy 2).left = E.zero) (hQ₂ : Q ≫ (E.mulBy 2).left = E.zero)
  (ω : E.InvariantDifferential) (hω : E.adaptedXCoord hP hQ hP₀ hQ₀ ω = 1)

include hP hQ hP₀ hQ₀ hP₂ hQ₂ hω in
/-- **The universal Legendre normal form read on `curveGeom`.** Under the Legendre conditions on
`(E, P, Q, ω)`, there is a unique pair of a morphism `f : S ⟶ Spec ℤ[1/2][λ, 1/λ(λ - 1)]` and a
morphism `g : E.carrier ⟶ curveGeom.carrier` exhibiting `E` as the pullback of `curveGeom` along
`f`, carrying the zero section to the zero section, `P` to `firstPointHom`, `Q` to `secondPointHom`,
and pulling `curveGeomDifferential` back to `ω`. -/
theorem existsUnique_legendreNormalForm_curveGeom :
    ∃! fg : (S ⟶ Spec (.of (ULift.{u} UniversalLegendre.Ring))) ×
      (E.carrier ⟶ curveGeom.{u}.carrier),
      ∃ (hg : IsPullback fg.2 E.structureMap curveGeom.structureMap fg.1)
        (h₀ : E.zero ≫ fg.2 = fg.1 ≫ curveGeom.zero),
        P ≫ fg.2 = fg.1 ≫ firstPointHom.left ∧ Q ≫ fg.2 = fg.1 ≫ secondPointHom.left ∧
          invariantDifferentialPullback hg h₀ curveGeomDifferential = ω := by
  obtain ⟨⟨f, g⟩, hfg, huniq⟩ := E.existsUnique_legendreNormalForm hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω
  refine ⟨(f, g ≫ (toEllipticCurveGeomIso curveULift).inv),
    (isLegendre_curveGeom_iff E ω).mpr ?_, fun ⟨f', g'⟩ hfg' ↦ ?_⟩
  · rwa [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have := huniq (f', g' ≫ (toEllipticCurveGeomIso curveULift).hom)
    ((isLegendre_curveGeom_iff E ω).mp hfg')
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (by simp [← this.2])

end CurveGeom

end EllipticCurveGeom

namespace UniversalLegendre

open MonoidalCategory

/-! ### Properties of the universal Legendre tuple on `curveGeom` -/

-- The universal tuple `(firstPointHom, secondPointHom, curveGeomDifferential)` on `curveGeom`
-- satisfies the Legendre conditions, as it is classified by
-- `(𝟙 _, (toEllipticCurveGeomIso curveULift).hom)`.
private theorem basisHom_conditions :
    ∃ (hP₀ : ∀ s, firstPointHom.{u}.left s ≠ curveGeom.zero s)
      (hQ₀ : ∀ s, secondPointHom.{u}.left s ≠ curveGeom.zero s),
      firstPointHom.{u}.left ≫ (curveGeom.mulBy 2).left = curveGeom.zero ∧
        secondPointHom.{u}.left ≫ (curveGeom.mulBy 2).left = curveGeom.zero ∧
        (∀ s, secondPointHom.{u}.left s ≠ firstPointHom.left s) ∧
        curveGeom.{u}.adaptedXCoord (Over.w firstPointHom) (Over.w secondPointHom) hP₀ hQ₀
          curveGeomDifferential = 1 :=
  (curveGeom.exists_legendreNormalForm_iff (Over.w firstPointHom) (Over.w secondPointHom)
    curveGeomDifferential).mp
    ⟨𝟙 _, (toEllipticCurveGeomIso curveULift).hom,
      IsPullback.of_horiz_isIso
        ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩,
      by rw [zero_toEllipticCurveGeomIso_hom, Category.id_comp], by simp, by simp,
      (toEllipticCurveGeomDifferential_def curveULift).symm⟩

/-- `firstPointHom` is killed by `2` on `curveGeom`. -/
@[reassoc]
theorem firstPointHom_left_comp_mulBy_two_left :
    firstPointHom.{u}.left ≫ (curveGeom.mulBy 2).left = curveGeom.zero :=
  basisHom_conditions.choose_spec.choose_spec.1

/-- `secondPointHom` is killed by `2` on `curveGeom`. -/
@[reassoc]
theorem secondPointHom_left_comp_mulBy_two_left :
    secondPointHom.{u}.left ≫ (curveGeom.mulBy 2).left = curveGeom.zero :=
  basisHom_conditions.choose_spec.choose_spec.2.1

/-- `secondPointHom` differs from `firstPointHom` at every point of the base. -/
theorem secondPointHom_left_ne_firstPointHom_left (s) :
    secondPointHom.{u}.left s ≠ firstPointHom.{u}.left s :=
  basisHom_conditions.choose_spec.choose_spec.2.2.1 s

end UniversalLegendre

end TauCeti.AlgebraicGeometry
