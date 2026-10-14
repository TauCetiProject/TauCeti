/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Base change of points of an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `E'` an elliptic curve over a scheme `S'`, and
let `g : E' ⟶ E` be a morphism lying over `f : S' ⟶ S` such that the square formed by `g`, `f` and
the two structure morphisms is a pullback square, and carrying the zero section of `E'` to that of
`E`. Every `S`-point `P` of `E` then has a base change `P'`, the unique `S'`-point of `E'` with
`P' ≫ g = f ≫ P`. This file shows that base change of points is a homomorphism for the group laws
on points (`EllipticCurveGeom.pointsPullback`), that it is functorial in the pullback square, and
that it is compatible with the ideal sheaves of sections: the divisor `[P']` on `E'` is the inverse
image of the divisor `[P]` on `E` (`EllipticCurveGeom.ker_pointsPullback_left`), and the inverse
image of a closed subgroup scheme of `E` is a closed subgroup scheme of `E'`
(`EllipticCurveGeom.exists_grpObj_isMonHom_comap`). This is what makes level structures defined
through divisors of points, such as points of exact order `N`, pull back along base change.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsPullback hg h0`: base change of `S`-points of
  `E` to `S'`-points of `E'`, as a group homomorphism.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.universalPoint E`: the diagonal section of
  `E ×_S E`, as a point of the base change of `E` to `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.toBaseChangeSelf hg P'`: the morphism from `E'` to
  the base change of `E` to `E`, lying over the morphism `S' ⟶ E` given by an `S'`-point `P'`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.mul_left_comp_of_isPullback`: `g` carries the sum
  of two points of `E'`, with values in any scheme over `S'`, to the sum of their images in `E`;
  `mul_left_comp_eq_of_isPullback` states this with the group law on points of `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsPullback_left_comp`: the base change `P'` of
  `P` satisfies `P' ≫ g = f ≫ P`, and `eq_pointsPullback_iff` characterises it by this property.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsPullback_id` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsPullback_comp`: base change of points along
  the identity square is the identity, and along a pasted square it is the composite.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsPullback_universalPoint`: every point of
  every base change of `E` is the base change of the universal point, along the pullback square
  `isPullback_toBaseChangeSelf`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pointsPullback_left_apply_eq_zero_iff`: the base
  change `P'` of `P` meets the zero section at a point `s'` of `S'` exactly when `P` meets the
  zero section at `f s'`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.ker_pointsPullback_left`: the ideal sheaf of `P'`
  is the inverse image of the ideal sheaf of `P` along `g`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_comap`: the inverse image of
  a closed subgroup scheme of `E` along `g` is a closed subgroup scheme of `E'`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1 and Chapter 4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- An `S`-point of an elliptic curve over `S` is a section of its structure morphism. -/
@[reassoc (attr := simp)]
theorem left_comp_structureMap {T : Scheme.{u}} {C : EllipticCurveGeom T}
    (P : 𝟙_ (Over T) ⟶ Over.mk C.structureMap) : P.left ≫ C.structureMap = 𝟙 T := by
  simpa using Over.w P

-- The base change of an `S`-point of `E`, before it is bundled into a group homomorphism.
private noncomputable def pointPullback (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    𝟙_ (Over S') ⟶ Over.mk E'.structureMap :=
  Over.homMk (hg.lift (f ≫ P.left) (𝟙 S') (by simp)) (by simp)

@[reassoc]
private theorem pointPullback_left_comp (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    (pointPullback hg P).left ≫ g = f ≫ P.left :=
  hg.lift_fst _ _ _

include hg in
/-- An `S'`-point of `E'` is determined by its composite with `g`. -/
private theorem point_ext {P Q : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap}
    (h : P.left ≫ g = Q.left ≫ g) : P = Q := by
  ext1
  exact hg.hom_ext h (by simp)

include hg h0 in
/-- **Base change carries sums of points to sums of points.** For points `x` and `y` of `E'` with
values in a scheme `Z` over `S'`, the composite of their sum with `g` is the sum, under the
addition morphism of `E`, of the composites of `x` and `y` with `g`. -/
theorem mul_left_comp_of_isPullback {Z : Over S'} (x y : Z ⟶ Over.mk E'.structureMap) :
    (x * y).left ≫ g = pullback.lift (x.left ≫ g) (y.left ≫ g)
      (by have hx := Over.w x; have hy := Over.w y; dsimp at hx hy
          simp [hg.w, reassoc_of% hx, reassoc_of% hy]) ≫ E.addition := by
  rw [hom_mul_left, Category.assoc, addition_comp_of_isPullback hg h0, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

include hg h0 in
/-- **Base change carries sums of points to sums of points**, in terms of the group law on points
of `E`. If points `x` and `y` of `E'` with values in a scheme `Z` over `S'` lie over points `x₀`
and `y₀` of `E` with values in `Z`, viewed as a scheme over `S`, then the sum of `x` and `y` lies
over the sum of `x₀` and `y₀`. -/
theorem mul_left_comp_eq_of_isPullback {Z : Over S'} {x y : Z ⟶ Over.mk E'.structureMap}
    {x₀ y₀ : Over.mk (Z.hom ≫ f) ⟶ Over.mk E.structureMap} (hx : x.left ≫ g = x₀.left)
    (hy : y.left ≫ g = y₀.left) : (x * y).left ≫ g = (x₀ * y₀).left := by
  rw [mul_left_comp_of_isPullback hg h0, hom_mul_left]
  congr 1
  apply pullback.hom_ext <;> simp [hx, hy]

/-- **Base change of points of an elliptic curve.** For a morphism `g : E' ⟶ E` of elliptic curves
lying over `f : S' ⟶ S`, forming a pullback square with the structure morphisms and carrying the
zero section of `E'` to that of `E`, the base change of an `S`-point `P` of `E` is the unique
`S'`-point `P'` of `E'` with `P' ≫ g = f ≫ P` (`eq_pointsPullback_iff`). Base change of points is
a homomorphism for the group laws on points. -/
noncomputable def pointsPullback :
    (𝟙_ (Over S) ⟶ Over.mk E.structureMap) →* (𝟙_ (Over S') ⟶ Over.mk E'.structureMap) where
  toFun := pointPullback hg
  map_one' := point_ext hg <| by
    simp [pointPullback_left_comp, h0]
  map_mul' P Q := point_ext hg <| by
    rw [mul_left_comp_of_isPullback hg h0, pointPullback_left_comp, hom_mul_left, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [pointPullback_left_comp]

/-- The base change `P'` of a point `P` satisfies `P' ≫ g = f ≫ P`. -/
@[reassoc (attr := simp)]
theorem pointsPullback_left_comp (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    (pointsPullback hg h0 P).left ≫ g = f ≫ P.left :=
  pointPullback_left_comp hg P

/-- **The characterising property of the base change of a point**: an `S'`-point `Q` of `E'` is
the base change of the `S`-point `P` of `E` exactly when `Q ≫ g = f ≫ P`. -/
theorem eq_pointsPullback_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {Q : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap} :
    Q = pointsPullback hg h0 P ↔ Q.left ≫ g = f ≫ P.left :=
  ⟨fun h ↦ h ▸ pointsPullback_left_comp hg h0 P,
    fun h ↦ point_ext hg (h.trans (pointsPullback_left_comp hg h0 P).symm)⟩

/-- **Base change of points along the identity square** is the identity. -/
@[simp]
theorem pointsPullback_id (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    pointsPullback (.id_horiz E.structureMap) (by simp) P = P :=
  ((eq_pointsPullback_iff _ _).mpr (by simp)).symm

/-- **Base change of points is functorial**: base change of points along a pasted pullback square
is the composite of the base changes along the two squares. -/
theorem pointsPullback_comp {S'' : Scheme.{u}} {E'' : EllipticCurveGeom S''}
    {g' : E''.carrier ⟶ E'.carrier} {f' : S'' ⟶ S'}
    (hg' : IsPullback g' E''.structureMap E'.structureMap f') (h0' : E''.zero ≫ g' = f' ≫ E'.zero)
    (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    pointsPullback (hg'.paste_horiz hg) (by simp [reassoc_of% h0', h0]) P =
      pointsPullback hg' h0' (pointsPullback hg h0 P) :=
  ((eq_pointsPullback_iff _ _).mpr (by simp)).symm

variable (E) in
/-- The **universal point** of `E`: the diagonal section of `E ×_S E`, viewed as a point of the
base change of `E` to `E` itself. Every point of every base change of `E` is a base change of it,
along the morphism to `E` that the point defines (`pointsPullback_universalPoint`). -/
noncomputable def universalPoint :
    𝟙_ (Over E.carrier) ⟶ Over.mk (E.baseChange E.structureMap).structureMap :=
  Over.homMk ((E.isPullback_baseChange E.structureMap).lift (𝟙 _) (𝟙 _) (by simp)) (by simp)

/-- The universal point composed with the projection to `E` is the identity. -/
@[reassoc (attr := simp)]
theorem universalPoint_left_baseChangeIso_hom_fst :
    (E.universalPoint).left ≫ (E.baseChangeIso E.structureMap).hom ≫
      pullback.fst E.structureMap E.structureMap = 𝟙 E.carrier :=
  (E.isPullback_baseChange E.structureMap).lift_fst _ _ _

/-- The morphism from a base change `E'` of `E` to the base change of `E` to `E` itself, lying over
the morphism `S' ⟶ E` given by an `S'`-point `P'` of `E'`. -/
noncomputable def toBaseChangeSelf (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    E'.carrier ⟶ (E.baseChange E.structureMap).carrier :=
  (E.isPullback_baseChange E.structureMap).lift g (E'.structureMap ≫ P'.left ≫ g)
    (by simp [hg.w])

/-- `toBaseChangeSelf` composed with the projection to `E` is `g`. -/
theorem toBaseChangeSelf_fst (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    toBaseChangeSelf hg P' ≫ (E.baseChangeIso E.structureMap).hom ≫
      pullback.fst E.structureMap E.structureMap = g :=
  (E.isPullback_baseChange E.structureMap).lift_fst _ _ _

/-- `toBaseChangeSelf` lies over the morphism `S' ⟶ E` given by the point `P'`. -/
theorem toBaseChangeSelf_structureMap (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    toBaseChangeSelf hg P' ≫ (E.baseChange E.structureMap).structureMap =
      E'.structureMap ≫ P'.left ≫ g :=
  (E.isPullback_baseChange E.structureMap).lift_snd _ _ _

/-- `E'` is the base change of the base change of `E` to `E` along the morphism `S' ⟶ E` given by
an `S'`-point `P'` of `E'`, via `toBaseChangeSelf`. -/
theorem isPullback_toBaseChangeSelf (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    IsPullback (toBaseChangeSelf hg P') E'.structureMap (E.baseChange E.structureMap).structureMap
      (P'.left ≫ g) := by
  -- paste with the pullback square of `E ×_S E ⟶ E` over `E ⟶ S` to recover `hg`
  refine .of_right (h₁₂ := (E.baseChangeIso E.structureMap).hom ≫ pullback.fst _ _) ?_
    (toBaseChangeSelf_structureMap hg P') (E.isPullback_baseChange E.structureMap)
  have hw : (P'.left ≫ g) ≫ E.structureMap = f := by simp [hg.w]
  rwa [toBaseChangeSelf_fst, hw]

include h0 in
/-- `toBaseChangeSelf` carries the zero section of `E'` to that of the base change of `E` to `E`. -/
theorem zero_toBaseChangeSelf (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    E'.zero ≫ toBaseChangeSelf hg P' = (P'.left ≫ g) ≫ (E.baseChange E.structureMap).zero := by
  apply (E.isPullback_baseChange E.structureMap).hom_ext
  · rw [Category.assoc, toBaseChangeSelf_fst, h0]
    simp [reassoc_of% hg.w, pullbackSection_fst]
  · simp [toBaseChangeSelf_structureMap]

include h0 in
/-- **Every point of a base change of `E` is a base change of the universal point**, along the
morphism `S' ⟶ E` it defines. -/
theorem pointsPullback_universalPoint (P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap) :
    pointsPullback (isPullback_toBaseChangeSelf hg P') (zero_toBaseChangeSelf hg h0 P')
      E.universalPoint = P' := by
  refine ((eq_pointsPullback_iff _ _).mpr ?_).symm
  apply (E.isPullback_baseChange E.structureMap).hom_ext
  · simp [toBaseChangeSelf_fst]
  · simp [toBaseChangeSelf_structureMap, universalPoint]

/-- Along a morphism `t : T ⟶ S'`, the base change `P'` of an `S`-point `P` of `E` agrees with the
zero section of `E'` exactly when `P` agrees with the zero section of `E` along `t ≫ f`. -/
theorem comp_pointsPullback_left_eq_comp_zero_iff (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)
    {T : Scheme.{u}} (t : T ⟶ S') :
    t ≫ (pointsPullback hg h0 P).left = t ≫ E'.zero ↔ (t ≫ f) ≫ P.left = (t ≫ f) ≫ E.zero :=
  ⟨fun h ↦ by simpa [h0] using congr($h ≫ g),
    fun h ↦ hg.hom_ext (by simpa [h0] using h) (by simp)⟩

/-- **A base-changed point meets the zero section exactly over the points where the original
point does.** For a pullback square of elliptic curves over `f : S' ⟶ S` and an `S`-point `P` of
`E`, the base change `P'` of `P` agrees with the zero section of `E'` at a point `s'` of `S'` if and
only if `P` agrees with the zero section of `E` at `f s'`. -/
theorem pointsPullback_left_apply_eq_zero_iff (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)
    (s' : S') :
    (pointsPullback hg h0 P).left s' = E'.zero s' ↔ P.left (f s') = E.zero (f s') := by
  -- both sides are read at the point `t : Spec κ(s') ⟶ S'`, where they become equalities of
  -- morphisms; they are chained with `Iff.trans` since the point `p` of `Spec κ(s')` is typed in
  -- `Spec (.of _)` by `comp_eq_comp_iff_of_section`, which blocks `rw`
  obtain ⟨p⟩ : Nonempty (Spec (S'.residueField s')) := inferInstance
  have key {T : Scheme.{u}} {X : Scheme.{u}} (a b : T ⟶ X) (z y : T) (hz : z = y) :
      a z = b z ↔ a y = b y := by
    rw [hz]
  refine (key _ _ _ _ (Scheme.fromSpecResidueField_apply s' p)).symm.trans
    ((comp_eq_comp_iff_of_section (left_comp_structureMap _) E'.zero_comp_structureMap
      (S'.fromSpecResidueField s') p).symm.trans
        ((comp_pointsPullback_left_eq_comp_zero_iff hg h0 P _).trans ((comp_eq_comp_iff_of_section
          (left_comp_structureMap P) E.zero_comp_structureMap (S'.fromSpecResidueField s' ≫ f)
            p).trans (key _ _ _ _ (congrArg f (Scheme.fromSpecResidueField_apply s' p))))))

/-- **The divisor of a base-changed point.** The ideal sheaf of the base change `P'` of an
`S`-point `P` of `E`, which cuts out the divisor `[P']` on `E'`, is the inverse image along `g` of
the ideal sheaf of `P`. -/
theorem ker_pointsPullback_left (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    (pointsPullback hg h0 P).left.ker = P.left.ker.comap g := by
  have := P.left.isClosedImmersion_of_comp_eq_id (f := E.structureMap) (left_comp_structureMap P)
  refine Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := f) _ ?_
  -- The square `P' ≫ g = f ≫ P` is the left half of a pasted square whose outer rectangle, the
  -- composite of `P'` and `P` with the structure morphisms, is the identity square over `f`.
  refine IsPullback.of_right ?_ (pointsPullback_left_comp hg h0 P) hg.flip
  rw [left_comp_structureMap, left_comp_structureMap]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

include hg h0 in
/-- **Closed subgroup schemes are stable under base change.** Let `g : E' ⟶ E` be a morphism of
elliptic curves lying over `f : S' ⟶ S`, forming a pullback square with the structure morphisms and
carrying the zero section of `E'` to that of `E`. If the closed subscheme of `E` cut out by an
ideal sheaf `D` is a subgroup scheme, then so is the closed subscheme of `E'` cut out by the
inverse image of `D` along `g`. -/
theorem exists_grpObj_isMonHom_comap (D : E.carrier.IdealSheafData)
    (hD : ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E.structureMap)),
      IsMonHom (Over.homMk D.subschemeι :
        Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap)) :
    ∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap) := by
  let i : Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap :=
    Over.homMk D.subschemeι
  let i' : Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap :=
    Over.homMk (D.comap g).subschemeι
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion D.subschemeι)
  have : IsClosedImmersion i'.left := inferInstanceAs (IsClosedImmersion (D.comap g).subschemeι)
  have hi : i.left.ker = D := Scheme.IdealSheafData.ker_subschemeι _
  have hi' : i'.left.ker = D.comap g := Scheme.IdealSheafData.ker_subschemeι _
  rw [GroupScheme.exists_grpObj_isMonHom_iff_ker_le i, hi] at hD
  rw [GroupScheme.exists_grpObj_isMonHom_iff_ker_le i', hi']
  obtain ⟨he, hm, hj⟩ := hD
  -- The morphism `ρ` from the closed subscheme of `D.comap g` to that of `D` induced by `g`.
  let ρ := Scheme.IdealSheafData.subschemeMap (D.comap g) D g (D.le_map_comap g)
  have hρ : ρ ≫ D.subschemeι = (D.comap g).subschemeι ≫ g :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  -- `D.comap g` lies in the ideal sheaf of a morphism `h` exactly when `D` lies in that of `h ≫ g`.
  simp only [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker]
  refine ⟨?_, ?_, ?_⟩
  · rw [one_left, h0]
    exact he.trans (Scheme.Hom.le_ker_comp _ _)
  · -- The two points `fst ≫ i'` and `snd ≫ i'` of `E'` with values in `D' ×_{S'} D'`, composed
    -- with `g`, factor through `ρ` as points `σ₁` and `σ₂` of `D` over `S`.
    let A := Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)
    let Z := Over.mk ((A ⊗ A).hom ≫ f)
    have hw (p : A ⊗ A ⟶ A) : (p.left ≫ ρ) ≫ D.subschemeι ≫ E.structureMap = Z.hom := by
      have := Over.w p
      dsimp [A, Z] at this ⊢
      simp only [Category.assoc, reassoc_of% hρ, hg.w, reassoc_of% this]
    let σ₁ : Z ⟶ Over.mk (D.subschemeι ≫ E.structureMap) :=
      Over.homMk ((fst A A).left ≫ ρ) (hw _)
    let σ₂ : Z ⟶ Over.mk (D.subschemeι ≫ E.structureMap) :=
      Over.homMk ((snd A A).left ≫ ρ) (hw _)
    have key : ((i' ⊗ₘ i') ≫ μ[Over.mk E'.structureMap]).left ≫ g =
        (lift σ₁ σ₂).left ≫ ((i ⊗ₘ i) ≫ μ[Over.mk E.structureMap]).left := by
      -- Both sides are composites of tensor products with `μ`, i.e. products of points.
      simp only [← Over.comp_left, mul_eq_mul, comp_mul, tensorHom_fst, tensorHom_snd]
      exact mul_left_comp_eq_of_isPullback hg h0 (by simp [σ₁, i, i', A, ← hρ])
        (by simp [σ₂, i, i', A, ← hρ])
    rw [key]
    exact hm.trans (Scheme.Hom.le_ker_comp _ _)
  · have key : (i' ≫ ι[Over.mk E'.structureMap]).left ≫ g =
        ρ ≫ (i ≫ ι[Over.mk E.structureMap]).left := by
      simp [i, i', neg_comp_of_isPullback hg h0, reassoc_of% hρ]
    rw [key]
    exact hj.trans (Scheme.Hom.le_ker_comp _ _)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
