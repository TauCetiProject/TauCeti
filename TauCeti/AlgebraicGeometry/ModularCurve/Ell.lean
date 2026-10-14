/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# The category `Ell/B` of elliptic curves over `B`-schemes

Let `B` be a scheme. The category `Ell/B` of Katz and Mazur has as objects the pairs `(S, E)` of a
`B`-scheme `S` and an elliptic curve `E` over `S` (`EllipticCurveGeom S`), and as arrows
`(S', E') ⟶ (S, E)` the pairs of a morphism of `B`-schemes `f : S' ⟶ S` and a morphism
`g : E' ⟶ E` carrying the zero section of `E'` to that of `E`, such that the square formed by
`g`, `f` and the two structure morphisms is cartesian. Thus every arrow exhibits its source as a
base change of its target. For a ring `R`, the category `Ell/R` of Katz and Mazur is `Ell/Spec R`.
A moduli problem is a contravariant functor on this category.

The forgetful functor `EllObj.forget B : Ell/B ⥤ Sch/B`, sending `(S, E)` to `S`, makes `Ell/B` a
category fibred in groupoids over `Sch/B`:

* every arrow of `Ell/B` is strongly cartesian (`EllObj.isStronglyCartesian`): an arrow
  `X ⟶ Z` factors through an arrow `Y ⟶ Z` along any compatible morphism of bases, uniquely
  (`EllObj.Hom.lift` and `EllObj.Hom.eq_lift`), because the square of `Y ⟶ Z` is cartesian;
* every morphism `T ⟶ S` of `B`-schemes has a lift with target `(S, E)`, namely the base change of
  `E` to `T` (`EllObj.baseChangeHom`), so `EllObj.forget B` is a fibered category;
* consequently an arrow of `Ell/B` is an isomorphism exactly when its morphism of bases is
  (`EllObj.isIso_iff_isIso_base`), and the fibre of `Ell/B` over a `B`-scheme `S` is the groupoid
  of elliptic curves over `S`.

Base change of a fixed object `X = (S, E)` is functorial in the scheme over `S`
(`EllObj.baseChangeFunctor`), with the canonical morphisms `EllipticCurveGeom.baseChangeMap`
between base changes as the morphisms of total spaces, and with the projections
`EllObj.baseChangeFunctorHom` to `X`. Along an arrow `f : X ⟶ Y` of `Ell/B`, base change of `X` is
base change of `Y` along the composite with `f.base` (`EllObj.baseChangeFunctorIso`); this is what
makes the fibres of moduli problems over `Ell/B` compatible with base change.

An arrow of `Ell/B` is determined by its morphism of total spaces (`EllObj.hom_ext`): the morphism
of bases is recovered through the zero section (`EllObj.Hom.base_eq`). It is automatically
compatible with the group laws (`EllObj.Hom.addition_total` and `EllObj.Hom.neg_total`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllObj B`: the objects of `Ell/B`.
* `TauCeti.AlgebraicGeometry.EllObj.Hom X Y`: the arrows of `Ell/B`, cartesian pointed morphisms
  of elliptic curves over morphisms of `B`-schemes, with the category structure `EllObj.category`.
* `TauCeti.AlgebraicGeometry.EllObj.forget B`: the functor `Ell/B ⥤ Over B` to the base.
* `TauCeti.AlgebraicGeometry.EllObj.baseChange` and
  `TauCeti.AlgebraicGeometry.EllObj.baseChangeHom`: the base change of an object along a morphism
  of `B`-schemes, with its arrow to the object.
* `TauCeti.AlgebraicGeometry.EllObj.baseChangeFunctor X`: base change of an object `X = (S, E)`
  of `Ell/B` as a functor from schemes over `S` to `Ell/B`.
* `TauCeti.AlgebraicGeometry.EllObj.baseChangeFunctorIso f`: for an arrow `f : X ⟶ Y`, the natural
  isomorphism between base change of `X` and base change of `Y` along the composite with `f.base`.

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.isStronglyCartesian`: every arrow of `Ell/B` is strongly
  cartesian over `Sch/B`.
* `TauCeti.AlgebraicGeometry.EllObj.isFibered_forget`: `Ell/B` is a fibered category over `Sch/B`.
* `TauCeti.AlgebraicGeometry.EllObj.isIso_iff_isIso_base`: an arrow of `Ell/B` is an isomorphism
  if and only if its morphism of bases is.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 4.
* The Stacks Project, *Categories*, Section *Fibred categories* (Tag 02XJ) and Section
  *Categories fibred in groupoids* (Tag 003S).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- An **object of `Ell/B`**: a scheme `base` over `B`, through `structureMap`, together with an
elliptic curve `curve` over `base`. For a ring `R`, the objects of the category `Ell/R` of Katz and
Mazur are the objects of `EllObj (Spec R)`. -/
structure EllObj (B : Scheme.{u}) where
  /-- The base scheme `S` of the elliptic curve. -/
  base : Scheme.{u}
  /-- The structure morphism `S ⟶ B` of the base. -/
  structureMap : base ⟶ B
  /-- The elliptic curve over `S`. -/
  curve : EllipticCurveGeom base

namespace EllObj

variable {B : Scheme.{u}}

/-- An **arrow of `Ell/B`** from `X = (S', E')` to `Y = (S, E)`: a morphism of `B`-schemes
`base : S' ⟶ S` and a morphism `total : E' ⟶ E` of total spaces such that the square formed by
`total`, `base` and the two structure morphisms is cartesian, and carrying the zero section of `E'`
to that of `E`. It exhibits `E'` as the base change of `E` along `base`. -/
structure Hom (X Y : EllObj B) where
  /-- The morphism of bases. -/
  base : X.base ⟶ Y.base
  /-- The morphism of bases is a morphism of `B`-schemes. -/
  base_structureMap : base ≫ Y.structureMap = X.structureMap
  /-- The morphism of total spaces. -/
  total : X.curve.carrier ⟶ Y.curve.carrier
  /-- The square formed by `total`, `base` and the structure morphisms is cartesian. -/
  isPullback : IsPullback total X.curve.structureMap Y.curve.structureMap base
  /-- The morphism of total spaces carries the zero section to the zero section. -/
  zero_total : X.curve.zero ≫ total = base ≫ Y.curve.zero

attribute [reassoc (attr := simp)] Hom.base_structureMap Hom.zero_total

namespace Hom

variable {X Y Z : EllObj B}

/-- The morphism of total spaces of an arrow of `Ell/B` lies over its morphism of bases. -/
@[reassoc (attr := simp)]
theorem total_structureMap (f : Hom X Y) :
    f.total ≫ Y.curve.structureMap = X.curve.structureMap ≫ f.base :=
  f.isPullback.w

/-- The morphism of total spaces of an arrow of `Ell/B` carries the addition morphism of its
source to that of its target. -/
@[reassoc]
theorem addition_total (f : Hom X Y) :
    X.curve.addition ≫ f.total = pullback.map _ _ _ _ f.total f.total f.base
      f.isPullback.w.symm f.isPullback.w.symm ≫ Y.curve.addition :=
  EllipticCurveGeom.addition_comp_of_isPullback f.isPullback f.zero_total

/-- The morphism of total spaces of an arrow of `Ell/B` carries the negation morphism of its
source to that of its target. -/
@[reassoc]
theorem neg_total (f : Hom X Y) : X.curve.neg ≫ f.total = f.total ≫ Y.curve.neg :=
  EllipticCurveGeom.neg_comp_of_isPullback f.isPullback f.zero_total

/-- The morphism of bases of an arrow of `Ell/B` is determined by its morphism of total spaces:
it is the composite of the zero section, the morphism of total spaces and the structure
morphism. -/
theorem base_eq (f : Hom X Y) : f.base = X.curve.zero ≫ f.total ≫ Y.curve.structureMap := by
  simp

/-- Two arrows of `Ell/B` with the same morphism of total spaces are equal. -/
private theorem ext_total {f g : Hom X Y} (h : f.total = g.total) : f = g := by
  have hb : f.base = g.base := by rw [f.base_eq, g.base_eq, h]
  cases f
  cases g
  simp_all

end Hom

/-- The category `Ell/B`, whose arrows are the cartesian pointed morphisms `EllObj.Hom`. The
composite of two arrows pastes their cartesian squares. -/
instance category : Category.{u} (EllObj B) where
  Hom := Hom
  id X :=
    { base := 𝟙 X.base
      base_structureMap := Category.id_comp _
      total := 𝟙 X.curve.carrier
      isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
      zero_total := by simp }
  comp f g :=
    { base := f.base ≫ g.base
      base_structureMap := by simp
      total := f.total ≫ g.total
      isPullback := f.isPullback.paste_horiz g.isPullback
      zero_total := by simp }
  -- the private `Hom.ext_total` is only visible from tactic proofs here
  id_comp f := by exact Hom.ext_total (Category.id_comp f.total)
  comp_id f := by exact Hom.ext_total (Category.comp_id f.total)
  assoc f g h := by exact Hom.ext_total (Category.assoc f.total g.total h.total)

variable {X Y Z : EllObj B}

/-- **Extensionality for arrows of `Ell/B`**: two arrows with the same morphism of total spaces
are equal. -/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.total = g.total) : f = g :=
  Hom.ext_total h

@[simp]
theorem id_base (X : EllObj B) : Hom.base (𝟙 X) = 𝟙 X.base :=
  (rfl)

@[simp]
theorem id_total (X : EllObj B) : Hom.total (𝟙 X) = 𝟙 X.curve.carrier :=
  (rfl)

@[simp]
theorem comp_base (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  (rfl)

@[simp]
theorem comp_total (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).total = f.total ≫ g.total :=
  (rfl)

/-! ### The cartesian factorisation -/

namespace Hom

/-- **The cartesian factorisation in `Ell/B`.** Given arrows `g : Y ⟶ Z` and `f : X ⟶ Z` and a
morphism of bases `h : X.base ⟶ Y.base` with `h ≫ g.base = f.base`, this is the arrow `X ⟶ Y`
over `h` whose composite with `g` is `f` (`Hom.lift_comp`). It is unique (`Hom.eq_lift`). Its
morphism of total spaces is `EllipticCurveGeom.baseChangeLift`, induced by the cartesian square
of `g`. -/
noncomputable def lift (g : Y ⟶ Z) (f : X ⟶ Z) (h : X.base ⟶ Y.base) (hh : h ≫ g.base = f.base) :
    X ⟶ Y where
  base := h
  base_structureMap := by rw [← g.base_structureMap, reassoc_of% hh, f.base_structureMap]
  total := EllipticCurveGeom.baseChangeLift g.isPullback f.isPullback.toCommSq hh
  isPullback := EllipticCurveGeom.isPullback_baseChangeLift g.isPullback f.isPullback hh
  zero_total := EllipticCurveGeom.zero_baseChangeLift g.isPullback f.isPullback.toCommSq hh
    g.zero_total f.zero_total

variable (g : Y ⟶ Z) (f : X ⟶ Z) (h : X.base ⟶ Y.base) (hh : h ≫ g.base = f.base)

@[simp]
theorem lift_base : (lift g f h hh).base = h :=
  (rfl)

@[reassoc (attr := simp)]
theorem lift_total_total : (lift g f h hh).total ≫ g.total = f.total :=
  EllipticCurveGeom.baseChangeLift_fst _ _ _

/-- The cartesian factorisation `Hom.lift g f h hh` composed with `g` is `f`. -/
@[reassoc (attr := simp)]
theorem lift_comp : lift g f h hh ≫ g = f :=
  hom_ext (lift_total_total g f h hh)

/-- **Uniqueness of the cartesian factorisation.** An arrow `k : X ⟶ Y` over `h` whose composite
with `g` is `f` is the cartesian factorisation `Hom.lift g f h hh`. -/
theorem eq_lift (k : X ⟶ Y) (hk : k ≫ g = f) (hkb : k.base = h) : k = lift g f h hh := by
  subst hk hkb
  ext
  exact g.isPullback.hom_ext (by simp) (by simp)

end Hom

/-! ### The forgetful functor to the base -/

variable (B) in
/-- The **forgetful functor** `Ell/B ⥤ Sch/B`, sending an elliptic curve `E` over a `B`-scheme `S`
to `S`, and an arrow of `Ell/B` to its morphism of bases. -/
@[expose, simps]
def forget : EllObj B ⥤ Over B where
  obj X := Over.mk X.structureMap
  map f := Over.homMk f.base f.base_structureMap

/-- An arrow of `Ell/B` lies over every morphism of `B`-schemes with the same underlying morphism
of schemes as its morphism of bases. -/
theorem isHomLift_of_base_eq {f : X ⟶ Y} {g : (forget B).obj X ⟶ (forget B).obj Y}
    (h : f.base = g.left) : (forget B).IsHomLift g f := by
  obtain rfl : (forget B).map f = g := Over.OverMorphism.ext h
  infer_instance

/-- **Every arrow of `Ell/B` is strongly cartesian** over `Sch/B`: the cartesian factorisation
`Hom.lift` is the unique lift of a morphism of bases. -/
instance isStronglyCartesian {R S : Over B} (g : R ⟶ S) (f : X ⟶ Y) [(forget B).IsHomLift g f] :
    (forget B).IsStronglyCartesian g f := by
  subst_hom_lift (forget B) g f
  refine { universal_property' := fun {X'} k φ _ ↦ ?_ }
  have hb : k.left ≫ f.base = φ.base :=
    congr_arg CommaMorphism.left (IsHomLift.eq_of_isHomLift (forget B) (k ≫ (forget B).map f) φ)
  refine ⟨Hom.lift f φ k.left hb,
    ⟨isHomLift_of_base_eq (Hom.lift_base _ _ _ _), Hom.lift_comp _ _ _ _⟩, ?_⟩
  rintro χ ⟨hχ, hχf⟩
  exact Hom.eq_lift _ _ _ _ χ hχf
    (congr_arg CommaMorphism.left (IsHomLift.eq_of_isHomLift (forget B) k χ)).symm

/-- Two arrows `X ⟶ Y` of `Ell/B` with the same morphism of bases and the same composite with an
arrow `g : Y ⟶ Z` are equal, since `g` is strongly cartesian. -/
theorem hom_ext_of_comp (g : Y ⟶ Z) {k k' : X ⟶ Y} (hk : k ≫ g = k' ≫ g)
    (hb : k.base = k'.base) : k = k' :=
  have := isHomLift_of_base_eq (f := k) (g := (forget B).map k) rfl
  have := isHomLift_of_base_eq (f := k') (g := (forget B).map k) hb.symm
  Functor.IsStronglyCartesian.ext (forget B) ((forget B).map g) g ((forget B).map k) hk

/-! ### Base change -/

/-- The **base change** of an object `X = (S, E)` of `Ell/B` along a morphism `g : T ⟶ S` of
`B`-schemes: the elliptic curve `E.baseChange g.left` over `T`. -/
@[expose, simps]
noncomputable def baseChange (X : EllObj B) {T : Over B} (g : T ⟶ (forget B).obj X) : EllObj B where
  base := T.left
  structureMap := T.hom
  curve := X.curve.baseChange g.left

/-- The arrow of `Ell/B` from the base change of `X` along `g` to `X`, lying over `g`. Its
morphism of total spaces is the first projection of the fibre product. -/
noncomputable def baseChangeHom (X : EllObj B) {T : Over B} (g : T ⟶ (forget B).obj X) :
    X.baseChange g ⟶ X where
  base := g.left
  base_structureMap := Over.w g
  total := (X.curve.baseChangeIso g.left).hom ≫ pullback.fst _ _
  isPullback := X.curve.isPullback_baseChange g.left
  zero_total := (X.curve.zero_baseChangeIso_hom_assoc g.left _).trans (pullbackSection_fst _ _ _ _)

variable (X : EllObj B) {T : Over B} (g : T ⟶ (forget B).obj X)

@[simp]
theorem baseChangeHom_base : (X.baseChangeHom g).base = g.left :=
  (rfl)

@[simp]
theorem baseChangeHom_total :
    (X.baseChangeHom g).total = (X.curve.baseChangeIso g.left).hom ≫ pullback.fst _ _ :=
  (rfl)

/-- The arrow `baseChangeHom X g` lies over `g`. -/
instance isHomLift_baseChangeHom : (forget B).IsHomLift g (X.baseChangeHom g) :=
  isHomLift_of_base_eq (baseChangeHom_base X g)

/-- **`Ell/B` is fibred over `Sch/B`**: every morphism of `B`-schemes `T ⟶ S` lifts to an arrow of
`Ell/B` with target any given elliptic curve over `S`, namely the base change. Since every arrow
of `Ell/B` is cartesian, `Ell/B` is a category fibred in groupoids. -/
instance isFibered_forget : (forget B).IsFibered :=
  .of_exists_isStronglyCartesian fun X _ g ↦
    ⟨X.baseChange g, X.baseChangeHom g, inferInstance⟩

/-- The **base-change functor** of an object `X = (S, E)` of `Ell/B`: it sends a scheme `T` over
`S`, through `t : T ⟶ S`, to the elliptic curve `E.baseChange t` over the `B`-scheme `T`, and a
morphism `k : T' ⟶ T` of schemes over `S` to the arrow of `Ell/B` over `k` whose morphism of total
spaces is the canonical morphism `E.baseChangeMap k` between the base changes. -/
@[expose, simps obj_base obj_structureMap obj_curve map_base map_total]
noncomputable def baseChangeFunctor (X : EllObj B) : Over X.base ⥤ EllObj B where
  obj T := ⟨T.left, T.hom ≫ X.structureMap, X.curve.baseChange T.hom⟩
  map {T' T} k :=
    { base := k.left
      base_structureMap := by simp
      total := X.curve.baseChangeMap k.left (Over.w k)
      isPullback := .of_right (by simpa using X.curve.isPullback_baseChange T'.hom) (by simp)
        (X.curve.isPullback_baseChange T.hom)
      zero_total := X.curve.zero_baseChangeMap _ _ }
  map_id T := hom_ext (by simp)
  map_comp k l := hom_ext (by simp)

/-- **An arrow of `Ell/B` is an isomorphism if and only if its morphism of bases is.** In
particular, every arrow of `Ell/B` lying over the identity of its base is an isomorphism, so the
fibres of `Ell/B` are groupoids. -/
theorem isIso_iff_isIso_base (f : X ⟶ Y) : IsIso f ↔ IsIso f.base := by
  constructor
  -- `(Over.forget B).map ((forget B).map f)` is `f.base` by `Over.homMk_left`
  · intro
    exact Functor.map_isIso (Over.forget B) ((forget B).map f)
  · intro h
    have : IsIso ((Over.forget B).map ((forget B).map f)) := h
    have : IsIso ((forget B).map f) := isIso_of_reflects_iso _ (Over.forget B)
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (forget B) ((forget B).map f) f

/-! ### Base change along an arrow of `Ell/B` -/

/-- The arrow of `Ell/B` from the base change `X.baseChangeFunctor.obj T` of `X = (S, E)` along
`T ⟶ S` to `X`, lying over the structure morphism of `T`: the arrow `baseChangeHom` along `T ⟶ S`,
whose source is `X.baseChangeFunctor.obj T` by definition. Its morphism of total spaces is the
first projection of the fibre product. -/
noncomputable def baseChangeFunctorHom (X : EllObj B) (T : Over X.base) :
    X.baseChangeFunctor.obj T ⟶ X :=
  X.baseChangeHom (T := Over.mk (T.hom ≫ X.structureMap)) (Over.homMk T.hom)

@[simp]
theorem baseChangeFunctorHom_base {X : EllObj B} (T : Over X.base) :
    (X.baseChangeFunctorHom T).base = T.hom :=
  (rfl)

@[simp]
theorem baseChangeFunctorHom_total {X : EllObj B} (T : Over X.base) :
    (X.baseChangeFunctorHom T).total = (X.curve.baseChangeIso T.hom).hom ≫ pullback.fst _ _ :=
  (rfl)

/-- The arrows `baseChangeFunctorHom` are natural in the scheme over the base of `X`. -/
@[reassoc (attr := simp)]
theorem baseChangeFunctor_map_baseChangeFunctorHom {X : EllObj B} {T' T : Over X.base}
    (k : T' ⟶ T) :
    X.baseChangeFunctor.map k ≫ X.baseChangeFunctorHom T = X.baseChangeFunctorHom T' := by
  ext
  -- the objects of these composites are only definitionally those of the two lemmas below, so
  -- `simp` cannot rewrite with them
  exact (X.curve.baseChangeMap_baseChangeIso_hom_assoc k.left (Over.w k) _).trans
    (congrArg ((X.curve.baseChangeIso T'.hom).hom ≫ ·) (pullback.mapSnd_fst _ _ _ _ _))

/-- The component at `T` of `baseChangeFunctorIso f`: the cartesian factorisation of
`X.baseChangeFunctorHom T ≫ f` through `Y.baseChangeFunctorHom`, over the identity of `T`. -/
private noncomputable def baseChangeFunctorIsoApp {X Y : EllObj B} (f : X ⟶ Y) (T : Over X.base) :
    X.baseChangeFunctor.obj T ⟶ Y.baseChangeFunctor.obj ((Over.map f.base).obj T) :=
  Hom.lift (Y.baseChangeFunctorHom ((Over.map f.base).obj T)) (X.baseChangeFunctorHom T ≫ f)
    (𝟙 T.left) (Category.id_comp _)

@[reassoc (attr := simp)]
private theorem baseChangeFunctorIsoApp_comp {X Y : EllObj B} (f : X ⟶ Y) (T : Over X.base) :
    baseChangeFunctorIsoApp f T ≫ Y.baseChangeFunctorHom ((Over.map f.base).obj T) =
      X.baseChangeFunctorHom T ≫ f :=
  Hom.lift_comp _ _ _ _

private theorem baseChangeFunctorIsoApp_naturality {X Y : EllObj B} (f : X ⟶ Y)
    {T' T : Over X.base} (k : T' ⟶ T) :
    X.baseChangeFunctor.map k ≫ baseChangeFunctorIsoApp f T =
      baseChangeFunctorIsoApp f T' ≫ Y.baseChangeFunctor.map ((Over.map f.base).map k) :=
  -- the two morphisms of bases are `k.left ≫ 𝟙 T.left` and `𝟙 T'.left ≫ k.left` only after
  -- unfolding `baseChangeFunctor`, so they are compared by a term rather than by `simp`
  hom_ext_of_comp (Y.baseChangeFunctorHom _) (by simp)
    ((Category.comp_id k.left).trans (Category.id_comp _).symm)

/-- **Base change along an arrow of `Ell/B`.** For an arrow `f : X ⟶ Y` of `Ell/B`, the base
change of `X` along a scheme `T` over `X.base` is identified with the base change of `Y` along
the composite `T ⟶ X.base ⟶ Y.base`, naturally in `T`. The component at `T` lies over the identity
of `T` (`baseChangeFunctorIso_hom_app_base`) and is the cartesian factorisation of
`X.baseChangeFunctorHom T ≫ f` through `Y.baseChangeFunctorHom`
(`baseChangeFunctorIso_hom_app_comp`). -/
noncomputable def baseChangeFunctorIso {X Y : EllObj B} (f : X ⟶ Y) :
    X.baseChangeFunctor ≅ Over.map f.base ⋙ Y.baseChangeFunctor :=
  NatIso.ofComponents
    (fun T ↦
      have : IsIso (baseChangeFunctorIsoApp f T) :=
        (isIso_iff_isIso_base _ _).2 (inferInstanceAs (IsIso (𝟙 T.left)))
      asIso (baseChangeFunctorIsoApp f T))
    (baseChangeFunctorIsoApp_naturality f)

@[simp]
theorem baseChangeFunctorIso_hom_app_base {X Y : EllObj B} (f : X ⟶ Y) (T : Over X.base) :
    ((baseChangeFunctorIso f).hom.app T).base = 𝟙 T.left :=
  (rfl)

@[reassoc (attr := simp)]
theorem baseChangeFunctorIso_hom_app_comp {X Y : EllObj B} (f : X ⟶ Y) (T : Over X.base) :
    (baseChangeFunctorIso f).hom.app T ≫ Y.baseChangeFunctorHom ((Over.map f.base).obj T) =
      X.baseChangeFunctorHom T ≫ f :=
  baseChangeFunctorIsoApp_comp f T

end EllObj

end TauCeti.AlgebraicGeometry
