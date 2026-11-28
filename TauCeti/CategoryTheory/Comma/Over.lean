/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi

/-!
# Isomorphisms and base change of objects over a base

An isomorphism in `Over X` is an isomorphism of the underlying objects. Mathlib records this
for comma categories (`CategoryTheory.Comma.instIsIsoLeft`) and for arrow categories
(`CategoryTheory.Arrow.isIso_left`), but `Over X` is a `def` rather than an abbreviation for
a comma category, so instance search does not see through it to the comma statement. This file
supplies the missing `Over` form, which lets `infer_instance` discharge `IsIso φ.left` goals
that otherwise have to name the forgetful functor by hand.

Base change `Over.pullback f` along `f : T ⟶ S` sends a morphism `g : A ⟶ B` over `S` to the
induced morphism `A ×_S T ⟶ B ×_S T`, which is the pullback of `g` along the projection
`B ×_S T ⟶ B`. For `f : X ⟶ S` and `g : S' ⟶ S`, the two base changes of `X` to an object
`T` over `S'` agree, `T ×_{S'} (S' ×_S X) ≅ T ×_S X` (`pullbackRightPullbackFstIso`), naturally in
`T`.

Factorization through a monomorphism can be checked after base change whenever the projection
to the source is a strong epimorphism. This uses Mathlib's `StrongEpi.llp` and `CommSq.lift`.

## Main declarations

* `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is
  an isomorphism.
* `CategoryTheory.Over.mapMkIso`: an object `Z` over `S` is the image under `Over.map p` of
  `Over.mk a`, for a lift `a` of its structure morphism through `p : S' ⟶ S`.
* `CategoryTheory.Over.isPullback_pullback_map_left`: base change of a morphism over `S` is a
  pullback of it.
* `CategoryTheory.Over.exists_comp_pullback_map_eq_iff`: factorization through a monomorphism
  can be checked after base change if the projection to the source is a strong epimorphism.
* `CategoryTheory.Over.pullbackRightPullbackFstIso_inv_comp_pullback_map`: the identification
  `T ×_S X ≅ T ×_{S'} (S' ×_S X)` is natural in `T` over `S'`.
* `CategoryTheory.Over.mapSection`: a section of a presheaf on `Over S` over `T` restricts to a
  section of its restriction along `Over.map T.hom`.
* `CategoryTheory.isPullback_overPost_iff`: for `F : C ⥤ D` and `X : C`, a square in
  `Over (F.obj X)` with a side `(Over.post F).map snd` is a pullback square exactly when the
  underlying square in `D` is.
* `CategoryTheory.Over.postHomMk`: for `F` full, a morphism `F.obj a ⟶ B.left` regarded as a
  morphism of `Over (F.obj X)` out of the image under `Over.post F` of an object over `X`.
-/

public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Over

/-- The underlying morphism of an isomorphism in `Over X` is an isomorphism. -/
instance isIso_left {T : Type u} [Category.{v} T] {X : T} {f g : Over X} (φ : f ⟶ g)
    [IsIso φ] : IsIso φ.left :=
  (Over.forget X).map_isIso φ

/-- An object `Z` over `S` is the image under `Over.map p` of `Over.mk a`, for a lift
`a : Z.left ⟶ S'` of its structure morphism through `p : S' ⟶ S`. -/
def mapMkIso {T : Type u} [Category.{v} T] {S S' : T} {p : S' ⟶ S} {Z : Over S}
    (a : Z.left ⟶ S') (ha : a ≫ p = Z.hom) : (Over.map p).obj (Over.mk a) ≅ Z :=
  Over.isoMk (Iso.refl Z.left) (by simp [ha])

/-- The isomorphism `mapMkIso` is the identity on underlying objects. -/
@[simp]
theorem mapMkIso_hom_left {T : Type u} [Category.{v} T] {S S' : T} {p : S' ⟶ S} {Z : Over S}
    (a : Z.left ⟶ S') (ha : a ≫ p = Z.hom) : (mapMkIso a ha).hom.left = 𝟙 Z.left := by
  simp [mapMkIso]

/-- The inverse of `mapMkIso` is the identity on underlying objects. -/
@[simp]
theorem mapMkIso_inv_left {T : Type u} [Category.{v} T] {S S' : T} {p : S' ⟶ S} {Z : Over S}
    (a : Z.left ⟶ S') (ha : a ≫ p = Z.hom) : (mapMkIso a ha).inv.left = 𝟙 Z.left := by
  simp [mapMkIso]

/-- Base change along `f : T ⟶ S` of a morphism `g : A ⟶ B` over `S` is the pullback of `g.left`
along the projection `B ×_S T ⟶ B`: the square formed by `A ×_S T ⟶ B ×_S T`, the two first
projections and `g.left` is cartesian. -/
theorem isPullback_pullback_map_left {C : Type u} [Category.{v} C] {S T : C} (f : T ⟶ S)
    [HasPullbacksAlong f] {A B : Over S} (g : A ⟶ B) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst A.hom f) (pullback.fst B.hom f)
      g.left := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback B.hom f).flip
  simpa using (IsPullback.of_hasPullback A.hom f).flip

/-- The identification `T ×_S X ≅ T ×_{S'} (S' ×_S X)` of the two base changes of `f : X ⟶ S` to
an object `T` over `S'`, where `T` lies over `S` through `g : S' ⟶ S`, commutes with the morphisms
induced by a morphism `φ : T ⟶ T'` over `S'`. -/
@[reassoc]
theorem pullbackRightPullbackFstIso_inv_comp_pullback_map {C : Type u} [Category.{v} C]
    [HasPullbacks C] {S S' X : C} (f : X ⟶ S) (g : S' ⟶ S) {T T' : Over S'} (φ : T ⟶ T') :
    (pullbackRightPullbackFstIso g f T.hom).inv ≫ ((Over.pullback (pullback.fst g f)).map φ).left =
      ((Over.pullback f).map ((Over.map g).map φ)).left ≫
        (pullbackRightPullbackFstIso g f T'.hom).inv := by
  apply pullback.hom_ext
  · simp
  · apply pullback.hom_ext
    · simp
    · simp

/-- A morphism over `S` factors through a monomorphism if and only if its base change along
`p` does, provided the projection to its source is a strong epimorphism. -/
theorem exists_comp_pullback_map_eq_iff {C : Type u} [Category.{v} C]
    {S S' : C} (p : S' ⟶ S) [HasPullbacksAlong p]
    {X Y Z : Over S} [StrongEpi (pullback.fst Z.hom p)]
    (i : X ⟶ Y) [Mono i] (f : Z ⟶ Y) :
    (∃ g : (Over.pullback p).obj Z ⟶ (Over.pullback p).obj X,
      g ≫ (Over.pullback p).map i = (Over.pullback p).map f) ↔
      ∃ g : Z ⟶ X, g ≫ i = f := by
  constructor
  · rintro ⟨g, hg⟩
    have sq : CommSq (g.left ≫ pullback.fst X.hom p) (pullback.fst Z.hom p) i.left f.left := by
      constructor
      simpa using congr(($hg).left ≫ pullback.fst Y.hom p)
    refine ⟨Over.homMk sq.lift ?_, ?_⟩
    · simpa only [Category.assoc, i.w, f.w] using congr($(sq.fac_right) ≫ Y.hom)
    · ext1
      simpa only [comp_left, homMk_left] using sq.fac_right
  · rintro ⟨g, rfl⟩
    exact ⟨(Over.pullback p).map g, ((Over.pullback p).map_comp g i).symm⟩

/-- A section `ξ` of a presheaf `F` on `Over S` over an object `T` restricts to every object
`(Over.map T.hom).obj T'` for `T'` over `T.left`, along the morphism `T'` itself; these
restrictions form a section of the presheaf `(Over.map T.hom).op ⋙ F` on `Over T.left`. -/
def mapSection {C : Type u} [Category.{v} C] {S : C} (F : (Over S)ᵒᵖ ⥤ Type*) {T : Over S}
    (ξ : F.obj (Opposite.op T)) : ((Over.map T.hom).op ⋙ F).sections where
  val T' := F.map (Over.homMk T'.unop.hom : (Over.map T.hom).obj T'.unop ⟶ T).op ξ
  property {T₁ T₂} f := by
    dsimp
    rw [← Functor.map_comp_apply, ← op_comp]
    congr 3
    ext
    simp

/-- The section `mapSection F ξ` over `T'` is the restriction of `ξ` along `T'`. -/
@[simp]
lemma mapSection_coe {C : Type u} [Category.{v} C] {S : C} (F : (Over S)ᵒᵖ ⥤ Type*) {T : Over S}
    (ξ : F.obj (Opposite.op T)) (T' : (Over T.left)ᵒᵖ) :
    (mapSection F ξ).val T' =
      F.map (Over.homMk T'.unop.hom : (Over.map T.hom).obj T'.unop ⟶ T).op ξ :=
  (rfl)

end Over

section OverPost

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D) {X : C}

/-- A square in `Over (F.obj X)` with a side `(Over.post F).map snd` is a pullback square exactly
when the underlying square in `D` is. -/
lemma isPullback_overPost_iff {A B : Over (F.obj X)} {f : A ⟶ B} {a b : Over X}
    {g : (Over.post F).obj a ⟶ B} {fst : (Over.post F).obj b ⟶ A} {snd : b ⟶ a} :
    IsPullback fst ((Over.post F).map snd) f g ↔
      IsPullback fst.left (F.map snd.left) f.left g.left := by
  refine ⟨fun h ↦ h.map (Over.forget _), fun h ↦ IsPullback.of_map (Over.forget _) ?_ h⟩
  ext
  exact h.w

variable {F}

/-- A pullback square in `D` with sides `F.map snd` and `g.left`, for `g : (Over.post F).obj a ⟶ B`
in `Over (F.obj X)`, lifts to a pullback square in `Over (F.obj X)`, with `b` lying over `X`
through `snd ≫ a.hom`. -/
lemma IsPullback.overPost_homMk {A B : Over (F.obj X)} {f : A ⟶ B} {a : Over X} {b : C}
    {g : (Over.post F).obj a ⟶ B} {fst : F.obj b ⟶ A.left} {snd : b ⟶ a.left}
    (h : IsPullback fst (F.map snd) f.left g.left) :
    IsPullback (Over.homMk (U := (Over.post F).obj (Over.mk (snd ≫ a.hom))) fst
        (by rw [← Over.w f, reassoc_of% h.w, Over.w g]; exact (F.map_comp _ _).symm) : _ ⟶ A)
      ((Over.post F).map (Over.homMk snd : Over.mk (snd ≫ a.hom) ⟶ a)) f g :=
  (isPullback_overPost_iff F).2 h

variable [F.Full]

/-- A morphism `g : F.obj a ⟶ B.left` to the underlying object of `B : Over (F.obj X)`, regarded
as a morphism of `Over (F.obj X)` out of the image under `Over.post F` of `a` over `X`. -/
noncomputable abbrev Over.postHomMk {B : Over (F.obj X)} {a : C} (g : F.obj a ⟶ B.left) :
    (Over.post F).obj (Over.mk (F.preimage (g ≫ B.hom))) ⟶ B :=
  Over.homMk g (by simp)

end OverPost

end CategoryTheory
