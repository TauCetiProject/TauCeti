/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Presentation
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The free braided category on a tensor signature

The free braided category `TauCeti.TensorSignature.FreeBraided S` on a tensor signature `S` is
presented as a monoidal category, using the presentations of
`TauCeti.CategoryTheory.Monoidal.Presentation`. Its generating objects are those of `S`; its
coupons, collected in `TauCeti.TensorSignature.braidedExtension S`, are the coupons of `S`
together with a formal braiding `X ⊗ Y ⟶ Y ⊗ X` and a formal inverse braiding `Y ⊗ X ⟶ X ⊗ Y`
for every ordered pair of tensor words `X`, `Y`. The equations `TensorSignature.FreeBraided.Rel`
are exactly the axioms of a braided monoidal category: the formal braidings are mutually inverse,
natural on both sides, and satisfy the two hexagon identities. No equation between coupons of `S`
is imposed, and the braiding is not required to be symmetric.

Its universal property is that of a free braided category, for braided functors into arbitrary
(not necessarily strict) braided categories:

* `TensorSignature.FreeBraided.lift fo fc` is the braided functor determined by images `fo` of
  the generating objects and `fc` of the coupons of `S`, with computation rules
  `FreeBraided.lift_obj_of` and `FreeBraided.lift_map_coupon`; it sends the braiding to the
  braiding (`FreeBraided.lift_map_braiding_hom`), with identity tensorator and unit comparison.
* `TensorSignature.FreeBraided.monoidalNatIso`: two braided functors out of `S.FreeBraided`
  agreeing up to isomorphism on the generating objects, compatibly with the coupons of `S`, are
  isomorphic by a monoidal natural isomorphism. Compatibility with the formal braidings is not a
  hypothesis: it is automatic for braided functors
  (`FreeBraided.map_braiding_comp_wordIso_hom`).

Since `S.FreeBraided` is a presented monoidal category, monoidal natural transformations out of
it are determined by their components at the generating objects by
`TauCeti.TensorSignature.Presented.natTrans_ext`.

## References

* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. 102 (1993), 20–78.
* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991) (tensor
  schemes, §1, and free braided tensor categories on them).
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory FreeMonoidalCategory Functor.LaxMonoidal
  Functor.OplaxMonoidal

namespace TauCeti.TensorSignature

variable (S : TensorSignature.{u, v})

/-- The coupons of the braided extension of a tensor signature `S`: the coupons of `S`, and a
formal braiding and a formal inverse braiding for every ordered pair of tensor words. -/
inductive BraidedCoupon : Type (max u v)
  | /-- A coupon of `S`. -/
    coupon (g : S.Coupon)
  | /-- The formal braiding `X ⊗ Y ⟶ Y ⊗ X`. -/
    braiding (X Y : FreeMonoidalCategory S.Obj)
  | /-- The formal inverse braiding `Y ⊗ X ⟶ X ⊗ Y`. -/
    braidingInv (X Y : FreeMonoidalCategory S.Obj)

/-- The braided extension of a tensor signature `S`: the same generating objects, and as
coupons those of `S` together with a formal braiding `X ⊗ Y ⟶ Y ⊗ X` and a formal inverse
braiding `Y ⊗ X ⟶ X ⊗ Y` for all tensor words `X` and `Y`. -/
abbrev braidedExtension : TensorSignature.{u, max u v} where
  Obj := S.Obj
  Coupon := S.BraidedCoupon
  src
    | .coupon g => S.src g
    | .braiding X Y => X.tensor Y
    | .braidingInv X Y => Y.tensor X
  tgt
    | .coupon g => S.tgt g
    | .braiding X Y => Y.tensor X
    | .braidingInv X Y => X.tensor Y

namespace FreeBraided

variable {S}

/-- The formal braiding of two objects of the free monoidal category on the braided extension. -/
abbrev freeBraiding (X Y : S.braidedExtension.FreeMonoidal) : X ⊗ Y ⟶ Y ⊗ X :=
  FreeMonoidal.coupon (S := S.braidedExtension) (.braiding X.as Y.as)

/-- The formal inverse braiding of two objects of the free monoidal category on the braided
extension. -/
abbrev freeBraidingInv (X Y : S.braidedExtension.FreeMonoidal) : Y ⊗ X ⟶ X ⊗ Y :=
  FreeMonoidal.coupon (S := S.braidedExtension) (.braidingInv X.as Y.as)

/-- The axioms of a braided monoidal category for the formal braidings: they are inverse to the
formal inverse braidings, natural on both sides, and satisfy the two hexagon identities, in the
form of the fields of `CategoryTheory.BraidedCategory`. -/
inductive Rel : HomRel S.braidedExtension.FreeMonoidal
  | hom_inv_id (X Y : S.braidedExtension.FreeMonoidal) :
      Rel (freeBraiding X Y ≫ freeBraidingInv X Y) (𝟙 _)
  | inv_hom_id (X Y : S.braidedExtension.FreeMonoidal) :
      Rel (freeBraidingInv X Y ≫ freeBraiding X Y) (𝟙 _)
  | naturality_right (X : S.braidedExtension.FreeMonoidal) {Y Z : S.braidedExtension.FreeMonoidal}
      (f : Y ⟶ Z) :
      Rel (X ◁ f ≫ freeBraiding X Z) (freeBraiding X Y ≫ f ▷ X)
  | naturality_left {X Y : S.braidedExtension.FreeMonoidal} (f : X ⟶ Y)
      (Z : S.braidedExtension.FreeMonoidal) :
      Rel (f ▷ Z ≫ freeBraiding Y Z) (freeBraiding X Z ≫ Z ◁ f)
  | hexagon_forward (X Y Z : S.braidedExtension.FreeMonoidal) :
      Rel ((α_ X Y Z).hom ≫ freeBraiding X (Y ⊗ Z) ≫ (α_ Y Z X).hom)
        (freeBraiding X Y ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ freeBraiding X Z)
  | hexagon_reverse (X Y Z : S.braidedExtension.FreeMonoidal) :
      Rel ((α_ X Y Z).inv ≫ freeBraiding (X ⊗ Y) Z ≫ (α_ Z X Y).inv)
        (X ◁ freeBraiding Y Z ≫ (α_ X Z Y).inv ≫ freeBraiding X Z ▷ Y)

end FreeBraided

/-- The free braided category on a tensor signature `S`: the monoidal category presented by the
generating objects of `S`, the coupons of `S` and formal braidings with their inverses, subject
only to the axioms of a braided monoidal category. Its objects are the tensor words in the
generating objects of `S`. -/
abbrev FreeBraided : Type u :=
  S.braidedExtension.Presented FreeBraided.Rel

namespace FreeBraided

variable {S}

/-- The quotient functor from the free monoidal category on the braided extension of `S` onto
the free braided category on `S`. -/
abbrev quotientFunctor : S.braidedExtension.FreeMonoidal ⥤ S.FreeBraided :=
  Presented.quotientFunctor Rel

/-- The object of the free braided category given by a single generating object. -/
abbrev of (a : S.Obj) : S.FreeBraided :=
  quotientFunctor.obj (FreeMonoidal.of a)

/-- The generating morphism of the free braided category given by a coupon of `S`, from its
source word to its target word. -/
abbrev coupon (g : S.Coupon) :
    quotientFunctor.obj (⟨S.src g⟩ : S.braidedExtension.FreeMonoidal) ⟶
      quotientFunctor.obj (⟨S.tgt g⟩ : S.braidedExtension.FreeMonoidal) :=
  quotientFunctor.map (FreeMonoidal.coupon (S := S.braidedExtension) (.coupon g))

/-- The braiding of the free braided category is given by the classes of the formal braidings,
with the classes of the formal inverse braidings as inverses. -/
instance : BraidedCategory S.FreeBraided where
  braiding X Y :=
    { hom := quotientFunctor.map (freeBraiding X.as Y.as)
      inv := quotientFunctor.map (freeBraidingInv X.as Y.as)
      -- The remaining `rfl` identifies `𝟙 (quotientFunctor.obj (X.as ⊗ Y.as))` with
      -- `𝟙 (X ⊗ Y)`: the tensor product of the quotient is defined on representatives.
      hom_inv_id := by
        rw [← Functor.map_comp, Presented.sound (Rel.hom_inv_id _ _), Functor.map_id]
        rfl
      inv_hom_id := by
        rw [← Functor.map_comp, Presented.sound (Rel.inv_hom_id _ _), Functor.map_id]
        rfl }
  braiding_naturality_right X Y Z f := by
    obtain ⟨f, rfl⟩ := quotientFunctor.map_surjective f
    exact Presented.sound (Rel.naturality_right X.as f)
  braiding_naturality_left f Z := by
    obtain ⟨f, rfl⟩ := quotientFunctor.map_surjective f
    exact Presented.sound (Rel.naturality_left f Z.as)
  hexagon_forward X Y Z := Presented.sound (Rel.hexagon_forward X.as Y.as Z.as)
  hexagon_reverse X Y Z := Presented.sound (Rel.hexagon_reverse X.as Y.as Z.as)

/-- The braiding of the free braided category is the class of the formal braiding. -/
theorem braiding_hom (X Y : S.FreeBraided) :
    (β_ X Y).hom = quotientFunctor.map (freeBraiding X.as Y.as) :=
  (rfl)

/-- The inverse braiding of the free braided category is the class of the formal inverse
braiding. -/
theorem braiding_inv (X Y : S.FreeBraided) :
    (β_ X Y).inv = quotientFunctor.map (freeBraidingInv X.as Y.as) :=
  (rfl)

section Lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (fo : S.Obj → D) (fc : ∀ g : S.Coupon, projectObj fo (S.src g) ⟶ projectObj fo (S.tgt g))

/-- The interpretation of the coupons of the braided extension of `S` in a braided category:
the coupons of `S` by `fc`, and the formal braidings and their inverses by the braidings of `D`
and their inverses. -/
def liftCoupon : ∀ g : S.BraidedCoupon,
    projectObj fo (S.braidedExtension.src g) ⟶ projectObj fo (S.braidedExtension.tgt g)
  | .coupon g => fc g
  | .braiding X Y => (β_ (projectObj fo X) (projectObj fo Y)).hom
  | .braidingInv X Y => (β_ (projectObj fo X) (projectObj fo Y)).inv

@[simp]
theorem liftCoupon_coupon (g : S.Coupon) : liftCoupon fo fc (.coupon g) = fc g := (rfl)

@[simp]
theorem liftCoupon_braiding (X Y : FreeMonoidalCategory S.Obj) :
    liftCoupon fo fc (.braiding X Y) = (β_ (projectObj fo X) (projectObj fo Y)).hom := (rfl)

@[simp]
theorem liftCoupon_braidingInv (X Y : FreeMonoidalCategory S.Obj) :
    liftCoupon fo fc (.braidingInv X Y) = (β_ (projectObj fo X) (projectObj fo Y)).inv := (rfl)

/-- The interpretation of the free monoidal category on the braided extension of `S` given by
`liftCoupon fo fc` satisfies the axioms of a braided monoidal category. -/
theorem freeMonoidalLift_map_eq_of_rel ⦃X Y : S.braidedExtension.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄
    (h : Rel f g) :
    (FreeMonoidal.lift (S := S.braidedExtension) fo (liftCoupon fo fc)).map f =
      (FreeMonoidal.lift (S := S.braidedExtension) fo (liftCoupon fo fc)).map g := by
  -- After computing the interpretation of each side, the relations are the corresponding
  -- axioms of the braided category `D`. The objects `(FreeMonoidal.lift fo _).obj X` are by
  -- definition the interpretations `projectObj fo X.as` appearing in `liftCoupon`.
  cases h with
  | hom_inv_id X Y =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, liftCoupon_braiding,
      liftCoupon_braidingInv, Functor.map_id]
    exact (β_ _ _).hom_inv_id
  | inv_hom_id X Y =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, liftCoupon_braiding,
      liftCoupon_braidingInv, Functor.map_id]
    exact (β_ _ _).inv_hom_id
  | naturality_right X f =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, liftCoupon_braiding,
      FreeMonoidal.lift_map_whiskerLeft, FreeMonoidal.lift_map_whiskerRight]
    exact BraidedCategory.braiding_naturality_right _ _
  | naturality_left f Z =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, liftCoupon_braiding,
      FreeMonoidal.lift_map_whiskerLeft, FreeMonoidal.lift_map_whiskerRight]
    exact BraidedCategory.braiding_naturality_left _ _
  | hexagon_forward X Y Z =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, liftCoupon_braiding,
      FreeMonoidal.lift_map_whiskerLeft, FreeMonoidal.lift_map_whiskerRight,
      FreeMonoidal.lift_map_associator_hom]
    exact BraidedCategory.hexagon_forward _ _ _
  | hexagon_reverse X Y Z =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_coupon, liftCoupon_braiding,
      FreeMonoidal.lift_map_whiskerLeft, FreeMonoidal.lift_map_whiskerRight,
      FreeMonoidal.lift_map_associator_inv]
    exact BraidedCategory.hexagon_reverse _ _ _

/-- The braided functor out of the free braided category on `S` determined by the images `fo`
of the generating objects and `fc` of the coupons of `S`. It sends the braiding to the braiding,
and its tensorator and unit comparison are identities. -/
abbrev lift : S.FreeBraided ⥤ D :=
  Presented.lift fo (liftCoupon fo fc) (freeMonoidalLift_map_eq_of_rel fo fc)

theorem lift_obj_of (a : S.Obj) : (lift fo fc).obj (of a) = fo a := (rfl)

theorem lift_map_coupon (g : S.Coupon) : (lift fo fc).map (coupon g) = fc g :=
  (Presented.lift_map _ _ _ _).trans (FreeMonoidal.lift_map_coupon _ _ _)

/- The two braiding lemmas take priority over Mathlib's `Functor.map_braiding`, which would
instead produce the identity tensorators of `lift fo fc` with types that `simp` cannot cancel. -/
@[simp high]
theorem lift_map_braiding_hom (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).hom = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).hom :=
  (Presented.lift_map _ _ _ _).trans (FreeMonoidal.lift_map_coupon _ _ _)

@[simp high]
theorem lift_map_braiding_inv (X Y : S.FreeBraided) :
    (lift fo fc).map (β_ X Y).inv = (β_ ((lift fo fc).obj X) ((lift fo fc).obj Y)).inv :=
  (Presented.lift_map _ _ _ _).trans (FreeMonoidal.lift_map_coupon _ _ _)

instance : (lift fo fc).Braided where
  braided X Y := by
    -- The tensorators are identities on `(lift fo fc).obj X ⊗ (lift fo fc).obj Y`, which is
    -- `(lift fo fc).obj (X ⊗ Y)` by definition of the lifted functor on objects.
    simp only [Presented.lift_μ, lift_map_braiding_hom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end Lift

section Uniqueness

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  {F G : S.FreeBraided ⥤ D} [F.Braided] [G.Braided]
  {e : ∀ a, F.obj (of a) ≅ G.obj (of a)}

/-- The isomorphisms which `e` induces on all tensor words commute with the braidings: braided
functors out of the free braided category automatically respect the formal braidings. -/
theorem map_braiding_comp_wordIso_hom (X Y : S.braidedExtension.FreeMonoidal) :
    F.map (β_ (quotientFunctor.obj X) (quotientFunctor.obj Y)).hom ≫
        (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (Y ⊗ X).as).hom =
      (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (X ⊗ Y).as).hom ≫
        G.map (β_ (quotientFunctor.obj X) (quotientFunctor.obj Y)).hom := by
  simp [FreeMonoidal.wordIso_tensor_hom]

/-- The isomorphisms which `e` induces on all tensor words commute with the inverse braidings. -/
theorem map_braiding_inv_comp_wordIso_hom (X Y : S.braidedExtension.FreeMonoidal) :
    F.map (β_ (quotientFunctor.obj X) (quotientFunctor.obj Y)).inv ≫
        (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (X ⊗ Y).as).hom =
      (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (Y ⊗ X).as).hom ≫
        G.map (β_ (quotientFunctor.obj X) (quotientFunctor.obj Y)).inv := by
  rw [← cancel_epi (F.map (β_ _ _).hom), ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp, reassoc_of% (map_braiding_comp_wordIso_hom X Y),
    ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]

variable (F G e) in
/-- Two braided functors out of the free braided category on `S` that agree up to isomorphisms
`e` on the generating objects, compatibly with every coupon of `S`, are isomorphic by a monoidal
natural isomorphism extending `e`. The compatibility is stated with the isomorphisms
`FreeMonoidal.wordIso` which `e` induces on all tensor words; compatibility with the braidings is
automatic. Taking `F` to be `lift fo fc`, this is the uniqueness of the lift. -/
def monoidalNatIso
    (he : ∀ g : S.Coupon, F.map (coupon g) ≫
        (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (S.tgt g)).hom =
      (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (S.src g)).hom ≫
        G.map (coupon g)) :
    F ≅ G :=
  Presented.monoidalNatIso F G e fun
    | .coupon g => he g
    | .braiding X Y => map_braiding_comp_wordIso_hom ⟨X⟩ ⟨Y⟩
    | .braidingInv X Y => map_braiding_inv_comp_wordIso_hom ⟨X⟩ ⟨Y⟩

variable (he : ∀ g : S.Coupon, F.map (coupon g) ≫
    (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (S.tgt g)).hom =
  (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e (S.src g)).hom ≫
    G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.braidedExtension.FreeMonoidal) :
    (monoidalNatIso F G e he).hom.app (quotientFunctor.obj X) =
      (FreeMonoidal.wordIso (quotientFunctor ⋙ F) (quotientFunctor ⋙ G) e X.as).hom :=
  Presented.monoidalNatIso_hom_app _ X

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso F G e he).hom.app (of a) = (e a).hom := by
  simp

instance : NatTrans.IsMonoidal (monoidalNatIso F G e he).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Presented.monoidalNatIso F G e _).hom)

end Uniqueness

end FreeBraided

end TauCeti.TensorSignature
