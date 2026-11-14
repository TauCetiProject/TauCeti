/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Core

/-!
# The category and groupoid of strong braided monoidal functors

Mathlib bundles lax monoidal functors as `CategoryTheory.LaxMonoidalFunctor` and lax braided
functors as `CategoryTheory.LaxBraidedFunctor`, with monoidal natural transformations as morphisms.
This file introduces `TauCeti.BraidedFunctor C D`, the category of bundled *strong* braided
monoidal functors from `C` to `D` and monoidal natural transformations, whose core
`Core (BraidedFunctor C D)` is the groupoid of strong braided functors and monoidal natural
isomorphisms.

Two strong braided functors agree as soon as their underlying lax monoidal functors agree
(`TauCeti.BraidedFunctor.ext`): the inverse coherence maps `η` and `δ` of a strong monoidal functor
are uniquely determined by `ε` and `μ` (`CategoryTheory.Functor.Monoidal.toLaxMonoidal_injective`),
and the braiding condition is a proposition (`CategoryTheory.Functor.Braided.toMonoidal_injective`).
Likewise, morphisms need no extra braiding condition beyond `CategoryTheory.NatTrans.IsMonoidal`, so
the forgetful functors to `LaxBraidedFunctor C D` and `LaxMonoidalFunctor C D` (and their induced
functors on cores) are fully faithful.

## Main declarations

* `TauCeti.BraidedFunctor`: bundled strong braided monoidal functors, with category structure given
  by monoidal natural transformations and extensionality `TauCeti.BraidedFunctor.ext`;
* `TauCeti.BraidedFunctor.homMk`, `TauCeti.BraidedFunctor.isoMk`, and
  `TauCeti.BraidedFunctor.isoOfComponents`: constructors for morphisms and isomorphisms, modeled on
  `CategoryTheory.LaxMonoidalFunctor` and `CategoryTheory.LaxBraidedFunctor`;
* `TauCeti.BraidedFunctor.forgetToLaxBraided` and `TauCeti.BraidedFunctor.forgetToLaxMonoidal`:
  fully faithful forgetful functors;
* `TauCeti.BraidedFunctor.id`, `TauCeti.BraidedFunctor.comp`,
  `TauCeti.BraidedFunctor.whiskeringLeft`, and `TauCeti.BraidedFunctor.whiskeringRight`: identity,
  composition, and whiskering of bundled strong braided functors, together with unitors and
  associators.

## References

* A. Joyal, R. Street, *Braided tensor categories*, Adv. Math. **102** (1993), 20–78
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.1
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace TauCeti

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- Bundled strong braided monoidal functors from `C` to `D`. Morphisms are monoidal natural
transformations, and `Core (BraidedFunctor C D)` is the groupoid of strong braided functors and
monoidal natural isomorphisms. -/
structure BraidedFunctor (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] extends C ⥤ D where
  /-- The underlying functor is strong braided monoidal. -/
  braided : toFunctor.Braided := by infer_instance

namespace BraidedFunctor

attribute [instance] braided

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E'] [BraidedCategory E']

/-- Bundle an unbundled strong braided monoidal functor `F : C ⥤ D`. -/
abbrev of (F : C ⥤ D) [F.Braided] : BraidedFunctor C D where
  toFunctor := F

/-- The functor underlying `BraidedFunctor.of F` is `F`. -/
@[simp]
theorem of_toFunctor (F : C ⥤ D) [F.Braided] : (of F).toFunctor = F :=
  (rfl)

/-- The bundled lax braided functor underlying a strong braided functor. -/
abbrev toLaxBraidedFunctor (F : BraidedFunctor C D) : LaxBraidedFunctor C D where
  toFunctor := F.toFunctor

/-- The bundled lax monoidal functor underlying a strong braided functor. -/
abbrev toLaxMonoidalFunctor (F : BraidedFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor

/-- Passing to `LaxBraidedFunctor` retains the underlying functor. -/
@[simp]
theorem toLaxBraidedFunctor_toFunctor (F : BraidedFunctor C D) :
    F.toLaxBraidedFunctor.toFunctor = F.toFunctor :=
  (rfl)

/-- Passing to `LaxMonoidalFunctor` retains the underlying functor. -/
@[simp]
theorem toLaxMonoidalFunctor_toFunctor (F : BraidedFunctor C D) :
    F.toLaxMonoidalFunctor.toFunctor = F.toFunctor :=
  (rfl)

/-- Forgetting from `BraidedFunctor` to `LaxBraidedFunctor` and then `LaxMonoidalFunctor` agrees
with forgetting directly to `LaxMonoidalFunctor`. -/
@[simp]
theorem toLaxBraidedFunctor_toLaxMonoidalFunctor (F : BraidedFunctor C D) :
    F.toLaxBraidedFunctor.toLaxMonoidalFunctor = F.toLaxMonoidalFunctor :=
  (rfl)

/-- A bundled strong braided functor is determined by its underlying lax monoidal functor. -/
theorem toLaxMonoidalFunctor_injective :
    Function.Injective (toLaxMonoidalFunctor (C := C) (D := D)) := by
  rintro ⟨F, hF⟩ ⟨G, hG⟩ h
  have hFG : F = G := congrArg LaxMonoidalFunctor.toFunctor h
  subst hFG
  have hLax : hF.toLaxMonoidal = hG.toLaxMonoidal := eq_of_heq (LaxMonoidalFunctor.mk.inj h).2
  have hMon : hF.toMonoidal = hG.toMonoidal := Functor.Monoidal.toLaxMonoidal_injective F hLax
  cases Functor.Braided.toMonoidal_injective F hMon
  rfl

/-- Two bundled strong braided functors are equal when their underlying lax monoidal functors are
equal. -/
@[ext]
theorem ext {F G : BraidedFunctor C D} (h : F.toLaxMonoidalFunctor = G.toLaxMonoidalFunctor) :
    F = G :=
  toLaxMonoidalFunctor_injective h

/-- A bundled strong braided functor is determined by its underlying lax braided functor. -/
theorem toLaxBraidedFunctor_injective :
    Function.Injective (toLaxBraidedFunctor (C := C) (D := D)) := fun _ _ h ↦
  ext (congrArg LaxBraidedFunctor.toLaxMonoidalFunctor h)

/-- Two bundled strong braided functors are equal when their underlying lax braided functors are
equal. -/
theorem ext_of_toLaxBraidedFunctor {F G : BraidedFunctor C D}
    (h : F.toLaxBraidedFunctor = G.toLaxBraidedFunctor) : F = G :=
  toLaxBraidedFunctor_injective h

/-! ### Morphisms and category structure -/

/-- A monoidal natural transformation between bundled strong braided functors. -/
@[ext]
structure Hom (F G : BraidedFunctor C D) where
  /-- The underlying natural transformation. -/
  hom : F.toFunctor ⟶ G.toFunctor
  /-- Compatibility with the unit and tensor comparisons. -/
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal

instance : Category (BraidedFunctor C D) where
  Hom := Hom
  id F := ⟨𝟙 F.toFunctor, inferInstance⟩
  comp α β := ⟨α.hom ≫ β.hom, inferInstance⟩

/-- The underlying natural transformation of the identity morphism is the identity. -/
@[simp]
theorem id_hom (F : BraidedFunctor C D) : Hom.hom (𝟙 F) = 𝟙 F.toFunctor :=
  (rfl)

/-- Composition of morphisms is composition of their underlying natural transformations. -/
@[reassoc, simp]
theorem comp_hom {F G H : BraidedFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom :=
  (rfl)

/-- Two morphisms of strong braided functors agree when their underlying natural transformations
agree. -/
@[ext]
theorem hom_ext {F G : BraidedFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β :=
  Hom.ext h

/-- Construct a morphism in `BraidedFunctor C D` from a monoidal natural transformation. -/
def homMk {F G : BraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G :=
  ⟨f, inferInstance⟩

/-- `homMk` retains the supplied natural transformation. -/
@[simp]
theorem homMk_hom {F G : BraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal f] : (homMk f).hom = f :=
  (rfl)

/-- Construct an isomorphism in `BraidedFunctor C D` from a monoidal natural isomorphism. -/
def isoMk {F G : BraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

/-- The forward morphism of `isoMk e` has underlying natural transformation `e.hom`. -/
@[simp]
theorem isoMk_hom_hom {F G : BraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).hom.hom = e.hom :=
  (rfl)

/-- The inverse morphism of `isoMk e` has underlying natural transformation `e.inv`. -/
@[simp]
theorem isoMk_inv_hom {F G : BraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).inv.hom = e.inv :=
  (rfl)

/-- Construct an isomorphism in `BraidedFunctor C D` from objectwise isomorphisms compatible with
morphisms, the unit comparison, and the tensor comparison. -/
def isoOfComponents {F G : BraidedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  haveI : NatTrans.IsMonoidal (NatIso.ofComponents e naturality).hom := ⟨unit, tensor⟩
  isoMk (NatIso.ofComponents e naturality)

/-- The forward component at `X` of `isoOfComponents` is `(e X).hom`. -/
@[simp]
theorem isoOfComponents_hom_hom_app {F G : BraidedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y) (X : C) :
    (isoOfComponents e naturality unit tensor).hom.hom.app X = (e X).hom :=
  (rfl)

/-- The inverse component at `X` of `isoOfComponents` is `(e X).inv`. -/
@[simp]
theorem isoOfComponents_inv_hom_app {F G : BraidedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y) (X : C) :
    (isoOfComponents e naturality unit tensor).inv.hom.app X = (e X).inv :=
  (rfl)

/-! ### Forgetful functors -/

section Forget

variable (C D)

/-- The faithful forgetful functor from strong braided functors to ordinary functors. -/
@[expose]
def forgetToFunctor : BraidedFunctor C D ⥤ C ⥤ D where
  obj F := F.toFunctor
  map α := α.hom

/-- `forgetToFunctor` takes a bundled strong braided functor to its underlying functor. -/
@[simp]
theorem forgetToFunctor_obj (F : BraidedFunctor C D) :
    (forgetToFunctor C D).obj F = F.toFunctor :=
  (rfl)

/-- `forgetToFunctor` takes a morphism to its underlying natural transformation. -/
@[simp]
theorem forgetToFunctor_map {F G : BraidedFunctor C D} (α : F ⟶ G) :
    (forgetToFunctor C D).map α = α.hom :=
  (rfl)

instance : (forgetToFunctor C D).Faithful where
  map_injective h := hom_ext h

/-- The fully faithful forgetful functor from strong braided functors to lax monoidal functors. -/
@[expose]
def forgetToLaxMonoidal : BraidedFunctor C D ⥤ LaxMonoidalFunctor C D where
  obj F := F.toLaxMonoidalFunctor
  map α := ⟨α.hom, α.isMonoidal⟩

/-- `forgetToLaxMonoidal` sends `F` to `F.toLaxMonoidalFunctor`. -/
@[simp]
theorem forgetToLaxMonoidal_obj (F : BraidedFunctor C D) :
    (forgetToLaxMonoidal C D).obj F = F.toLaxMonoidalFunctor :=
  (rfl)

/-- The natural transformation underlying `(forgetToLaxMonoidal C D).map α` is `α.hom`. -/
@[simp]
theorem forgetToLaxMonoidal_map_hom {F G : BraidedFunctor C D} (α : F ⟶ G) :
    ((forgetToLaxMonoidal C D).map α).hom = α.hom :=
  (rfl)

/-- Forgetting from strong braided functors to lax monoidal functors is fully faithful. -/
def fullyFaithfulForgetToLaxMonoidal : (forgetToLaxMonoidal C D).FullyFaithful where
  preimage f := ⟨f.hom, f.isMonoidal⟩

instance : (forgetToLaxMonoidal C D).Full :=
  (fullyFaithfulForgetToLaxMonoidal C D).full

instance : (forgetToLaxMonoidal C D).Faithful :=
  (fullyFaithfulForgetToLaxMonoidal C D).faithful

/-- The fully faithful forgetful functor from strong braided functors to lax braided functors. -/
@[expose]
def forgetToLaxBraided : BraidedFunctor C D ⥤ LaxBraidedFunctor C D where
  obj F := F.toLaxBraidedFunctor
  map α := InducedCategory.homMk ⟨α.hom, α.isMonoidal⟩

/-- `forgetToLaxBraided` sends `F` to `F.toLaxBraidedFunctor`. -/
@[simp]
theorem forgetToLaxBraided_obj (F : BraidedFunctor C D) :
    (forgetToLaxBraided C D).obj F = F.toLaxBraidedFunctor :=
  (rfl)

/-- The natural transformation underlying `(forgetToLaxBraided C D).map α` is `α.hom`. -/
@[simp]
theorem forgetToLaxBraided_map_hom_hom {F G : BraidedFunctor C D} (α : F ⟶ G) :
    ((forgetToLaxBraided C D).map α).hom.hom = α.hom :=
  (rfl)

/-- Forgetting from strong braided functors to lax braided functors is fully faithful. -/
def fullyFaithfulForgetToLaxBraided : (forgetToLaxBraided C D).FullyFaithful where
  preimage f := ⟨f.hom.hom, f.hom.isMonoidal⟩
  map_preimage _ := InducedCategory.hom_ext rfl
  preimage_map _ := rfl

instance : (forgetToLaxBraided C D).Full :=
  (fullyFaithfulForgetToLaxBraided C D).full

instance : (forgetToLaxBraided C D).Faithful :=
  (fullyFaithfulForgetToLaxBraided C D).faithful

/-- Forgetting to `LaxBraidedFunctor` and then to `LaxMonoidalFunctor` is forgetting directly to
`LaxMonoidalFunctor`. -/
@[simp]
theorem forgetToLaxBraided_comp_forget :
    forgetToLaxBraided C D ⋙ LaxBraidedFunctor.forget = forgetToLaxMonoidal C D :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (LaxMonoidalFunctor.hom_ext rfl)

end Forget

/-! ### Identity, composition, and whiskering -/

/-- The identity strong braided monoidal functor on `C`. -/
abbrev id (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C] :
    BraidedFunctor C C :=
  of (𝟭 C)

/-- The composite of two bundled strong braided monoidal functors. -/
abbrev comp (F : BraidedFunctor C D) (G : BraidedFunctor D E) : BraidedFunctor C E :=
  of (F.toFunctor ⋙ G.toFunctor)

/-- Horizontal composition of morphisms of strong braided functors. -/
def hcomp {F₁ F₂ : BraidedFunctor C D} {G₁ G₂ : BraidedFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : F₁.comp G₁ ⟶ F₂.comp G₂ :=
  homMk (α.hom ◫ β.hom)

/-- Horizontal composition acts by horizontal composition on underlying natural transformations. -/
@[simp]
theorem hcomp_hom {F₁ F₂ : BraidedFunctor C D} {G₁ G₂ : BraidedFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : (hcomp α β).hom = α.hom ◫ β.hom :=
  (rfl)

/-- Precomposition with a strong braided functor `F : BraidedFunctor C D`. -/
@[expose]
def whiskeringLeft (F : BraidedFunctor C D)
    (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E] :
    BraidedFunctor D E ⥤ BraidedFunctor C E where
  obj G := F.comp G
  map β := homMk (Functor.whiskerLeft F.toFunctor β.hom)

/-- `whiskeringLeft F E` acts on objects by `F.comp`. -/
@[simp]
theorem whiskeringLeft_obj (F : BraidedFunctor C D) (G : BraidedFunctor D E) :
    (whiskeringLeft F E).obj G = F.comp G :=
  (rfl)

/-- `whiskeringLeft F E` acts on morphisms by `Functor.whiskerLeft`. -/
@[simp]
theorem whiskeringLeft_map_hom (F : BraidedFunctor C D) {G₁ G₂ : BraidedFunctor D E}
    (β : G₁ ⟶ G₂) : ((whiskeringLeft F E).map β).hom = Functor.whiskerLeft F.toFunctor β.hom :=
  (rfl)

/-- Postcomposition with a strong braided functor `G : BraidedFunctor D E`. -/
@[expose]
def whiskeringRight (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    (G : BraidedFunctor D E) :
    BraidedFunctor C D ⥤ BraidedFunctor C E where
  obj F := F.comp G
  map α := homMk (Functor.whiskerRight α.hom G.toFunctor)

/-- `whiskeringRight C G` acts on objects by `fun F ↦ F.comp G`. -/
@[simp]
theorem whiskeringRight_obj (F : BraidedFunctor C D) (G : BraidedFunctor D E) :
    (whiskeringRight C G).obj F = F.comp G :=
  (rfl)

/-- `whiskeringRight C G` acts on morphisms by `Functor.whiskerRight`. -/
@[simp]
theorem whiskeringRight_map_hom {F₁ F₂ : BraidedFunctor C D} (α : F₁ ⟶ F₂)
    (G : BraidedFunctor D E) :
    ((whiskeringRight C G).map α).hom = Functor.whiskerRight α.hom G.toFunctor :=
  (rfl)

/-- Left unitor isomorphism `(id C).comp F ≅ F` in `BraidedFunctor C D`. -/
def leftUnitor (F : BraidedFunctor C D) : (id C).comp F ≅ F :=
  isoMk F.toFunctor.leftUnitor

/-- Forward underlying natural transformation of `leftUnitor`. -/
@[simp]
theorem leftUnitor_hom_hom (F : BraidedFunctor C D) :
    (leftUnitor F).hom.hom = F.toFunctor.leftUnitor.hom :=
  (rfl)

/-- Inverse underlying natural transformation of `leftUnitor`. -/
@[simp]
theorem leftUnitor_inv_hom (F : BraidedFunctor C D) :
    (leftUnitor F).inv.hom = F.toFunctor.leftUnitor.inv :=
  (rfl)

/-- Right unitor isomorphism `F.comp (id D) ≅ F` in `BraidedFunctor C D`. -/
def rightUnitor (F : BraidedFunctor C D) : F.comp (id D) ≅ F :=
  isoMk F.toFunctor.rightUnitor

/-- Forward underlying natural transformation of `rightUnitor`. -/
@[simp]
theorem rightUnitor_hom_hom (F : BraidedFunctor C D) :
    (rightUnitor F).hom.hom = F.toFunctor.rightUnitor.hom :=
  (rfl)

/-- Inverse underlying natural transformation of `rightUnitor`. -/
@[simp]
theorem rightUnitor_inv_hom (F : BraidedFunctor C D) :
    (rightUnitor F).inv.hom = F.toFunctor.rightUnitor.inv :=
  (rfl)

/-- Associator isomorphism `(F.comp G).comp H ≅ F.comp (G.comp H)` in `BraidedFunctor C E'`. -/
def associator (F : BraidedFunctor C D) (G : BraidedFunctor D E) (H : BraidedFunctor E E') :
    (F.comp G).comp H ≅ F.comp (G.comp H) :=
  isoMk (Functor.associator F.toFunctor G.toFunctor H.toFunctor)

/-- Forward underlying natural transformation of `associator`. -/
@[simp]
theorem associator_hom_hom (F : BraidedFunctor C D) (G : BraidedFunctor D E)
    (H : BraidedFunctor E E') :
    (associator F G H).hom.hom = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom :=
  (rfl)

/-- Inverse underlying natural transformation of `associator`. -/
@[simp]
theorem associator_inv_hom (F : BraidedFunctor C D) (G : BraidedFunctor D E)
    (H : BraidedFunctor E E') :
    (associator F G H).inv.hom = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).inv :=
  (rfl)

end BraidedFunctor

end TauCeti
