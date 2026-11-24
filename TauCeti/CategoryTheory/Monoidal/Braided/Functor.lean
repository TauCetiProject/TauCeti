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
@[simps toFunctor]
abbrev of (F : C ⥤ D) [F.Braided] : BraidedFunctor C D where
  toFunctor := F

/-- The bundled lax braided functor underlying a strong braided functor. -/
@[simps toFunctor]
abbrev toLaxBraidedFunctor (F : BraidedFunctor C D) : LaxBraidedFunctor C D where
  toFunctor := F.toFunctor

/-- The bundled lax monoidal functor underlying a strong braided functor. -/
@[simps toFunctor]
abbrev toLaxMonoidalFunctor (F : BraidedFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor

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
@[expose, simps]
def homMk {F G : BraidedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G :=
  ⟨f, inferInstance⟩

/-- Construct an isomorphism in `BraidedFunctor C D` from a monoidal natural isomorphism. -/
@[expose, simps! hom_hom inv_hom]
def isoMk {F G : BraidedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

/-- Construct an isomorphism in `BraidedFunctor C D` from objectwise isomorphisms compatible with
morphisms, the unit comparison, and the tensor comparison. -/
@[expose, simps! hom_hom_app inv_hom_app]
def isoOfComponents {F G : BraidedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  @isoMk _ _ _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) ⟨unit, tensor⟩

/-! ### Forgetful functors -/

section Forget

variable (C D)

/-- The faithful forgetful functor from strong braided functors to ordinary functors. -/
@[expose, simps]
def forgetToFunctor : BraidedFunctor C D ⥤ C ⥤ D where
  obj F := F.toFunctor
  map α := α.hom

instance : (forgetToFunctor C D).Faithful where
  map_injective h := hom_ext h

/-- The fully faithful forgetful functor from strong braided functors to lax monoidal functors. -/
@[expose, simps obj map_hom]
def forgetToLaxMonoidal : BraidedFunctor C D ⥤ LaxMonoidalFunctor C D where
  obj F := F.toLaxMonoidalFunctor
  map α := ⟨α.hom, α.isMonoidal⟩

/-- Forgetting from strong braided functors to lax monoidal functors is fully faithful. -/
def fullyFaithfulForgetToLaxMonoidal : (forgetToLaxMonoidal C D).FullyFaithful where
  preimage f := ⟨f.hom, f.isMonoidal⟩

instance : (forgetToLaxMonoidal C D).Full :=
  (fullyFaithfulForgetToLaxMonoidal C D).full

instance : (forgetToLaxMonoidal C D).Faithful :=
  (fullyFaithfulForgetToLaxMonoidal C D).faithful

/-- The fully faithful forgetful functor from strong braided functors to lax braided functors. -/
@[expose, simps! obj map_hom_hom]
def forgetToLaxBraided : BraidedFunctor C D ⥤ LaxBraidedFunctor C D where
  obj F := F.toLaxBraidedFunctor
  map α := InducedCategory.homMk ⟨α.hom, α.isMonoidal⟩

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
@[expose, simps!]
def hcomp {F₁ F₂ : BraidedFunctor C D} {G₁ G₂ : BraidedFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : F₁.comp G₁ ⟶ F₂.comp G₂ :=
  homMk (α.hom ◫ β.hom)

/-- Precomposition with a strong braided functor `F : BraidedFunctor C D`. -/
@[expose, simps! obj map_hom]
def whiskeringLeft (F : BraidedFunctor C D)
    (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E] :
    BraidedFunctor D E ⥤ BraidedFunctor C E where
  obj G := F.comp G
  map β := homMk (Functor.whiskerLeft F.toFunctor β.hom)

/-- Postcomposition with a strong braided functor `G : BraidedFunctor D E`. -/
@[expose, simps! obj map_hom]
def whiskeringRight (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    (G : BraidedFunctor D E) :
    BraidedFunctor C D ⥤ BraidedFunctor C E where
  obj F := F.comp G
  map α := homMk (Functor.whiskerRight α.hom G.toFunctor)

/-- Left unitor isomorphism `(id C).comp F ≅ F` in `BraidedFunctor C D`. -/
@[expose, simps! hom_hom inv_hom]
def leftUnitor (F : BraidedFunctor C D) : (id C).comp F ≅ F :=
  isoMk F.toFunctor.leftUnitor

/-- Right unitor isomorphism `F.comp (id D) ≅ F` in `BraidedFunctor C D`. -/
@[expose, simps! hom_hom inv_hom]
def rightUnitor (F : BraidedFunctor C D) : F.comp (id D) ≅ F :=
  isoMk F.toFunctor.rightUnitor

/-- Associator isomorphism `(F.comp G).comp H ≅ F.comp (G.comp H)` in `BraidedFunctor C E'`. -/
@[expose, simps! hom_hom inv_hom]
def associator (F : BraidedFunctor C D) (G : BraidedFunctor D E) (H : BraidedFunctor E E') :
    (F.comp G).comp H ≅ F.comp (G.comp H) :=
  isoMk (Functor.associator F.toFunctor G.toFunctor H.toFunctor)

end BraidedFunctor

end TauCeti
