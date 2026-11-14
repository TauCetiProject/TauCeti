/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Balanced.Basic
public import TauCeti.CategoryTheory.Monoidal.Braided.Functor

/-!
# Balanced functors and their category

A balanced functor is a strong braided monoidal functor preserving the chosen twists.
Preservation is stable under identity, composition, and natural isomorphism. In particular,
no additional equation on a monoidal natural isomorphism is needed to compare balanced
functors: ordinary naturality already intertwines the twists.

Bundling twist-preserving strong braided functors gives the category `TauCeti.BalancedFunctor C D`
with monoidal natural transformations as morphisms, and its maximal subgroupoid
`Core (BalancedFunctor C D)` of twist-preserving strong braided functors and monoidal natural
isomorphisms. Since `CategoryTheory.Functor.IsBalanced` is a property and morphisms require no
extra twist compatibility, the forgetful functor `TauCeti.BalancedFunctor.forget` to
`TauCeti.BraidedFunctor C D` (and its induced functor on cores) is fully faithful.

The convention for twists is that of `TauCeti.BalancedCategory`. These functors allow the
correspondence between pivotal and balanced structures to be used on morphisms and functor
groupoids as well.

## Main declarations

* `CategoryTheory.Functor.IsBalanced`: twist-preservation class on an unbundled strong braided
  functor, stable under identity, composition, and natural isomorphism;
* `TauCeti.BalancedFunctor`: bundled twist-preserving strong braided functors, with category
  structure induced from `TauCeti.BraidedFunctor C D` and extensionality
  `TauCeti.BalancedFunctor.ext`;
* `TauCeti.BalancedFunctor.forget`: the fully faithful forgetful functor to
  `TauCeti.BraidedFunctor C D`;
* `TauCeti.BalancedFunctor.id`, `TauCeti.BalancedFunctor.comp`,
  `TauCeti.BalancedFunctor.whiskeringLeft`, and `TauCeti.BalancedFunctor.whiskeringRight`:
  identity, composition, and whiskering of balanced functors, compatible with forgetting to
  `TauCeti.BraidedFunctor`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal TauCeti

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [BalancedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  [BalancedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  [BalancedCategory E]

/-- A strong braided monoidal functor is balanced when it preserves the chosen twists. -/
class IsBalanced (F : C ⥤ D) [F.Braided] : Prop where
  /-- The image of the source twist is the target twist. -/
  map_twist_hom_app (X : C) :
    F.map (BalancedCategory.twist.hom.app X) = BalancedCategory.twist.hom.app (F.obj X)

attribute [simp] IsBalanced.map_twist_hom_app

variable (F : C ⥤ D) [F.Braided]

/-- A balanced functor also preserves inverse twists. -/
@[simp]
theorem map_twist_inv_app [F.IsBalanced] (X : C) :
    F.map (BalancedCategory.twist.inv.app X) = BalancedCategory.twist.inv.app (F.obj X) := by
  apply (cancel_mono (BalancedCategory.twist.hom.app (F.obj X))).mp
  rw [← IsBalanced.map_twist_hom_app (F := F), ← F.map_comp]
  simp

/-- The identity braided functor preserves the twist. -/
instance isBalanced_id : (𝟭 C).IsBalanced where
  map_twist_hom_app _ := rfl

/-- A composite of balanced functors is balanced. -/
instance isBalanced_comp (G : D ⥤ E) [G.Braided] [F.IsBalanced] [G.IsBalanced] :
    (F ⋙ G).IsBalanced where
  map_twist_hom_app X := by simp

variable {F} {G : C ⥤ D} [G.Braided]

/-- Twist preservation transports along any natural isomorphism of braided functors.
The isomorphism need not itself be monoidal for this assertion. -/
theorem IsBalanced.of_iso (e : F ≅ G) [F.IsBalanced] : G.IsBalanced where
  map_twist_hom_app X := by
    apply (cancel_epi (e.hom.app X)).mp
    rw [← e.hom.naturality, IsBalanced.map_twist_hom_app]
    exact (BalancedCategory.twist.hom.naturality (e.hom.app X)).symm

/-- Naturally isomorphic braided functors preserve twists simultaneously. -/
theorem isBalanced_iff_of_iso (e : F ≅ G) : F.IsBalanced ↔ G.IsBalanced :=
  ⟨fun _ => IsBalanced.of_iso e, fun _ => IsBalanced.of_iso e.symm⟩

end CategoryTheory.Functor

namespace TauCeti

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- Bundled twist-preserving strong braided monoidal functors from `C` to `D`. Morphisms are
monoidal natural transformations, and `Core (BalancedFunctor C D)` is the groupoid of
twist-preserving strong braided functors and monoidal natural isomorphisms. -/
structure BalancedFunctor (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [BalancedCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] [BalancedCategory D]
    extends BraidedFunctor C D where
  /-- The underlying strong braided functor preserves the chosen twists. -/
  isBalanced : toFunctor.IsBalanced := by infer_instance

namespace BalancedFunctor

attribute [instance] isBalanced

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [BalancedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] [BalancedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E] [BalancedCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E'] [BraidedCategory E']
  [BalancedCategory E']

/-- Bundle an unbundled twist-preserving strong braided functor `F : C ⥤ D`. -/
abbrev of (F : C ⥤ D) [F.Braided] [F.IsBalanced] : BalancedFunctor C D where
  toFunctor := F

/-- The bundled strong braided functor underlying `BalancedFunctor.of F` is
`BraidedFunctor.of F`. -/
@[simp]
theorem of_toBraidedFunctor (F : C ⥤ D) [F.Braided] [F.IsBalanced] :
    (of F).toBraidedFunctor = BraidedFunctor.of F :=
  (rfl)

/-- The functor underlying `BalancedFunctor.of F` is `F`. -/
@[simp]
theorem of_toFunctor (F : C ⥤ D) [F.Braided] [F.IsBalanced] : (of F).toFunctor = F :=
  (rfl)

/-- A bundled balanced functor is determined by its underlying strong braided functor. -/
theorem toBraidedFunctor_injective :
    Function.Injective (toBraidedFunctor (C := C) (D := D)) := by
  rintro ⟨F, _⟩ ⟨G, _⟩ rfl
  rfl

/-- Two bundled balanced functors agree when their underlying strong braided functors agree. -/
@[ext]
theorem ext {F G : BalancedFunctor C D} (h : F.toBraidedFunctor = G.toBraidedFunctor) : F = G :=
  toBraidedFunctor_injective h

/-- Two bundled balanced functors agree when their underlying lax monoidal functors agree. -/
theorem ext_of_toLaxMonoidalFunctor {F G : BalancedFunctor C D}
    (h : F.toLaxMonoidalFunctor = G.toLaxMonoidalFunctor) : F = G :=
  ext (BraidedFunctor.ext h)

/-! ### Category structure and forgetful functor -/

instance : Category (BalancedFunctor C D) :=
  inferInstanceAs (Category (InducedCategory (BraidedFunctor C D) toBraidedFunctor))

/-- The underlying morphism in `BraidedFunctor C D` of `𝟙 F` is `𝟙 F.toBraidedFunctor`. -/
@[simp]
theorem id_hom (F : BalancedFunctor C D) :
    InducedCategory.Hom.hom (𝟙 F) = 𝟙 F.toBraidedFunctor :=
  (rfl)

/-- Composition of morphisms in `BalancedFunctor C D` is composition in `BraidedFunctor C D`. -/
@[reassoc, simp]
theorem comp_hom {F G H : BalancedFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom :=
  (rfl)

/-- Two morphisms of balanced functors agree when their underlying natural transformations agree. -/
@[ext]
theorem hom_ext {F G : BalancedFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) : α = β :=
  InducedCategory.hom_ext (BraidedFunctor.hom_ext h)

/-- Construct a morphism in `BalancedFunctor C D` from a monoidal natural transformation. -/
def homMk {F G : BalancedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G :=
  InducedCategory.homMk (BraidedFunctor.homMk f)

/-- `homMk` retains the supplied natural transformation. -/
@[simp]
theorem homMk_hom_hom {F G : BalancedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal f] : (homMk f).hom.hom = f :=
  BraidedFunctor.homMk_hom f

/-- Construct an isomorphism in `BalancedFunctor C D` from a monoidal natural isomorphism. -/
def isoMk {F G : BalancedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G :=
  InducedCategory.isoMk (BraidedFunctor.isoMk e)

/-- The forward morphism of `isoMk e` has underlying natural transformation `e.hom`. -/
@[simp]
theorem isoMk_hom_hom_hom {F G : BalancedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).hom.hom.hom = e.hom :=
  BraidedFunctor.isoMk_hom_hom e

/-- The inverse morphism of `isoMk e` has underlying natural transformation `e.inv`. -/
@[simp]
theorem isoMk_inv_hom_hom {F G : BalancedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).inv.hom.hom = e.inv :=
  BraidedFunctor.isoMk_inv_hom e

/-- Construct an isomorphism in `BalancedFunctor C D` from objectwise isomorphisms compatible with
morphisms, the unit comparison, and the tensor comparison. -/
def isoOfComponents {F G : BalancedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  InducedCategory.isoMk (BraidedFunctor.isoOfComponents e naturality unit tensor)

/-- The forward component at `X` of `isoOfComponents` is `(e X).hom`. -/
@[simp]
theorem isoOfComponents_hom_hom_hom_app {F G : BalancedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y) (X : C) :
    (isoOfComponents e naturality unit tensor).hom.hom.hom.app X = (e X).hom :=
  BraidedFunctor.isoOfComponents_hom_hom_app e naturality unit tensor X

/-- The inverse component at `X` of `isoOfComponents` is `(e X).inv`. -/
@[simp]
theorem isoOfComponents_inv_hom_hom_app {F G : BalancedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y) (X : C) :
    (isoOfComponents e naturality unit tensor).inv.hom.hom.app X = (e X).inv :=
  BraidedFunctor.isoOfComponents_inv_hom_app e naturality unit tensor X

section Forget

variable (C D)

/-- The fully faithful forgetful functor from balanced functors to strong braided functors. -/
@[expose]
def forget : BalancedFunctor C D ⥤ BraidedFunctor C D :=
  inducedFunctor toBraidedFunctor

/-- `forget` sends `F` to `F.toBraidedFunctor`. -/
@[simp]
theorem forget_obj (F : BalancedFunctor C D) :
    (forget C D).obj F = F.toBraidedFunctor :=
  (rfl)

/-- `forget` sends `α` to `α.hom`. -/
@[simp]
theorem forget_map {F G : BalancedFunctor C D} (α : F ⟶ G) :
    (forget C D).map α = α.hom :=
  (rfl)

/-- Forgetting twist preservation is fully faithful. -/
def fullyFaithfulForget : (forget C D).FullyFaithful :=
  fullyFaithfulInducedFunctor toBraidedFunctor

instance : (forget C D).Full :=
  (fullyFaithfulForget C D).full

instance : (forget C D).Faithful :=
  (fullyFaithfulForget C D).faithful

end Forget

/-! ### Identity, composition, and whiskering -/

/-- The identity balanced functor on `C`. -/
abbrev id (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [BalancedCategory C] : BalancedFunctor C C :=
  of (𝟭 C)

/-- The composite of two bundled balanced functors. -/
abbrev comp (F : BalancedFunctor C D) (G : BalancedFunctor D E) : BalancedFunctor C E :=
  of (F.toFunctor ⋙ G.toFunctor)

/-- Horizontal composition of morphisms of balanced functors. -/
def hcomp {F₁ F₂ : BalancedFunctor C D} {G₁ G₂ : BalancedFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : F₁.comp G₁ ⟶ F₂.comp G₂ :=
  InducedCategory.homMk (BraidedFunctor.hcomp α.hom β.hom)

/-- Horizontal composition acts through `BraidedFunctor.hcomp`. -/
@[simp]
theorem hcomp_hom {F₁ F₂ : BalancedFunctor C D} {G₁ G₂ : BalancedFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : (hcomp α β).hom = BraidedFunctor.hcomp α.hom β.hom :=
  (rfl)

/-- Precomposition with a balanced functor `F : BalancedFunctor C D`. -/
@[expose]
def whiskeringLeft (F : BalancedFunctor C D) (E : Type u₃) [Category.{v₃} E]
    [MonoidalCategory E] [BraidedCategory E] [BalancedCategory E] :
    BalancedFunctor D E ⥤ BalancedFunctor C E where
  obj G := F.comp G
  map β := InducedCategory.homMk ((BraidedFunctor.whiskeringLeft F.toBraidedFunctor E).map β.hom)

/-- `whiskeringLeft F E` acts on objects by `F.comp`. -/
@[simp]
theorem whiskeringLeft_obj (F : BalancedFunctor C D) (G : BalancedFunctor D E) :
    (whiskeringLeft F E).obj G = F.comp G :=
  (rfl)

/-- `whiskeringLeft F E` acts on morphisms via `BraidedFunctor.whiskeringLeft`. -/
@[simp]
theorem whiskeringLeft_map_hom (F : BalancedFunctor C D) {G₁ G₂ : BalancedFunctor D E}
    (β : G₁ ⟶ G₂) :
    ((whiskeringLeft F E).map β).hom =
      (BraidedFunctor.whiskeringLeft F.toBraidedFunctor E).map β.hom :=
  (rfl)

/-- Precomposition commutes with forgetting to `BraidedFunctor`. -/
@[simp]
theorem whiskeringLeft_comp_forget (F : BalancedFunctor C D) :
    whiskeringLeft F E ⋙ forget C E =
      forget D E ⋙ BraidedFunctor.whiskeringLeft F.toBraidedFunctor E :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Postcomposition with a balanced functor `G : BalancedFunctor D E`. -/
@[expose]
def whiskeringRight (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [BalancedCategory C] (G : BalancedFunctor D E) :
    BalancedFunctor C D ⥤ BalancedFunctor C E where
  obj F := F.comp G
  map α := InducedCategory.homMk ((BraidedFunctor.whiskeringRight C G.toBraidedFunctor).map α.hom)

/-- `whiskeringRight C G` acts on objects by `fun F ↦ F.comp G`. -/
@[simp]
theorem whiskeringRight_obj (F : BalancedFunctor C D) (G : BalancedFunctor D E) :
    (whiskeringRight C G).obj F = F.comp G :=
  (rfl)

/-- `whiskeringRight C G` acts on morphisms via `BraidedFunctor.whiskeringRight`. -/
@[simp]
theorem whiskeringRight_map_hom {F₁ F₂ : BalancedFunctor C D} (α : F₁ ⟶ F₂)
    (G : BalancedFunctor D E) :
    ((whiskeringRight C G).map α).hom =
      (BraidedFunctor.whiskeringRight C G.toBraidedFunctor).map α.hom :=
  (rfl)

/-- Postcomposition commutes with forgetting to `BraidedFunctor`. -/
@[simp]
theorem whiskeringRight_comp_forget (G : BalancedFunctor D E) :
    whiskeringRight C G ⋙ forget C E =
      forget C D ⋙ BraidedFunctor.whiskeringRight C G.toBraidedFunctor :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Left unitor isomorphism `(id C).comp F ≅ F` in `BalancedFunctor C D`. -/
def leftUnitor (F : BalancedFunctor C D) : (id C).comp F ≅ F :=
  InducedCategory.isoMk (BraidedFunctor.leftUnitor F.toBraidedFunctor)

/-- Forward underlying morphism of `leftUnitor`. -/
@[simp]
theorem leftUnitor_hom_hom (F : BalancedFunctor C D) :
    (leftUnitor F).hom.hom = (BraidedFunctor.leftUnitor F.toBraidedFunctor).hom :=
  (rfl)

/-- Inverse underlying morphism of `leftUnitor`. -/
@[simp]
theorem leftUnitor_inv_hom (F : BalancedFunctor C D) :
    (leftUnitor F).inv.hom = (BraidedFunctor.leftUnitor F.toBraidedFunctor).inv :=
  (rfl)

/-- Right unitor isomorphism `F.comp (id D) ≅ F` in `BalancedFunctor C D`. -/
def rightUnitor (F : BalancedFunctor C D) : F.comp (id D) ≅ F :=
  InducedCategory.isoMk (BraidedFunctor.rightUnitor F.toBraidedFunctor)

/-- Forward underlying morphism of `rightUnitor`. -/
@[simp]
theorem rightUnitor_hom_hom (F : BalancedFunctor C D) :
    (rightUnitor F).hom.hom = (BraidedFunctor.rightUnitor F.toBraidedFunctor).hom :=
  (rfl)

/-- Inverse underlying morphism of `rightUnitor`. -/
@[simp]
theorem rightUnitor_inv_hom (F : BalancedFunctor C D) :
    (rightUnitor F).inv.hom = (BraidedFunctor.rightUnitor F.toBraidedFunctor).inv :=
  (rfl)

/-- Associator isomorphism `(F.comp G).comp H ≅ F.comp (G.comp H)` in `BalancedFunctor C E'`. -/
def associator (F : BalancedFunctor C D) (G : BalancedFunctor D E) (H : BalancedFunctor E E') :
    (F.comp G).comp H ≅ F.comp (G.comp H) :=
  InducedCategory.isoMk
    (BraidedFunctor.associator F.toBraidedFunctor G.toBraidedFunctor H.toBraidedFunctor)

/-- Forward underlying morphism of `associator`. -/
@[simp]
theorem associator_hom_hom (F : BalancedFunctor C D) (G : BalancedFunctor D E)
    (H : BalancedFunctor E E') :
    (associator F G H).hom.hom =
      (BraidedFunctor.associator F.toBraidedFunctor G.toBraidedFunctor H.toBraidedFunctor).hom :=
  (rfl)

/-- Inverse underlying morphism of `associator`. -/
@[simp]
theorem associator_inv_hom (F : BalancedFunctor C D) (G : BalancedFunctor D E)
    (H : BalancedFunctor E E') :
    (associator F G H).inv.hom =
      (BraidedFunctor.associator F.toBraidedFunctor G.toBraidedFunctor H.toBraidedFunctor).inv :=
  (rfl)

end BalancedFunctor

end TauCeti
