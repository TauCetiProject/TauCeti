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
  functor, stable under identity (`CategoryTheory.Functor.isBalanced_id`, with
  `CategoryTheory.Functor.isBalanced_id_iff_eq` characterizing identity preservation between two
  balanced structures), composition, and natural isomorphism;
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

/-- The identity braided functor `𝟭 C` is balanced from `B₁` to `B₂` if and only if `B₁ = B₂`. -/
@[simp]
theorem isBalanced_id_iff_eq {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [BraidedCategory C] (B₁ B₂ : BalancedCategory C) :
    @IsBalanced C _ _ _ B₁ C _ _ _ B₂ (𝟭 C) _ ↔ B₁ = B₂ := by
  constructor
  · intro h
    apply BalancedCategory.ext
    ext X
    exact h.map_twist_hom_app X
  · rintro rfl
    let := B₁
    infer_instance

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
@[simps toBraidedFunctor]
abbrev of (F : C ⥤ D) [F.Braided] [F.IsBalanced] : BalancedFunctor C D where
  toBraidedFunctor := BraidedFunctor.of F

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
@[expose, simps! hom_hom]
def homMk {F G : BalancedFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G :=
  InducedCategory.homMk (BraidedFunctor.homMk f)

/-- Construct an isomorphism in `BalancedFunctor C D` from a monoidal natural isomorphism. -/
@[expose, simps! hom_hom_hom inv_hom_hom]
def isoMk {F G : BalancedFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G :=
  InducedCategory.isoMk (BraidedFunctor.isoMk e)

/-- Construct an isomorphism in `BalancedFunctor C D` from objectwise isomorphisms compatible with
morphisms, the unit comparison, and the tensor comparison. -/
@[expose, simps! hom_hom_hom_app inv_hom_hom_app]
def isoOfComponents {F G : BalancedFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  InducedCategory.isoMk (BraidedFunctor.isoOfComponents e naturality unit tensor)

section Forget

variable (C D)

/-- The fully faithful forgetful functor from balanced functors to strong braided functors. -/
@[expose, simps! obj map]
def forget : BalancedFunctor C D ⥤ BraidedFunctor C D :=
  inducedFunctor toBraidedFunctor

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
@[expose, simps! hom]
def hcomp {F₁ F₂ : BalancedFunctor C D} {G₁ G₂ : BalancedFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : F₁.comp G₁ ⟶ F₂.comp G₂ :=
  InducedCategory.homMk (BraidedFunctor.hcomp α.hom β.hom)

/-- Precomposition with a balanced functor `F : BalancedFunctor C D`. -/
@[expose, simps! obj map_hom]
def whiskeringLeft (F : BalancedFunctor C D) (E : Type u₃) [Category.{v₃} E]
    [MonoidalCategory E] [BraidedCategory E] [BalancedCategory E] :
    BalancedFunctor D E ⥤ BalancedFunctor C E where
  obj G := F.comp G
  map β := InducedCategory.homMk ((BraidedFunctor.whiskeringLeft F.toBraidedFunctor E).map β.hom)

/-- Precomposition commutes with forgetting to `BraidedFunctor`. -/
@[simp]
theorem whiskeringLeft_comp_forget (F : BalancedFunctor C D) :
    whiskeringLeft F E ⋙ forget C E =
      forget D E ⋙ BraidedFunctor.whiskeringLeft F.toBraidedFunctor E :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Postcomposition with a balanced functor `G : BalancedFunctor D E`. -/
@[expose, simps! obj map_hom]
def whiskeringRight (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [BalancedCategory C] (G : BalancedFunctor D E) :
    BalancedFunctor C D ⥤ BalancedFunctor C E where
  obj F := F.comp G
  map α := InducedCategory.homMk ((BraidedFunctor.whiskeringRight C G.toBraidedFunctor).map α.hom)

/-- Postcomposition commutes with forgetting to `BraidedFunctor`. -/
@[simp]
theorem whiskeringRight_comp_forget (G : BalancedFunctor D E) :
    whiskeringRight C G ⋙ forget C E =
      forget C D ⋙ BraidedFunctor.whiskeringRight C G.toBraidedFunctor :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Left unitor isomorphism `(id C).comp F ≅ F` in `BalancedFunctor C D`. -/
@[expose, simps! hom_hom inv_hom]
def leftUnitor (F : BalancedFunctor C D) : (id C).comp F ≅ F :=
  InducedCategory.isoMk (BraidedFunctor.leftUnitor F.toBraidedFunctor)

/-- Right unitor isomorphism `F.comp (id D) ≅ F` in `BalancedFunctor C D`. -/
@[expose, simps! hom_hom inv_hom]
def rightUnitor (F : BalancedFunctor C D) : F.comp (id D) ≅ F :=
  InducedCategory.isoMk (BraidedFunctor.rightUnitor F.toBraidedFunctor)

/-- Associator isomorphism `(F.comp G).comp H ≅ F.comp (G.comp H)` in `BalancedFunctor C E'`. -/
@[expose, simps! hom_hom inv_hom]
def associator (F : BalancedFunctor C D) (G : BalancedFunctor D E) (H : BalancedFunctor E E') :
    (F.comp G).comp H ≅ F.comp (G.comp H) :=
  InducedCategory.isoMk
    (BraidedFunctor.associator F.toBraidedFunctor G.toBraidedFunctor H.toBraidedFunctor)

end BalancedFunctor

end TauCeti
