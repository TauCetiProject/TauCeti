/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Functor
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic

/-!
# Pivotal-preserving strong braided functors and their category

A strong braided monoidal functor `F : C ⥤ D` between braided pivotal rigid categories is pivotal
(`CategoryTheory.Functor.IsPivotal`) when it carries the pivotal isomorphisms of `C` to those of `D`
along the bidual comparisons `κ_X = F.mapDoubleRightDualIso X`. Bundling such functors gives the
category `TauCeti.BraidedPivotalFunctor C D` with monoidal natural transformations as morphisms, and
its maximal subgroupoid `Core (BraidedPivotalFunctor C D)` of pivotal-preserving strong braided
functors and monoidal natural isomorphisms.

Because `CategoryTheory.Functor.IsPivotal` is a proposition and monoidal natural transformations
already commute with dual and bidual comparisons, no extra pivotal compatibility condition is
needed on morphisms: the forgetful functor `TauCeti.BraidedPivotalFunctor.forget` to
`TauCeti.BraidedFunctor C D` (and its induced functor on cores) is fully faithful. Between symmetric
rigid categories equipped with their canonical Drinfeld pivotal structures, every strong braided
functor is automatically pivotal (`CategoryTheory.Functor.isPivotal_of_braided`), so forgetting
pivotal preservation is an equivalence of categories
(`TauCeti.BraidedPivotalFunctor.symmetricEquiv`) and hence of functor groupoids.

## Main declarations

* `TauCeti.BraidedPivotalFunctor`: bundled pivotal-preserving strong braided monoidal functors, with
  category structure induced from `TauCeti.BraidedFunctor C D` and extensionality
  `TauCeti.BraidedPivotalFunctor.ext`;
* `TauCeti.BraidedPivotalFunctor.forget`: the fully faithful forgetful functor to
  `TauCeti.BraidedFunctor C D`;
* `TauCeti.BraidedPivotalFunctor.id`, `TauCeti.BraidedPivotalFunctor.comp`,
  `TauCeti.BraidedPivotalFunctor.whiskeringLeft`, and
  `TauCeti.BraidedPivotalFunctor.whiskeringRight`: identity, composition, and whiskering of
  pivotal-preserving strong braided functors;
* `TauCeti.BraidedPivotalFunctor.symmetricEquiv`: between symmetric rigid categories with their
  canonical pivotal structures, `BraidedPivotalFunctor C D ≌ BraidedFunctor C D`.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 8.10
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace TauCeti

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-- Bundled pivotal-preserving strong braided monoidal functors from `C` to `D`. Morphisms are
monoidal natural transformations, and `Core (BraidedPivotalFunctor C D)` is the groupoid of
pivotal-preserving strong braided functors and monoidal natural isomorphisms. -/
structure BraidedPivotalFunctor (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [BraidedCategory C] [RigidCategory C] [PivotalCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] [RigidCategory D]
    [PivotalCategory D] extends BraidedFunctor C D where
  /-- The underlying strong braided functor preserves the chosen pivotal structures. -/
  isPivotal : toFunctor.IsPivotal := by infer_instance

namespace BraidedPivotalFunctor

attribute [instance] isPivotal

section Pivotal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C] [PivotalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] [RigidCategory D]
  [PivotalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E] [RigidCategory E]
  [PivotalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E'] [BraidedCategory E'] [RigidCategory E']
  [PivotalCategory E']

/-- Bundle an unbundled pivotal-preserving strong braided functor `F : C ⥤ D`. -/
@[simps toBraidedFunctor]
abbrev of (F : C ⥤ D) [F.Braided] [F.IsPivotal] : BraidedPivotalFunctor C D where
  toBraidedFunctor := BraidedFunctor.of F

/-- A bundled pivotal-preserving strong braided functor is determined by its underlying strong
braided functor. -/
theorem toBraidedFunctor_injective :
    Function.Injective (toBraidedFunctor (C := C) (D := D)) := by
  rintro ⟨F, _⟩ ⟨G, _⟩ rfl
  rfl

/-- Two bundled pivotal-preserving strong braided functors agree when their underlying strong
braided functors agree. -/
@[ext]
theorem ext {F G : BraidedPivotalFunctor C D} (h : F.toBraidedFunctor = G.toBraidedFunctor) :
    F = G :=
  toBraidedFunctor_injective h

/-- Two bundled pivotal-preserving strong braided functors agree when their underlying lax monoidal
functors agree. -/
theorem ext_of_toLaxMonoidalFunctor {F G : BraidedPivotalFunctor C D}
    (h : F.toLaxMonoidalFunctor = G.toLaxMonoidalFunctor) : F = G :=
  ext (BraidedFunctor.ext h)

/-! ### Category structure and forgetful functor -/

instance : Category (BraidedPivotalFunctor C D) :=
  inferInstanceAs (Category (InducedCategory (BraidedFunctor C D) toBraidedFunctor))

/-- The underlying morphism in `BraidedFunctor C D` of `𝟙 F` is `𝟙 F.toBraidedFunctor`. -/
@[simp]
theorem id_hom (F : BraidedPivotalFunctor C D) :
    InducedCategory.Hom.hom (𝟙 F) = 𝟙 F.toBraidedFunctor :=
  (rfl)

/-- Composition of morphisms in `BraidedPivotalFunctor C D` is composition in
`BraidedFunctor C D`. -/
@[reassoc, simp]
theorem comp_hom {F G H : BraidedPivotalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom :=
  (rfl)

/-- Two morphisms of pivotal-preserving strong braided functors agree when their underlying natural
transformations agree. -/
@[ext]
theorem hom_ext {F G : BraidedPivotalFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) :
    α = β :=
  InducedCategory.hom_ext (BraidedFunctor.hom_ext h)

/-- Construct a morphism in `BraidedPivotalFunctor C D` from a monoidal natural transformation. -/
@[expose, simps! hom_hom]
def homMk {F G : BraidedPivotalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal f] : F ⟶ G :=
  InducedCategory.homMk (BraidedFunctor.homMk f)

/-- Construct an isomorphism in `BraidedPivotalFunctor C D` from a monoidal natural isomorphism. -/
@[expose, simps! hom_hom_hom inv_hom_hom]
def isoMk {F G : BraidedPivotalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G :=
  InducedCategory.isoMk (BraidedFunctor.isoMk e)

/-- Construct an isomorphism in `BraidedPivotalFunctor C D` from objectwise isomorphisms compatible
with morphisms, the unit comparison, and the tensor comparison. -/
@[expose, simps! hom_hom_hom_app inv_hom_hom_app]
def isoOfComponents {F G : BraidedPivotalFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  InducedCategory.isoMk (BraidedFunctor.isoOfComponents e naturality unit tensor)

section Forget

variable (C D)

/-- The fully faithful forgetful functor from pivotal-preserving strong braided functors to strong
braided functors. -/
@[expose, simps! obj map]
def forget : BraidedPivotalFunctor C D ⥤ BraidedFunctor C D :=
  inducedFunctor toBraidedFunctor

/-- Forgetting pivotal preservation is fully faithful. -/
def fullyFaithfulForget : (forget C D).FullyFaithful :=
  fullyFaithfulInducedFunctor toBraidedFunctor

instance : (forget C D).Full :=
  (fullyFaithfulForget C D).full

instance : (forget C D).Faithful :=
  (fullyFaithfulForget C D).faithful

end Forget

/-! ### Identity, composition, and whiskering -/

/-- The identity pivotal-preserving strong braided functor on `C`. -/
abbrev id (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] [PivotalCategory C] : BraidedPivotalFunctor C C :=
  of (𝟭 C)

/-- The composite of two bundled pivotal-preserving strong braided functors. -/
abbrev comp (F : BraidedPivotalFunctor C D) (G : BraidedPivotalFunctor D E) :
    BraidedPivotalFunctor C E :=
  of (F.toFunctor ⋙ G.toFunctor)

/-- Horizontal composition of morphisms of pivotal-preserving strong braided functors. -/
@[expose, simps! hom]
def hcomp {F₁ F₂ : BraidedPivotalFunctor C D} {G₁ G₂ : BraidedPivotalFunctor D E}
    (α : F₁ ⟶ F₂) (β : G₁ ⟶ G₂) : F₁.comp G₁ ⟶ F₂.comp G₂ :=
  InducedCategory.homMk (BraidedFunctor.hcomp α.hom β.hom)

/-- Precomposition with a pivotal-preserving strong braided functor `F`. -/
@[expose, simps! obj map_hom]
def whiskeringLeft (F : BraidedPivotalFunctor C D) (E : Type u₃) [Category.{v₃} E]
    [MonoidalCategory E] [BraidedCategory E] [RigidCategory E] [PivotalCategory E] :
    BraidedPivotalFunctor D E ⥤ BraidedPivotalFunctor C E where
  obj G := F.comp G
  map β := InducedCategory.homMk ((BraidedFunctor.whiskeringLeft F.toBraidedFunctor E).map β.hom)

/-- Precomposition commutes with forgetting to `BraidedFunctor`. -/
@[simp]
theorem whiskeringLeft_comp_forget (F : BraidedPivotalFunctor C D) :
    whiskeringLeft F E ⋙ forget C E =
      forget D E ⋙ BraidedFunctor.whiskeringLeft F.toBraidedFunctor E :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Postcomposition with a pivotal-preserving strong braided functor `G`. -/
@[expose, simps! obj map_hom]
def whiskeringRight (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
    [RigidCategory C] [PivotalCategory C] (G : BraidedPivotalFunctor D E) :
    BraidedPivotalFunctor C D ⥤ BraidedPivotalFunctor C E where
  obj F := F.comp G
  map α := InducedCategory.homMk ((BraidedFunctor.whiskeringRight C G.toBraidedFunctor).map α.hom)

/-- Postcomposition commutes with forgetting to `BraidedFunctor`. -/
@[simp]
theorem whiskeringRight_comp_forget (G : BraidedPivotalFunctor D E) :
    whiskeringRight C G ⋙ forget C E =
      forget C D ⋙ BraidedFunctor.whiskeringRight C G.toBraidedFunctor :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq rfl

/-- Left unitor isomorphism `(id C).comp F ≅ F` in `BraidedPivotalFunctor C D`. -/
@[expose, simps! hom_hom inv_hom]
def leftUnitor (F : BraidedPivotalFunctor C D) : (id C).comp F ≅ F :=
  InducedCategory.isoMk (BraidedFunctor.leftUnitor F.toBraidedFunctor)

/-- Right unitor isomorphism `F.comp (id D) ≅ F` in `BraidedPivotalFunctor C D`. -/
@[expose, simps! hom_hom inv_hom]
def rightUnitor (F : BraidedPivotalFunctor C D) : F.comp (id D) ≅ F :=
  InducedCategory.isoMk (BraidedFunctor.rightUnitor F.toBraidedFunctor)

/-- Associator isomorphism `(F.comp G).comp H ≅ F.comp (G.comp H)` in
`BraidedPivotalFunctor C E'`. -/
@[expose, simps! hom_hom inv_hom]
def associator (F : BraidedPivotalFunctor C D) (G : BraidedPivotalFunctor D E)
    (H : BraidedPivotalFunctor E E') :
    (F.comp G).comp H ≅ F.comp (G.comp H) :=
  InducedCategory.isoMk
    (BraidedFunctor.associator F.toBraidedFunctor G.toBraidedFunctor H.toBraidedFunctor)

end Pivotal

/-! ### Symmetric rigid categories -/

section Symmetric

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
  [RigidCategory C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D] [RigidCategory D]

/-- Every strong braided functor between symmetric rigid categories preserves their canonical
Drinfeld pivotal structures, giving a functor `BraidedFunctor C D ⥤ BraidedPivotalFunctor C D`. -/
@[expose, simps! obj_toBraidedFunctor map_hom]
noncomputable def ofSymmetricFunctor : BraidedFunctor C D ⥤ BraidedPivotalFunctor C D where
  obj F := { toBraidedFunctor := F }
  map α := InducedCategory.homMk α

/-- Between symmetric rigid categories with their canonical pivotal structures, pivotal-preserving
strong braided functors are equivalent to all strong braided functors. -/
@[expose, simps functor inverse]
noncomputable def symmetricEquiv : BraidedPivotalFunctor C D ≌ BraidedFunctor C D where
  functor := forget C D
  inverse := ofSymmetricFunctor C D
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.id_comp _

end Symmetric

end BraidedPivotalFunctor

end TauCeti
