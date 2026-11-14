/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural automorphisms and the category of strong monoidal functors

Mathlib makes the bundled lax monoidal functors `LaxMonoidalFunctor C D` into a category whose
morphisms are the monoidal natural transformations, so for a lax monoidal functor `F` the group
`Aut (LaxMonoidalFunctor.of F)` is the group of monoidal natural automorphisms of `F`. This file
adds the injective group homomorphism `CategoryTheory.LaxMonoidalFunctor.forgetAut F` to the
group `Aut F` of all natural automorphisms of `F`. Its values are typed as automorphisms of `F`
itself rather than of `(LaxMonoidalFunctor.of F).toFunctor`, so their components compose with
other morphisms out of `F.obj X` without unfolding `LaxMonoidalFunctor.of`.

The group `Aut (LaxMonoidalFunctor.of (𝟭 C))` of monoidal natural automorphisms of the identity
functor of a monoidal category, often written `Aut_⊗(𝟭_C)`, is commutative, like Mathlib's
centre `CategoryTheory.CatCenter C` of all natural endomorphisms of `𝟭 C`. It is the group
acting on the pivotal structures of a rigid monoidal category.

A natural transformation between lax monoidal functors that is an epimorphism at the tensor unit
and compatible with the tensorators is already monoidal: compatibility with the unit comparisons
follows (`CategoryTheory.NatTrans.IsMonoidal.of_tensor`).

Bundled strong monoidal functors `TauCeti.MonoidalFunctor C D`, with the monoidal natural
transformations as morphisms, embed fully faithfully into `LaxMonoidalFunctor C D`
(`TauCeti.MonoidalFunctor.fullyFaithfulForget`). Their isomorphisms are the monoidal natural
isomorphisms, so the core of this category is the groupoid of strong monoidal functors in which
universal properties of free monoidal categories are stated.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LaxMonoidalFunctor

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The underlying natural automorphism of a monoidal natural automorphism of a lax monoidal
functor `F`, as a group homomorphism `Aut (LaxMonoidalFunctor.of F) →* Aut F`. -/
def forgetAut (F : C ⥤ D) [F.LaxMonoidal] : Aut (LaxMonoidalFunctor.of F) →* Aut F where
  toFun u := Aut.of
    { hom := u.asIso.hom.hom
      inv := u.asIso.inv.hom
      hom_inv_id := congrArg Hom.hom u.asIso.hom_inv_id
      inv_hom_id := congrArg Hom.hom u.asIso.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F : C ⥤ D) [F.LaxMonoidal]

-- The right-hand sides below are typed through `(LaxMonoidalFunctor.of F).toFunctor`, which is
-- `F` only up to unfolding, so these are not `simp` lemmas: `forgetAut` is the normal form.

/-- The underlying natural transformation of `forgetAut F u` is that of `u`. -/
theorem forgetAut_apply_asIso_hom (u : Aut (LaxMonoidalFunctor.of F)) :
    (forgetAut F u).asIso.hom = u.asIso.hom.hom :=
  (rfl)

/-- The underlying natural transformation of the inverse of `forgetAut F u` is that of the
inverse of `u`. -/
theorem forgetAut_apply_asIso_inv (u : Aut (LaxMonoidalFunctor.of F)) :
    (forgetAut F u).asIso.inv = u.asIso.inv.hom :=
  (rfl)

/-- A monoidal natural automorphism is determined by its underlying natural automorphism. -/
theorem forgetAut_injective : Function.Injective (forgetAut F) := fun _ _ h ↦
  Aut.ext (Iso.ext (hom_ext (congrArg (fun w ↦ w.asIso.hom) h)))

/-- The underlying natural automorphism of a monoidal natural automorphism is monoidal. -/
instance isMonoidal_forgetAut_apply_asIso_hom (u : Aut (LaxMonoidalFunctor.of F)) :
    NatTrans.IsMonoidal (forgetAut F u).asIso.hom :=
  u.asIso.hom.isMonoidal

variable (C) in
/-- The monoidal natural automorphisms of the identity functor of a monoidal category commute. -/
instance : IsMulCommutative (Aut (LaxMonoidalFunctor.of (𝟭 C))) :=
  .of_comm fun u v ↦ Aut.ext (Iso.ext (hom_ext (NatTrans.id_comm v.asIso.hom.hom u.asIso.hom.hom)))

end CategoryTheory.LaxMonoidalFunctor

namespace CategoryTheory.NatTrans.IsMonoidal

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- **The unit condition follows from the tensor condition.** A natural transformation `τ` between
lax monoidal functors that is an epimorphism at the tensor unit and compatible with the
tensorators is monoidal. -/
theorem of_tensor {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G)
    [Epi (τ.app (𝟙_ C))]
    (h : ∀ X Y, μ F X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y) :
    τ.IsMonoidal where
  unit := by
    -- `G.obj (𝟙_ C)` is a monoid in `D` with multiplication
    -- `μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom` and unit `ε G`. Transporting the left
    -- unitality of `F` along the epimorphism `τ.app (𝟙_ C)` makes `ε F ≫ τ.app (𝟙_ C)` a left
    -- unit for this multiplication (`hl`), while `ε G` is a right unit (`hr`) because the two
    -- unitors of `𝟙_ C` agree; a left unit and a right unit of a multiplication are equal.
    have hl : (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) ≫ μ G (𝟙_ C) (𝟙_ C) ≫
        G.map (λ_ (𝟙_ C)).hom = (λ_ (G.obj (𝟙_ C))).hom := by
      have : Epi (𝟙_ D ◁ τ.app (𝟙_ C)) := by rw [id_whiskerLeft]; infer_instance
      rw [← cancel_epi (𝟙_ D ◁ τ.app (𝟙_ C))]
      have e : 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) =
          ε F ▷ F.obj (𝟙_ C) ≫ (τ.app (𝟙_ C) ⊗ₘ τ.app (𝟙_ C)) := by
        rw [comp_whiskerRight, ← Category.assoc, whisker_exchange, Category.assoc,
          ← tensorHom_def']
      calc 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) ≫
            μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom
          = ε F ▷ F.obj (𝟙_ C) ≫ (τ.app (𝟙_ C) ⊗ₘ τ.app (𝟙_ C)) ≫ μ G (𝟙_ C) (𝟙_ C) ≫
              G.map (λ_ (𝟙_ C)).hom := by rw [← Category.assoc, e, Category.assoc]
        _ = ε F ▷ F.obj (𝟙_ C) ≫ μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom ≫
              τ.app (𝟙_ C) := by
            rw [← reassoc_of% h, τ.naturality]
        _ = (λ_ (F.obj (𝟙_ C))).hom ≫ τ.app (𝟙_ C) := by rw [← left_unitality_assoc]
        _ = 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (λ_ (G.obj (𝟙_ C))).hom := by rw [leftUnitor_naturality]
    have hr : G.obj (𝟙_ C) ◁ ε G ≫ μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom =
        (ρ_ (G.obj (𝟙_ C))).hom := by
      rw [unitors_equal, right_unitality]
    calc ε F ≫ τ.app (𝟙_ C)
        = (λ_ (𝟙_ D)).inv ≫ (ε F ≫ τ.app (𝟙_ C)) ▷ 𝟙_ D ≫ (ρ_ (G.obj (𝟙_ C))).hom := by
          rw [rightUnitor_naturality, unitors_inv_equal, Iso.inv_hom_id_assoc]
      _ = (λ_ (𝟙_ D)).inv ≫ 𝟙_ D ◁ ε G ≫ (λ_ (G.obj (𝟙_ C))).hom := by
          rw [← hr, ← whisker_exchange_assoc, hl]
      _ = ε G := by rw [leftUnitor_naturality, Iso.inv_hom_id_assoc]
  tensor := h

end CategoryTheory.NatTrans.IsMonoidal

namespace TauCeti

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]

/-- Bundled strong monoidal functors. They form a category whose morphisms are the monoidal
natural transformations, which embeds fully faithfully into `LaxMonoidalFunctor C D`. -/
structure MonoidalFunctor extends C ⥤ D where
  /-- The strong monoidal structure of the underlying functor. -/
  monoidal : toFunctor.Monoidal := by infer_instance

namespace MonoidalFunctor

attribute [instance] monoidal

variable {C D}

/-- Constructor for `MonoidalFunctor C D`. -/
@[expose, simps toFunctor]
def of (F : C ⥤ D) [F.Monoidal] : MonoidalFunctor C D where
  toFunctor := F

/-- The underlying lax monoidal functor of a strong monoidal functor. -/
@[expose, simps! toFunctor]
def toLaxMonoidalFunctor (F : MonoidalFunctor C D) : LaxMonoidalFunctor C D :=
  LaxMonoidalFunctor.of F.toFunctor

/-- The type of monoidal natural transformations between strong monoidal functors. -/
@[ext]
structure Hom (F G : MonoidalFunctor C D) where
  /-- The underlying natural transformation. -/
  hom : F.toFunctor ⟶ G.toFunctor
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal

/-- Strong monoidal functors and monoidal natural transformations. -/
instance : Category (MonoidalFunctor C D) where
  Hom := Hom
  comp α β := ⟨α.hom ≫ β.hom, inferInstance⟩
  id _ := ⟨𝟙 _, inferInstance⟩

@[ext]
theorem hom_ext {F G : MonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β :=
  Hom.ext h

@[simp]
theorem id_hom (F : MonoidalFunctor C D) : Hom.hom (𝟙 F) = 𝟙 F.toFunctor :=
  (rfl)

@[reassoc, simp]
theorem comp_hom {F G H : MonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom :=
  (rfl)

/-- Constructor for morphisms of strong monoidal functors. -/
@[expose, simps]
def homMk {F G : MonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G :=
  ⟨f, inferInstance⟩

/-- Constructor for isomorphisms of strong monoidal functors. -/
@[expose, simps]
def isoMk {F G : MonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

variable (C D) in
/-- The forgetful functor from strong to lax monoidal functors. -/
@[expose, simps]
def forget : MonoidalFunctor C D ⥤ LaxMonoidalFunctor C D where
  obj F := F.toLaxMonoidalFunctor
  map α := ⟨α.hom, α.isMonoidal⟩

variable (C D) in
/-- The forgetful functor from strong to lax monoidal functors is fully faithful. -/
def fullyFaithfulForget : (forget C D).FullyFaithful where
  preimage α := ⟨α.hom, α.isMonoidal⟩

instance : (forget C D).Full :=
  (fullyFaithfulForget C D).full

instance : (forget C D).Faithful :=
  (fullyFaithfulForget C D).faithful

/-- The natural isomorphism between the underlying functors of an isomorphism of strong monoidal
functors. -/
@[expose, simps]
def toFunctorIso {F G : MonoidalFunctor C D} (e : F ≅ G) : F.toFunctor ≅ G.toFunctor where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by rw [← comp_hom, e.hom_inv_id, id_hom]
  inv_hom_id := by rw [← comp_hom, e.inv_hom_id, id_hom]

instance {F G : MonoidalFunctor C D} (e : F ≅ G) : NatTrans.IsMonoidal (toFunctorIso e).hom :=
  e.hom.isMonoidal

end MonoidalFunctor

end TauCeti
