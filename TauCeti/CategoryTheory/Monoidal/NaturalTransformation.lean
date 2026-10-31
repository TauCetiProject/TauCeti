/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural automorphisms

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

A natural transformation `τ : F ⟶ G` between strong monoidal functors whose component at the
unit is invertible is monoidal as soon as it is compatible with the tensor comparisons:
compatibility with the unit comparisons then follows from the unitality of `F` and `G`
(`CategoryTheory.NatTrans.IsMonoidal.of_tensor`). This applies in particular to natural
isomorphisms.
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

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A natural transformation between strong monoidal functors that is compatible with the tensor
comparisons, and whose component at the unit is invertible, is monoidal: compatibility with the
unit comparisons is automatic. -/
theorem of_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    [IsIso (τ.app (𝟙_ C))]
    (h : ∀ X Y : C, μ F X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y) :
    NatTrans.IsMonoidal τ where
  unit := by
    -- Left unitality of `F` and `G` and naturality of `τ` at `λ_ (𝟙_ C)` identify the
    -- whiskerings of both sides by `F.obj (𝟙_ C)`, after `G.obj (𝟙_ C) ◁ τ_𝟙`.
    have key : (ε F ≫ τ.app (𝟙_ C)) ▷ F.obj (𝟙_ C) ≫ G.obj (𝟙_ C) ◁ τ.app (𝟙_ C) =
        ε G ▷ F.obj (𝟙_ C) ≫ G.obj (𝟙_ C) ◁ τ.app (𝟙_ C) := by
      rw [← cancel_mono (μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom)]
      calc
        _ = ε F ▷ F.obj (𝟙_ C) ≫ μ F (𝟙_ C) (𝟙_ C) ≫ τ.app (𝟙_ C ⊗ 𝟙_ C) ≫
              G.map (λ_ (𝟙_ C)).hom := by
          rw [reassoc_of% h, tensorHom_def]; simp
        _ = (λ_ (F.obj (𝟙_ C))).hom ≫ τ.app (𝟙_ C) := by
          rw [← τ.naturality, Functor.LaxMonoidal.left_unitality]; simp
        _ = 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (λ_ (G.obj (𝟙_ C))).hom := (leftUnitor_naturality _).symm
        _ = _ := by rw [Functor.LaxMonoidal.left_unitality, whisker_exchange_assoc]; simp
    have hw : (ε F ≫ τ.app (𝟙_ C)) ▷ F.obj (𝟙_ C) = ε G ▷ F.obj (𝟙_ C) :=
      (cancel_mono _).1 key
    -- Whiskering by `F.obj (𝟙_ C) ≅ 𝟙_ D` is faithful.
    have hw' : (ε F ≫ τ.app (𝟙_ C)) ▷ 𝟙_ D = ε G ▷ 𝟙_ D := by
      rw [← cancel_epi (𝟙_ D ◁ η F), whisker_exchange, whisker_exchange, hw]
    rw [whiskerRight_id, whiskerRight_id, cancel_epi, cancel_mono] at hw'
    exact hw'
  tensor := h

end CategoryTheory.NatTrans.IsMonoidal
