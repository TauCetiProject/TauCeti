/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
# Composition, natural transformations and equivalences of left-linear functors

Let a monoidal category `C` act on the left on categories `D`, `D'`, `D''`. Mathlib's
`Functor.LaxLeftLinear`, `Functor.OplaxLeftLinear` and `Functor.LeftLinear` equip a functor with
lineators `μₗ F c d : c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)` and `δₗ F c d` in the other direction. For a
group `G`, a left-linear functor between categories with an action of `Discrete G` is a
`G`-equivariant functor, with commutation isomorphisms satisfying the unit and product
diagrams. This file develops the structure these functors form:

* the identity functor is (lax, oplax) left-linear with identity lineators, and composites of
  (lax, oplax) left-linear functors are (lax, oplax) left-linear (`Functor.LaxLeftLinear.comp`,
  `Functor.OplaxLeftLinear.comp`, `Functor.LeftLinear.comp`);
* `Functor.LeftLinear.ofLaxLeftLinear`: a lax left-linear functor with invertible lineators is
  left-linear;
* `NatTrans.IsLeftLinear`: a natural transformation between lax left-linear functors is
  left-linear (equivariant) when it commutes with the lineators. These are closed under
  identities, vertical and horizontal composition, whiskering and inverses, and the unitors and
  associators of functor composition are left-linear. Between left-linear functors, it is
  equivalent to commute with the oplax lineators (`app_comp_δₗ`, `of_app_comp_δₗ`);
* `Adjunction.rightAdjointLaxLeftLinear`: the right adjoint of an oplax left-linear functor is lax
  left-linear; when the left adjoint is left-linear, the unit and counit are left-linear;
* `Equivalence.inverseLeftLinear`: the inverse of a left-linear equivalence is left-linear, and
  the unit and counit of the equivalence are then left-linear, so that an equivalence whose
  functor is equivariant is an equivalence of categories with an action.

The constructions follow their monoidal counterparts in Mathlib: `Functor.LaxMonoidal.comp`,
`NatTrans.IsMonoidal`, `Adjunction.rightAdjointLaxMonoidal` and `Equivalence.inverseMonoidal`.
-/

public section

namespace CategoryTheory.Functor

open MonoidalCategory MonoidalLeftAction

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalLeftAction C D]
  {D' : Type*} [Category* D'] [MonoidalLeftAction C D']
  {D'' : Type*} [Category* D''] [MonoidalLeftAction C D'']

namespace LaxLeftLinear

variable (C D) in
/-- The identity functor is lax left-linear, with identity lineators. -/
@[simps]
instance id : (𝟭 D).LaxLeftLinear C where
  μₗ _ _ := 𝟙 _

variable (F : D ⥤ D') (G : D' ⥤ D'') [F.LaxLeftLinear C] [G.LaxLeftLinear C]

/-- The composite of lax left-linear functors is lax left-linear: the lineator of `F ⋙ G` at
`c` and `d` is `μₗ G c (F.obj d) ≫ G.map (μₗ F c d)`. -/
@[simps]
instance comp : (F ⋙ G).LaxLeftLinear C where
  μₗ c d := μₗ G c (F.obj d) ≫ G.map (μₗ F c d)
  μₗ_naturality_left f d := by
    simp_rw [comp_obj, comp_map, μₗ_naturality_left_assoc, Category.assoc, ← G.map_comp,
      μₗ_naturality_left]
  μₗ_naturality_right c _ _ f := by
    simp_rw [comp_obj, comp_map, μₗ_naturality_right_assoc, Category.assoc, ← G.map_comp,
      μₗ_naturality_right]
  μₗ_associativity c c' d := by
    simp only [comp_obj, comp_map, Category.assoc, actionHomRight_comp,
      μₗ_naturality_right_assoc, ← μₗ_associativity_assoc G, ← G.map_comp, μₗ_associativity]
  μₗ_unitality d := by
    simp only [comp_obj, comp_map, Category.assoc, ← G.map_comp, ← μₗ_unitality,
      ← μₗ_unitality G]

end LaxLeftLinear

namespace OplaxLeftLinear

variable (C D) in
/-- The identity functor is oplax left-linear, with identity lineators. -/
@[simps]
instance id : (𝟭 D).OplaxLeftLinear C where
  δₗ _ _ := 𝟙 _

variable (F : D ⥤ D') (G : D' ⥤ D'') [F.OplaxLeftLinear C] [G.OplaxLeftLinear C]

/-- The composite of oplax left-linear functors is oplax left-linear: the lineator of `F ⋙ G`
at `c` and `d` is `G.map (δₗ F c d) ≫ δₗ G c (F.obj d)`. -/
@[simps]
instance comp : (F ⋙ G).OplaxLeftLinear C where
  δₗ c d := G.map (δₗ F c d) ≫ δₗ G c (F.obj d)
  δₗ_naturality_left f d := by
    simp_rw [comp_obj, comp_map, ← G.map_comp_assoc, δₗ_naturality_left, G.map_comp,
      Category.assoc, δₗ_naturality_left]
  δₗ_naturality_right c _ _ f := by
    simp_rw [comp_obj, comp_map, ← G.map_comp_assoc, δₗ_naturality_right, G.map_comp,
      Category.assoc, δₗ_naturality_right]
  δₗ_associativity c c' d := by
    simp only [comp_obj, comp_map, Category.assoc, δₗ_associativity, ← G.map_comp_assoc,
      actionHomRight_comp, ← δₗ_naturality_right_assoc]
  δₗ_unitality_inv d := by
    simp only [comp_obj, comp_map, δₗ_unitality_inv G, δₗ_unitality_inv F d, G.map_comp,
      Category.assoc]

end OplaxLeftLinear

namespace LeftLinear

open LaxLeftLinear OplaxLeftLinear

variable (C D) in
/-- The identity functor is left-linear, with identity lineators. -/
instance id : (𝟭 D).LeftLinear C where
  μₗ_comp_δₗ _ _ := Category.id_comp _
  δₗ_comp_μₗ _ _ := Category.id_comp _

/-- A lax left-linear functor whose lineators `μₗ F c d` are isomorphisms is left-linear, with
oplax lineators their inverses. -/
@[instance_reducible]
noncomputable def ofLaxLeftLinear (F : D ⥤ D') [F.LaxLeftLinear C]
    [∀ (c : C) (d : D), IsIso (μₗ F c d)] : F.LeftLinear C where
  δₗ c d := CategoryTheory.inv (μₗ F c d)
  δₗ_naturality_left f d := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, μₗ_naturality_left]
  δₗ_naturality_right c _ _ f := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, μₗ_naturality_right]
  δₗ_associativity c c' d := by
    rw [← cancel_epi (μₗ F (c ⊗ c') d)]
    simp
  δₗ_unitality_inv d := by
    rw [IsIso.eq_comp_inv, μₗ_unitality_inv]
  μₗ_comp_δₗ _ _ := IsIso.hom_inv_id _
  δₗ_comp_μₗ _ _ := IsIso.inv_hom_id _

/-- The oplax lineators of `LeftLinear.ofLaxLeftLinear F` are the inverses of the lax ones. -/
lemma ofLaxLeftLinear_δₗ (F : D ⥤ D') [F.LaxLeftLinear C] [∀ (c : C) (d : D), IsIso (μₗ F c d)]
    (c : C) (d : D) :
    letI := ofLaxLeftLinear (C := C) F
    δₗ F c d = CategoryTheory.inv (μₗ F c d) := by
  rfl

section comp

variable (F : D ⥤ D') (G : D' ⥤ D'') [F.LeftLinear C] [G.LeftLinear C]

/-- The composite of left-linear functors is left-linear, with the lineators of
`LaxLeftLinear.comp` and `OplaxLeftLinear.comp`. -/
instance comp : (F ⋙ G).LeftLinear C where
  μₗ_comp_δₗ c d := by simp [← G.map_comp_assoc]
  δₗ_comp_μₗ c d := by simp [← G.map_comp]

end comp

end LeftLinear

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {D : Type*} [Category* D] {D' : Type*} [Category* D']

/-- A natural transformation `τ : F₁ ⟶ F₂` between lax left-linear functors is left-linear
(equivariant) if it commutes with the lineators:
`μₗ F₁ c d ≫ τ.app (c ⊙ₗ d) = c ⊴ₗ τ.app d ≫ μₗ F₂ c d`. -/
class IsLeftLinear {F₁ F₂ : D ⥤ D'} (τ : F₁ ⟶ F₂) (C : Type*) [Category* C]
    [MonoidalCategory C] [MonoidalLeftAction C D] [MonoidalLeftAction C D']
    [F₁.LaxLeftLinear C] [F₂.LaxLeftLinear C] : Prop where
  μₗ_comp_app (τ) (c : C) (d : D) :
    μₗ F₁ c d ≫ τ.app (c ⊙ₗ d) = c ⊴ₗ τ.app d ≫ μₗ F₂ c d := by cat_disch

namespace IsLeftLinear

attribute [reassoc (attr := simp)] μₗ_comp_app

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalLeftAction C D]
  [MonoidalLeftAction C D'] {D'' : Type*} [Category* D''] [MonoidalLeftAction C D'']
  {F₁ F₂ F₃ : D ⥤ D'} [F₁.LaxLeftLinear C] [F₂.LaxLeftLinear C] [F₃.LaxLeftLinear C]
  (τ : F₁ ⟶ F₂)

/-- The identity natural transformation is left-linear. -/
instance id : IsLeftLinear (𝟙 F₁) C where

/-- The vertical composite of left-linear natural transformations is left-linear. -/
instance comp (τ' : F₂ ⟶ F₃) [IsLeftLinear τ C] [IsLeftLinear τ' C] :
    IsLeftLinear (τ ≫ τ') C where
  μₗ_comp_app c d := by simp

/-- The horizontal composite of left-linear natural transformations is left-linear, for the
left-linear structures of `Functor.LaxLeftLinear.comp`. -/
instance hcomp {G₁ G₂ : D' ⥤ D''} [G₁.LaxLeftLinear C] [G₂.LaxLeftLinear C] (τ' : G₁ ⟶ G₂)
    [IsLeftLinear τ C] [IsLeftLinear τ' C] : IsLeftLinear (τ ◫ τ') C where
  μₗ_comp_app c d := by simp [← Functor.map_comp]

instance whiskerRight {G : D' ⥤ D''} [G.LaxLeftLinear C] [IsLeftLinear τ C] :
    IsLeftLinear (Functor.whiskerRight τ G) C := by
  rw [← Functor.hcomp_id]
  infer_instance

instance whiskerLeft {G₁ G₂ : D' ⥤ D''} [G₁.LaxLeftLinear C] [G₂.LaxLeftLinear C]
    (τ' : G₁ ⟶ G₂) [IsLeftLinear τ' C] : IsLeftLinear (Functor.whiskerLeft F₁ τ') C := by
  rw [← Functor.id_hcomp]
  infer_instance

instance (F : D ⥤ D') [F.LaxLeftLinear C] : IsLeftLinear F.leftUnitor.hom C where

instance (F : D ⥤ D') [F.LaxLeftLinear C] : IsLeftLinear F.rightUnitor.hom C where

instance {D''' : Type*} [Category* D'''] [MonoidalLeftAction C D'''] (F : D ⥤ D') (G : D' ⥤ D'')
    (H : D'' ⥤ D''') [F.LaxLeftLinear C] [G.LaxLeftLinear C] [H.LaxLeftLinear C] :
    IsLeftLinear (Functor.associator F G H).hom C where

/-- For left-linear functors, a left-linear natural transformation also commutes with the oplax
lineators `δₗ`. -/
@[reassoc]
lemma app_comp_δₗ {F₁ F₂ : D ⥤ D'} [F₁.LeftLinear C] [F₂.LeftLinear C] (τ : F₁ ⟶ F₂)
    [IsLeftLinear τ C] (c : C) (d : D) :
    τ.app (c ⊙ₗ d) ≫ δₗ F₂ c d = δₗ F₁ c d ≫ c ⊴ₗ τ.app d := by
  rw [← cancel_epi (μₗ F₁ c d), μₗ_comp_app_assoc]
  simp

/-- For left-linear functors, a natural transformation that commutes with the oplax lineators
`δₗ` is left-linear. -/
lemma of_app_comp_δₗ {F₁ F₂ : D ⥤ D'} [F₁.LeftLinear C] [F₂.LeftLinear C] (τ : F₁ ⟶ F₂)
    (h : ∀ (c : C) (d : D), τ.app (c ⊙ₗ d) ≫ δₗ F₂ c d = δₗ F₁ c d ≫ c ⊴ₗ τ.app d) :
    IsLeftLinear τ C where
  μₗ_comp_app c d := by
    rw [← cancel_mono (δₗ F₂ c d), Category.assoc, h]
    simp

end IsLeftLinear

end CategoryTheory.NatTrans

namespace CategoryTheory.Iso

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalLeftAction C D]
  {D' : Type*} [Category* D'] [MonoidalLeftAction C D']
  {F₁ F₂ : D ⥤ D'} [F₁.LaxLeftLinear C] [F₂.LaxLeftLinear C]

/-- The inverse of a natural isomorphism whose forward map is left-linear is left-linear. -/
instance (e : F₁ ≅ F₂) [NatTrans.IsLeftLinear e.hom C] :
    NatTrans.IsLeftLinear e.inv C where
  μₗ_comp_app c d := by
    rw [← cancel_mono (e.hom.app (c ⊙ₗ d))]
    simp [← actionHomRight_comp_assoc]

end CategoryTheory.Iso

namespace CategoryTheory.Adjunction

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalLeftAction C D]
  {D' : Type*} [Category* D'] [MonoidalLeftAction C D']
  {F : D ⥤ D'} {G : D' ⥤ D} (adj : F ⊣ G)

variable (C) in
/-- The right adjoint of an oplax left-linear functor is lax left-linear: the lineator
`μₗ G c d : c ⊙ₗ G.obj d ⟶ G.obj (c ⊙ₗ d)` is the adjoint of
`δₗ F c (G.obj d) ≫ c ⊴ₗ adj.counit.app d : F.obj (c ⊙ₗ G.obj d) ⟶ c ⊙ₗ d`. -/
@[instance_reducible]
def rightAdjointLaxLeftLinear [F.OplaxLeftLinear C] : G.LaxLeftLinear C where
  μₗ c d := adj.homEquiv _ _ (δₗ F c (G.obj d) ≫ c ⊴ₗ adj.counit.app d)
  μₗ_naturality_left f d := (adj.homEquiv _ _).symm.injective (by
    simp [homEquiv_unit, homEquiv_counit, action_exchange])
  μₗ_naturality_right c _ _ f := (adj.homEquiv _ _).symm.injective (by
    simp [homEquiv_unit, homEquiv_counit, ← actionHomRight_comp])
  μₗ_associativity c c' d := (adj.homEquiv _ _).symm.injective (by
    simp [homEquiv_unit, homEquiv_counit, ← actionHomRight_comp])
  μₗ_unitality d := (adj.homEquiv _ _).symm.injective (by
    simp [homEquiv_unit, homEquiv_counit])

/-- The lax lineators of `adj.rightAdjointLaxLeftLinear C`. -/
lemma rightAdjointLaxLeftLinear_μₗ [F.OplaxLeftLinear C] (c : C) (d : D') :
    letI := adj.rightAdjointLaxLeftLinear C
    μₗ G c d = adj.homEquiv _ _ (δₗ F c (G.obj d) ≫ c ⊴ₗ adj.counit.app d) := by
  rfl

variable (C)

/-- If `F` is left-linear and `G` carries the lax left-linear structure of
`adj.rightAdjointLaxLeftLinear C`, the unit `𝟭 D ⟶ F ⋙ G` of the adjunction is left-linear. -/
theorem isLeftLinear_unit [F.LeftLinear C] :
    letI := adj.rightAdjointLaxLeftLinear C
    NatTrans.IsLeftLinear adj.unit C := by
  let := adj.rightAdjointLaxLeftLinear C
  refine ⟨fun c d ↦ (adj.homEquiv _ _).symm.injective ?_⟩
  simp [rightAdjointLaxLeftLinear_μₗ, homEquiv_unit, homEquiv_counit,
    ← actionHomRight_comp_assoc, -actionHomRight_comp]

/-- If `F` is left-linear and `G` carries the lax left-linear structure of
`adj.rightAdjointLaxLeftLinear C`, the counit `G ⋙ F ⟶ 𝟭 D'` of the adjunction is
left-linear. -/
theorem isLeftLinear_counit [F.LeftLinear C] :
    letI := adj.rightAdjointLaxLeftLinear C
    NatTrans.IsLeftLinear adj.counit C := by
  let := adj.rightAdjointLaxLeftLinear C
  exact ⟨fun c d ↦ by simp [rightAdjointLaxLeftLinear_μₗ, homEquiv_unit]⟩

end CategoryTheory.Adjunction

namespace CategoryTheory.Equivalence

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalLeftAction C D]
  {D' : Type*} [Category* D'] [MonoidalLeftAction C D']

variable (C) in
/-- If the functor of an equivalence `e` is left-linear, so is its inverse, with lax lineators
those of `e.toAdjunction.rightAdjointLaxLeftLinear C`. -/
@[instance_reducible]
noncomputable def inverseLeftLinear (e : D ≌ D') [e.functor.LeftLinear C] :
    e.inverse.LeftLinear C :=
  letI := e.toAdjunction.rightAdjointLaxLeftLinear C
  haveI (c : C) (d : D') : IsIso (μₗ e.inverse c d) := by
    rw [Adjunction.rightAdjointLaxLeftLinear_μₗ, Adjunction.homEquiv_unit, toAdjunction_unit,
      toAdjunction_counit]
    infer_instance
  Functor.LeftLinear.ofLaxLeftLinear e.inverse

variable (e : D ≌ D') [e.functor.LeftLinear C]

/-- The lax lineators of `e.inverseLeftLinear C`: `μₗ e.inverse c d` is the adjoint of
`δₗ e.functor c (e.inverse.obj d) ≫ c ⊴ₗ e.counit.app d`. -/
lemma inverseLeftLinear_μₗ (c : C) (d : D') :
    letI := e.inverseLeftLinear C
    μₗ e.inverse c d = e.unit.app (c ⊙ₗ e.inverse.obj d) ≫
      e.inverse.map (δₗ e.functor c (e.inverse.obj d) ≫ c ⊴ₗ e.counit.app d) := by
  rfl

/-- The oplax lineators of `e.inverseLeftLinear C` are the inverses of its lax lineators. -/
lemma inverseLeftLinear_δₗ (c : C) (d : D') :
    letI := e.inverseLeftLinear C
    δₗ e.inverse c d = CategoryTheory.inv (μₗ e.inverse c d) := by
  rfl

variable (C)

/-- For the left-linear structure `e.inverseLeftLinear C` on the inverse, the unit
`𝟭 D ⟶ e.functor ⋙ e.inverse` of the equivalence is left-linear. -/
theorem isLeftLinear_unit :
    letI := e.inverseLeftLinear C
    NatTrans.IsLeftLinear e.unit C :=
  e.toAdjunction.isLeftLinear_unit C

/-- For the left-linear structure `e.inverseLeftLinear C` on the inverse, the counit
`e.inverse ⋙ e.functor ⟶ 𝟭 D'` of the equivalence is left-linear. -/
theorem isLeftLinear_counit :
    letI := e.inverseLeftLinear C
    NatTrans.IsLeftLinear e.counit C :=
  e.toAdjunction.isLeftLinear_counit C

end CategoryTheory.Equivalence

