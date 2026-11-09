/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Braiding and monoidal adjunctions

In a monoidal adjunction, the right adjoint's lax tensor map is compatible with braiding if and
only if the left adjoint's oplax tensor map is. In particular, a lax braided right adjoint makes a
strong monoidal left adjoint braided, and a braided strong monoidal left adjoint gives its right
adjoint a lax braided structure.

These facts apply to sheafification and to the pullback--pushforward adjunction of modules.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory
  Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- The oplax tensor map of a left adjoint respects braiding when the lax tensor map of its
right adjoint does. No invertibility of the left adjoint's tensor map is required. -/
@[reassoc]
theorem _root_.CategoryTheory.Adjunction.map_braiding_hom_comp_δ (adj : F ⊣ G)
    [F.OplaxMonoidal] [G.LaxBraided] [adj.IsMonoidal] (X Y : C) :
    F.map (β_ X Y).hom ≫ δ F Y X =
      δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [adj.unit_naturality_assoc, adj.unit_app_tensor_comp_map_δ,
    adj.unit_app_tensor_comp_map_δ_assoc, Functor.LaxBraided.braided, braiding_naturality_assoc]

/-- A strong monoidal left adjoint of a lax braided right adjoint is braided, for compatible
monoidal structures. Its monoidal structure is the given structure on `F`. -/
@[instance_reducible]
def _root_.CategoryTheory.Adjunction.leftAdjointBraided (adj : F ⊣ G)
    [F.Monoidal] [G.LaxBraided] [adj.IsMonoidal] : F.Braided where
  toMonoidal := inferInstance
  braided X Y := by
    rw [← cancel_epi (δ F X Y), Functor.Monoidal.δ_μ_assoc, ← adj.map_braiding_hom_comp_δ_assoc,
      Functor.Monoidal.δ_μ, Category.comp_id]

/-- The braided left adjoint retains its supplied monoidal structure. -/
@[simp]
theorem _root_.CategoryTheory.Adjunction.leftAdjointBraided_toMonoidal (adj : F ⊣ G)
    [hF : F.Monoidal] [G.LaxBraided] [adj.IsMonoidal] :
    adj.leftAdjointBraided.toMonoidal = hF :=
  (rfl)

/-- The lax tensor map of a right adjoint respects braiding when the oplax tensor map of its
left adjoint does. This is the converse of `Adjunction.map_braiding_hom_comp_δ`; no invertibility
of the left adjoint's tensor map is required. -/
@[reassoc]
theorem _root_.CategoryTheory.Adjunction.μ_comp_map_braiding_hom (adj : F ⊣ G)
    [F.OplaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal]
    (h : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (X Y : D) :
    μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj.counit_naturality, adj.map_μ_comp_counit_app_tensor_assoc,
    adj.map_μ_comp_counit_app_tensor, reassoc_of% h, braiding_naturality]

/-- A braided strong monoidal left adjoint gives a compatible lax monoidal right adjoint a
lax braided structure, with the given lax monoidal structure on `G`. -/
@[instance_reducible]
def _root_.CategoryTheory.Adjunction.rightAdjointLaxBraided (adj : F ⊣ G)
    [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal] : G.LaxBraided where
  toLaxMonoidal := inferInstance
  braided := adj.μ_comp_map_braiding_hom fun _ _ ↦ by simp

/-- The lax braided right adjoint retains its supplied lax monoidal structure. -/
@[simp]
theorem _root_.CategoryTheory.Adjunction.rightAdjointLaxBraided_toLaxMonoidal (adj : F ⊣ G)
    [F.Braided] [hG : G.LaxMonoidal] [adj.IsMonoidal] :
    adj.rightAdjointLaxBraided.toLaxMonoidal = hG :=
  (rfl)

end TauCeti
