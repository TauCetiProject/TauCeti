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

In a monoidal adjunction, a lax braided right adjoint makes the left adjoint's oplax tensor
map compatible with braiding. If the left adjoint is strong monoidal, it is therefore braided.
Conversely, a braided strong monoidal left adjoint gives its right adjoint a lax braided
structure.

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
    adj.unit_app_tensor_comp_map_δ_assoc, Functor.LaxBraided.braided]
  exact (braiding_naturality_assoc (adj.unit.app X) (adj.unit.app Y) _).symm

/-- A strong monoidal left adjoint of a lax braided right adjoint is braided, for compatible
monoidal structures. Its monoidal structure is the given structure on `F`. -/
@[instance_reducible]
def _root_.CategoryTheory.Adjunction.leftAdjointBraided (adj : F ⊣ G)
    [F.Monoidal] [G.LaxBraided] [adj.IsMonoidal] : F.Braided where
  toMonoidal := inferInstance
  braided X Y := by
    rw [← cancel_epi (δ F X Y)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    rw [← adj.map_braiding_hom_comp_δ_assoc, Functor.Monoidal.δ_μ,
      Category.comp_id]

/-- The braided left adjoint retains its supplied monoidal structure. -/
@[simp]
theorem _root_.CategoryTheory.Adjunction.leftAdjointBraided_toMonoidal (adj : F ⊣ G)
    [hF : F.Monoidal] [G.LaxBraided] [adj.IsMonoidal] :
    adj.leftAdjointBraided.toMonoidal = hF :=
  (rfl)

/-- A braided strong monoidal left adjoint gives a compatible lax monoidal right adjoint a
lax braided structure, with the given lax monoidal structure on `G`. -/
@[instance_reducible]
def _root_.CategoryTheory.Adjunction.rightAdjointLaxBraided (adj : F ⊣ G)
    [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal] : G.LaxBraided where
  toLaxMonoidal := inferInstance
  braided X Y := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [adj.counit_naturality, adj.map_μ_comp_counit_app_tensor_assoc,
      adj.map_μ_comp_counit_app_tensor, Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
    exact congrArg (δ F (G.obj X) (G.obj Y) ≫ ·)
      (braiding_naturality (adj.counit.app X) (adj.counit.app Y))

/-- The lax braided right adjoint retains its supplied lax monoidal structure. -/
@[simp]
theorem _root_.CategoryTheory.Adjunction.rightAdjointLaxBraided_toLaxMonoidal (adj : F ⊣ G)
    [F.Braided] [hG : G.LaxMonoidal] [adj.IsMonoidal] :
    adj.rightAdjointLaxBraided.toLaxMonoidal = hG :=
  (rfl)

end TauCeti
