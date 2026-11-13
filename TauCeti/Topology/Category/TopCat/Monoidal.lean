/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Fibre inclusions of products in `TopCat`

For spaces `X` and `F` and a point `x : X`, `TopCat.prodFiberInclusion X F x : F ⟶ X ⊗ F` is the
inclusion `f ↦ (x, f)` of the fibre of the first projection over `x`, built from the cartesian
monoidal structure of `TopCat`. Its composites with the projections are the constant map at `x`
and the identity, so it is a split monomorphism, and it is natural in `X` and in `F`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

namespace TopCat

variable (X F : TopCat.{u})

/-- The inclusion `f ↦ (x, f)` of the fibre `F` over `x : X` into the product `X × F`. -/
def prodFiberInclusion (x : X) : F ⟶ X ⊗ F :=
  lift (TopCat.const x) (𝟙 F)

lemma prodFiberInclusion_def (x : X) : prodFiberInclusion X F x = lift (TopCat.const x) (𝟙 F) :=
  (rfl)

@[simp]
lemma prodFiberInclusion_apply (x : X) (f : F) :
    prodFiberInclusion X F x f = ((x, f) : ↑(X ⊗ F)) := by
  rw [prodFiberInclusion_def, TopCat.lift_apply, TopCat.const_apply, ConcreteCategory.id_apply]

@[reassoc (attr := simp)]
lemma prodFiberInclusion_fst (x : X) : prodFiberInclusion X F x ≫ fst X F = TopCat.const x :=
  lift_fst _ _

@[reassoc (attr := simp)]
lemma prodFiberInclusion_snd (x : X) : prodFiberInclusion X F x ≫ snd X F = 𝟙 F :=
  lift_snd _ _

/-- The fibre inclusion is a split monomorphism, with retraction the second projection. -/
instance isSplitMono_prodFiberInclusion (x : X) : IsSplitMono (prodFiberInclusion X F x) :=
  .mk' ⟨snd X F, prodFiberInclusion_snd X F x⟩

variable {X F}

/-- The fibre inclusion is natural in the base. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_whiskerRight {Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    prodFiberInclusion X F x ≫ f ▷ F = prodFiberInclusion Y F (f x) := by
  ext <;> simp

/-- The fibre inclusion is natural in the fibre. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_whiskerLeft {G : TopCat.{u}} (g : F ⟶ G) (x : X) :
    prodFiberInclusion X F x ≫ X ◁ g = g ≫ prodFiberInclusion X G x := by
  ext <;> simp

/-- The fibre inclusion is natural in the base and the fibre jointly. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_tensorHom {Y G : TopCat.{u}} (f : X ⟶ Y) (g : F ⟶ G) (x : X) :
    prodFiberInclusion X F x ≫ (f ⊗ₘ g) = g ≫ prodFiberInclusion Y G (f x) := by
  ext <;> simp

end TopCat
