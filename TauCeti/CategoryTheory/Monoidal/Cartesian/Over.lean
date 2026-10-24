/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Products of section charts in a slice category

The pullback of two sections over the same base has equal projections to that base.
Consequently a product chart followed by multiplication in a monoid object evaluates as the
product of its two sections. This is useful for restricting group operations to a subscheme
covered by sections.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace TauCeti.CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {S : C}

/-- On a product of two section charts, multiplication after a map to a monoid object is the
product of the resulting sections, pulled back from the base. -/
@[reassoc]
theorem pullback_map_comp_mul_left {D G : Over S} [MonObj G] (i : D ⟶ G)
    (a b : 𝟙_ (Over S) ⟶ D) :
    pullback.map (a.left ≫ D.hom) (b.left ≫ D.hom) D.hom D.hom a.left b.left (𝟙 S)
      (Category.comp_id _) (Category.comp_id _) ≫ ((i ⊗ₘ i) ≫ μ[G]).left =
      pullback.fst (a.left ≫ D.hom) (b.left ≫ D.hom) ≫ ((a ≫ i) * (b ≫ i)).left := by
  have hsb (a : 𝟙_ (Over S) ⟶ D) : a.left ≫ D.hom = 𝟙 S := Over.w a
  have hab : pullback.fst (a.left ≫ D.hom) (b.left ≫ D.hom) =
      pullback.snd (a.left ≫ D.hom) (b.left ≫ D.hom) := by
    have h := pullback.condition (f := a.left ≫ D.hom) (g := b.left ≫ D.hom)
    simp only [hsb] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))
  rw [Hom.mul_def]
  simp only [Over.comp_left, Over.lift_left, Over.tensorHom_left]
  refine (Category.assoc _ _ _).symm.trans ?_
  conv_rhs => rw [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ (μ[G]).left)
  apply pullback.hom_ext
  · simp [pullback.map, Category.assoc]
  · simp [pullback.map, Category.assoc, hab]

end TauCeti.CategoryTheory.Over
