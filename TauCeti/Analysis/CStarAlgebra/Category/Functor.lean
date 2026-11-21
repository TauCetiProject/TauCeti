/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.CategoryTheory.Dagger.Functor

/-!
# Automatic contractivity of dagger functors between C*-categories

A complex linear dagger-preserving functor `F` between C*-categories restricts, on each object
`X`, to a unital star algebra homomorphism `F.mapEndStarAlgHom ℂ X : End X →⋆ₐ[ℂ] End (F.obj X)`
of C*-algebras. Such
homomorphisms are contractive, and isometric when injective. The C*-identity
`‖f‖² = ‖f†f‖` transfers both facts to arrows between different objects: every such functor is
contractive on Hom spaces, and a faithful one is isometric.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [DaggerPreadditive D] [DaggerLinear ℂ D]
  [∀ X Y : D, Norm (X ⟶ Y)] [CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

omit [DaggerPreadditive C] [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] in
/-- The square of the norm of `F.map f` is the norm of `F.map (f ≫ dagger f)`. -/
private theorem sq_norm_map {X Y : C} (f : X ⟶ Y) :
    ‖F.map f‖ ^ 2 = ‖F.mapEndStarAlgHom ℂ X (.of (f ≫ dagger f))‖ := by
  rw [End.norm_def, mapEndStarAlgHom_asHom, F.map_comp, F.map_dagger,
    CStarCategory.norm_self_comp_dagger]

/-- A complex linear dagger functor between C*-categories is contractive on Hom spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  refine (pow_le_pow_iff_left₀ (CStarCategory.norm_nonneg _) (CStarCategory.norm_nonneg f)
    two_ne_zero).1 ?_
  rw [sq_norm_map, ← CStarCategory.norm_self_comp_dagger, ← End.norm_of]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- A faithful complex linear dagger functor between C*-categories is isometric on Hom
spaces. -/
@[simp] theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  refine (pow_left_inj₀ (CStarCategory.norm_nonneg _) (CStarCategory.norm_nonneg f)
    two_ne_zero).1 ?_
  have hinj := F.mapEndAlgHom_injective ℂ X
  rw [← toAlgHom_mapEndStarAlgHom, StarAlgHom.coe_toAlgHom] at hinj
  rw [sq_norm_map, ← CStarCategory.norm_self_comp_dagger, ← End.norm_of]
  exact NonUnitalStarAlgHom.norm_map _ hinj _

end CategoryTheory.Functor
