/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Universe-lifted scalar linearity of categories and functors

If a preadditive category `C` is `R`-linear, then equipping each morphism group with Mathlib's
`ULift.module` action `(r : ULift.{w'} R) • f = r.down • f` makes `C` linear over the
universe-lifted semiring `ULift.{w'} R`. Likewise, an `R`-linear functor between `R`-linear
categories is `ULift.{w'} R`-linear, and conversely.

In particular, any preadditive category is `ULift.{v} ℤ`-linear in its own morphism universe `v`,
so enriched Hom-complex and differential graded constructions that require the scalar ring to live
in the morphism universe apply without universe restrictions on the category.
-/

public section

universe w' w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Linear

variable {R : Type w} [Semiring R] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]

/-- An `R`-linear category is linear over `ULift.{w'} R` via `r • f = r.down • f`. The underlying
module structure on each Hom group is `ULift.module`. -/
instance ulift : Linear (ULift.{w'} R) C where
  smul_comp _ _ _ r f g := Linear.smul_comp _ _ _ r.down f g
  comp_smul _ _ _ f r g := Linear.comp_smul _ _ _ f r.down g

end Linear

namespace Functor

variable (R : Type w) [Semiring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear R D]
  (F : C ⥤ D)

/-- An `R`-linear functor between `R`-linear categories is `ULift.{w'} R`-linear. -/
instance uliftLinear [F.Linear R] : F.Linear (ULift.{w'} R) where
  map_smul f r := F.map_smul r.down f

/-- Scalar linearity of a functor over `ULift.{w'} R` is equivalent to scalar linearity over `R`. -/
@[simp]
theorem linear_ulift_iff : F.Linear (ULift.{w'} R) ↔ F.Linear R :=
  ⟨fun h ↦ { map_smul := fun f r ↦ h.map_smul f (ULift.up r) }, fun _ ↦ inferInstance⟩

end Functor

end CategoryTheory
