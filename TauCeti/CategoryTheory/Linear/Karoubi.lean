/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linear structure on the idempotent completion

Mathlib equips the idempotent completion `Karoubi C` of a preadditive category `C` with its
preadditive structure only. This file shows that an `R`-linear structure on `C` also passes to
`Karoubi C`: the scalar multiple of a morphism `f : P ⟶ Q` is the morphism with underlying
morphism `r • f.f`, which is again compatible with the idempotents of `P` and `Q`.

The embedding `toKaroubi C` is then `R`-linear, and so is the extension
`(functorExtension₁ C D).obj F : Karoubi C ⥤ Karoubi D` of an `R`-linear functor
`F : C ⥤ Karoubi D`, and in particular the extension `(functorExtension₂ C D).obj F` of an
`R`-linear functor `F : C ⥤ D`.

Together with the linear structure on `Mat_ C` (`TauCeti/CategoryTheory/Linear/Mat.lean`), this
makes the additive and idempotent envelope `Karoubi (Mat_ C)` of an `R`-linear category
`R`-linear.

## Main results

* `CategoryTheory.Idempotents.Karoubi.smul_f`: the underlying morphism of a scalar multiple.
* The instance `CategoryTheory.Linear R (Karoubi C)`.
* The instance `(toKaroubi C).Linear R`.
* The instances `((functorExtension₁ C D).obj F).Linear R` and
  `((functorExtension₂ C D).obj F).Linear R` for an `R`-linear functor `F`.
-/

public section

namespace CategoryTheory.Idempotents

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {R : Type w} [Semiring R] [Linear R C]

namespace Karoubi

/-- The scalar multiple of a morphism of `Karoubi C`: its underlying morphism is `r • f.f`. -/
instance instSMulHom {P Q : Karoubi C} : SMul R (P ⟶ Q) where
  smul r f := ⟨r • f.f, by simp⟩

/-- The underlying morphism of a scalar multiple is the scalar multiple of the underlying
morphism. -/
@[simp]
theorem smul_f {P Q : Karoubi C} (r : R) (f : P ⟶ Q) : (r • f).f = r • f.f :=
  (rfl)

/-- The `R`-module of morphisms of `Karoubi C`, embedded in the `R`-module of underlying
morphisms by `Karoubi.Hom.f`. -/
instance instModuleHom {P Q : Karoubi C} : Module R (P ⟶ Q) :=
  Function.Injective.module R (inclusionHom P Q) (fun _ _ h ↦ hom_ext _ _ h) fun _ _ ↦ rfl

end Karoubi

open Karoubi

/-- The idempotent completion of an `R`-linear category is `R`-linear. -/
instance instLinearKaroubi : Linear R (Karoubi C) where
  smul_comp _ _ _ r f g := by
    ext
    simp
  comp_smul _ _ _ f r g := by
    ext
    simp

/-- The embedding of `C` into its idempotent completion is `R`-linear. -/
instance instLinearToKaroubi : (toKaroubi C).Linear R where

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]

/-- The extension to `Karoubi C` of an `R`-linear functor `C ⥤ Karoubi D` is `R`-linear. -/
instance (F : C ⥤ Karoubi D) [F.Linear R] : ((functorExtension₁ C D).obj F).Linear R where
  map_smul f r := by
    ext
    -- The extension applies `F.map` to underlying morphisms (`FunctorExtension₁.obj_map_f`), and
    -- scalars act on underlying morphisms (`Karoubi.smul_f`). Neither lemma rewrites here, since
    -- the types involved mention `(functorExtension₁ C D).obj F`, so the goal is closed up to
    -- these two definitional unfoldings.
    exact (congr_arg Hom.f (F.map_smul r f.f) :)

/-- The extension to the idempotent completions of an `R`-linear functor `C ⥤ D` is
`R`-linear. -/
instance (F : C ⥤ D) [F.Linear R] : ((functorExtension₂ C D).obj F).Linear R :=
  inferInstanceAs (((functorExtension₁ C D).obj (F ⋙ toKaroubi D)).Linear R)

end CategoryTheory.Idempotents
