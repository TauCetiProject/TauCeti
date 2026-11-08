/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The integers are projective in the category of abelian groups

The group of integers, universe-lifted as `ULift ℤ`, is a projective object of
`AddCommGrpCat`: it is free on the generator `1`, so a morphism out of it is determined by the
image of `1`, and that image lifts along any surjection. Epimorphisms of `AddCommGrpCat` are the
surjections (`AddCommGrpCat.epi_iff_surjective`).

This is the object that Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H` takes the constant
sheaf on, so projectivity of a constant sheaf with value `ULift ℤ` follows whenever the constant
sheaf functor is left adjoint to a functor preserving epimorphisms.
-/

public section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- **The integers are projective in `AddCommGrpCat`.** -/
instance projective_of_uliftInt : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) where
  factors {E X} f e he := by
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective e).mp he (f (ULift.up 1))
    refine ⟨AddCommGrpCat.ofHom ((zmultiplesHom E y).comp AddEquiv.ulift.toAddMonoidHom), ?_⟩
    ext ⟨n⟩
    -- Both sides are determined by the image of the generator `1`.
    have hn : (ULift.up n : ULift.{u} ℤ) = n • ULift.up 1 := ULift.ext (by simp)
    have h1 : AddEquiv.ulift (ULift.up 1 : ULift.{u} ℤ) = 1 := rfl
    simp [hy, hn, h1, map_zsmul]

end AddCommGrpCat
