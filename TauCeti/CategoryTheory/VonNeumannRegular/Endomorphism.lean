/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import TauCeti.CategoryTheory.VonNeumannRegular.Basic
public import TauCeti.RingTheory.VonNeumannRegular.Basic

/-!
# Endomorphisms in von Neumann regular categories

The endomorphism monoid of any object in a von Neumann regular category is von Neumann regular.
Conversely, regularity of the endomorphism monoid of a binary biproduct gives inner inverses
for morphisms between its summands.
-/

public section

namespace TauCeti.IsVonNeumannRegularCategory

open CategoryTheory

variable {C : Type*} [Category* C]

/-- Endomorphism monoids in a von Neumann regular category are von Neumann regular. -/
instance [IsVonNeumannRegularCategory C] (X : C) : IsVonNeumannRegularSemigroup (End X) where
  exists_mul_mul_eq_self f := by
    obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f.asHom
    exact ⟨End.of g, End.ext (by simpa only [End.mul_asHom, Category.assoc] using hg)⟩

end TauCeti.IsVonNeumannRegularCategory

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- If the endomorphism monoid of `X ⊞ Y` is von Neumann regular, then every morphism
`f : X ⟶ Y` has an inner inverse. -/
theorem exists_comp_comp_eq_self_of_isVonNeumannRegularSemigroup_end {X Y : C}
    [HasZeroMorphisms C] [HasBinaryBiproduct X Y] [IsVonNeumannRegularSemigroup (End (X ⊞ Y))]
    (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  obtain ⟨φ, hφ⟩ :=
    IsVonNeumannRegularSemigroup.exists_mul_mul_eq_self (End.of (biprod.fst ≫ f ≫ biprod.inr))
  refine ⟨biprod.inr ≫ φ.asHom ≫ biprod.fst, ?_⟩
  simpa using congrArg (fun ψ : End (X ⊞ Y) ↦ biprod.inl ≫ ψ.asHom ≫ biprod.snd) hφ

end TauCeti
