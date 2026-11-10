/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Objects presented by a property of objects

For a property `P` of objects of a preadditive category, `P.presented` is the property of being a
cokernel of a morphism between objects of `P`. In an abelian category in which every object is a
quotient of an object of `P`, every object is `P`-presented.

## Main declarations

* `CategoryTheory.ObjectProperty.presented`: the objects that are cokernels of morphisms between
  objects of `P`.
* `CategoryTheory.ObjectProperty.presented_eq_top`: every object is `P`-presented when every object
  is a quotient of an object of `P`.
-/

public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- The objects of `C` that are cokernels of morphisms between objects of `P`. -/
abbrev presented [Preadditive C] (P : ObjectProperty C) : ObjectProperty C :=
  (MorphismProperty.ofObjectProperty P P).cokernels

/-- If every object of `C` is a quotient of an object of `P`, then every object of `C` is a
cokernel of a morphism between objects of `P`. -/
theorem presented_eq_top [Abelian C] {P : ObjectProperty C}
    (hgen : ∀ X : C, ∃ (Q : C) (π : Q ⟶ X), P Q ∧ Epi π) :
    P.presented = ⊤ := by
  refine top_le_iff.1 fun X _ ↦ ?_
  obtain ⟨B, π, hB, hπ⟩ := hgen X
  obtain ⟨A, e, hA, he⟩ := hgen (kernel π)
  let S : ShortComplex C := .mk (e ≫ kernel.ι π) π (by simp)
  have hS : S.Exact := by
    rw [S.exact_iff_epi_kernel_lift]
    convert he
    ext
    simp [S]
  have : Epi S.g := hπ
  exact .of_isColimit S.f _ hS.gIsCokernel ⟨hA, hB⟩

end CategoryTheory.ObjectProperty
