/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Weak Serre subcategories and five-term exact sequences

Let `P` be a property of objects of an abelian category which is closed under kernels, cokernels
and extensions; such a `P` is called a weak Serre subcategory. If `A ⟶ B ⟶ M ⟶ D ⟶ E` is exact at
`B`, `M` and `D` and the four outer objects satisfy `P`, then so does `M`
(`CategoryTheory.ObjectProperty.prop_X₂_of_exact_of_exact_of_exact`): the object `M` is an extension
of the kernel of `D ⟶ E` by the cokernel of `A ⟶ B`.

Applied to the long exact homology sequence of a distinguished triangle, this shows that the
objects of a derived category whose homology objects all satisfy `P` form a triangulated
subcategory.

## References

* The Stacks project, chapter Homological Algebra, section Serre subcategories: the
  characterization of weak Serre subcategories by five-term exact sequences.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- A property closed under kernels, cokernels and extensions contains the middle object of a
five-term exact sequence `A ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ E` whose four outer objects it contains. -/
theorem prop_X₂_of_exact_of_exact_of_exact {S : ShortComplex C} (hS : S.Exact) {A E : C}
    {a : A ⟶ S.X₁} {e : S.X₃ ⟶ E} (wa : a ≫ S.f = 0) (we : S.g ≫ e = 0)
    (ha : (ShortComplex.mk a S.f wa).Exact) (he : (ShortComplex.mk S.g e we).Exact)
    (hA : P A) (h₁ : P S.X₁) (h₃ : P S.X₃) (hE : P E) : P S.X₂ := by
  exact P.prop_X₂_of_shortExact (S := ShortComplex.mk
    (cokernel.desc a S.f wa) (kernel.lift e S.g we) (by ext; simp))
    (hS.shortExact_cokernelDesc_kernelLift wa we ha he)
    (P.prop_cokernel a hA h₁) (P.prop_kernel e h₃ hE)

end CategoryTheory.ObjectProperty
