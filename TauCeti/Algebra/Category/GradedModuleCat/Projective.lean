/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Module.GradedModule.DegreeZeroPart

/-!
# Projective objects in the category of graded modules

A graded module whose underlying module is projective is projective in the graded category.
An ungraded lift exists by module projectivity; taking its degree-zero part gives a graded lift
without changing its composite with the given graded epimorphism.

This makes projective terms in graded module resolutions into categorical projectives, so the
categorical Ext-vanishing and projective Euler-evaluation theorems apply to them. The coefficient
ring need not be a field, and no finite-generation or boundedness hypothesis is imposed.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Mathlib's `ModuleCat.projective_of_categoryTheory_projective` supplies the corresponding
  ungraded lifting argument; here the lift is additionally made homogeneous.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [DirectSum.Decomposition 𝒜]

/-- An ungraded-projective module is a projective object of the graded module category.
Taking the degree-zero part of an ungraded lift produces the required graded lift. -/
instance projective_of_module_projective (P : GradedModuleCat.{v} 𝒜)
    [Module.Projective A P] : CategoryTheory.Projective P := by
  refine ⟨fun X E hE => ?_⟩
  obtain ⟨f, hf⟩ := Module.projective_lifting_property E.hom X.hom
    ((epi_iff_surjective E).mp hE)
  refine ⟨ofHom (P.grading.degreeZeroPart _ 𝒜 f)
    (P.grading.isHomogeneous_degreeZeroPart _ 𝒜 f), hom_ext ?_⟩
  simp only [hom_comp]
  exact (P.grading.comp_degreeZeroPart _ 𝒜 _ f E.isHomogeneous).trans
    ((congrArg (P.grading.degreeZeroPart _ 𝒜) hf).trans
      ((P.grading.degreeZeroPart_eq_self_iff _ 𝒜 X.hom).mpr X.isHomogeneous))

end TauCeti.GradedModuleCat
