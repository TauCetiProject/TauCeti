/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.LeftExact

import Mathlib.Algebra.Homology.ShortComplex.Ab
import TauCeti.CategoryTheory.Triangulated.WeakCokernels

/-!
# Flat modules over pretriangulated categories

A contravariant additive functor from a pretriangulated category to abelian groups
is flat exactly when it is cohomological. Distinguished triangles give weak
kernels in the opposite category, so exactness on triangles detects equational
flatness. This is the flatness–cohomological equivalence in Krause,
*Smashing subcategories and the telescope conjecture*, Lemma 2.7.
-/

public section

universe w v u

open CategoryTheory Limits Opposite Pretriangulated
open scoped CategoryTheory.Pretriangulated.Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Over a pretriangulated category, a module is flat precisely when it sends distinguished
triangles in the opposite category to exact sequences. -/
theorem flat_iff_isHomological (F : ModCat.{w} C) : F.Flat ↔ F.obj.IsHomological := by
  refine ⟨fun hF ↦ ⟨fun T hT ↦ ?_⟩, fun hF ↦ ?_⟩
  · let S := (shortComplexOfDistTriangle T hT).map F.obj
    exact S.ab_exact_iff_function_exact.mpr
      (Flat.exact_of_isWeakCokernel (isWeakCokernel_of_distTriang hT))
  · apply (flat_iff_exists_isWeakCokernel_exact F).mpr
    intro X Y f
    obtain ⟨Z, q, k, hT⟩ := distinguished_cocone_triangle₁ f.op
    let T := Triangle.mk q f.op k
    let S := (shortComplexOfDistTriangle T hT).map F.obj
    exact ⟨Z.unop, q.unop, isWeakCokernel_of_distTriang hT,
      S.ab_exact_iff_function_exact.mp (F.obj.map_distinguished_exact T hT)⟩

end TauCeti.ModCat
