/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Dimension obstructions to surjective derivatives

If the source has smaller finite dimension than the target, every derivative is nonsurjective,
so every source point is critical. This linear-algebraic obstruction holds for topological
modules over any nontrivially normed field, without differentiability assumptions.
-/

public section

open Function Module Set

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- When the source has strictly smaller finite dimension than the codomain, every Fréchet
derivative is nonsurjective. Thus every source point is critical, independently of the regularity
of the function. -/
theorem not_surjective_fderiv_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank 𝕜 E < finrank 𝕜 F) (x : E) :
    ¬ Surjective (fderiv 𝕜 f x) := by
  intro hsurj
  exact (not_le_of_gt hEF) (LinearMap.finrank_le_finrank_of_surjective hsurj)

/-- When the source has strictly smaller finite dimension than the codomain, the critical locus
of any function is the whole source. -/
@[simp]
theorem setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank 𝕜 E < finrank 𝕜 F) :
    {x | ¬ Surjective (fderiv 𝕜 f x)} = (univ : Set E) :=
  eq_univ_of_forall fun x ↦ not_surjective_fderiv_of_finrank_lt_finrank f hEF x

end TauCeti

end
