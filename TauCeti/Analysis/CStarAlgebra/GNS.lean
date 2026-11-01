/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# Continuity of the GNS class map

For a positive linear functional `f` on a possibly nonunital C⋆-algebra `A`, Mathlib's
`PositiveLinearMap.PreGNS` is `A` with the semi-inner product `⟪a, b⟫ = f (a⋆ b)`. Positive
functionals on C⋆-algebras are bounded, `PositiveLinearMap.exists_norm_apply_le`, so
`‖[a]‖ ^ 2 = f (a⋆ a) ≤ C ‖a‖ ^ 2` and the class map `f.toPreGNS : A → f.PreGNS` is continuous.
This lets norm-continuous families in `A`, such as orbits of point-norm continuous actions, be
transported to the GNS space. Composed with the embedding into the completion, it is the
continuous linear class map `f.toGNS : A →L[ℂ] f.GNS`, `a ↦ [a]`, which has dense range.
-/

public section

open scoped ComplexOrder NNReal

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The class map of a positive linear functional on a C⋆-algebra into its GNS pre-Hilbert space
is continuous. -/
@[fun_prop]
theorem continuous_toPreGNS (f : A →ₚ[ℂ] ℂ) : Continuous (f.toPreGNS : A → f.PreGNS) := by
  obtain ⟨C, hC⟩ := f.exists_norm_apply_le
  refine AddMonoidHomClass.continuous_of_bound f.toPreGNS (√C) fun a => ?_
  calc ‖f.toPreGNS a‖ = √‖f (star a * a)‖ := by simp [preGNS_norm_def']
    _ ≤ √(C * ‖a‖ ^ 2) := by
      gcongr
      simpa [CStarRing.norm_star_mul_self, sq] using hC (star a * a)
    _ = √C * ‖a‖ := by rw [Real.sqrt_mul C.coe_nonneg, Real.sqrt_sq (norm_nonneg a)]

/-- The class map `a ↦ [a]` of a positive linear functional on a C⋆-algebra into its GNS Hilbert
space, as a continuous linear map. -/
noncomputable def toGNS (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] f.GNS :=
  UniformSpace.Completion.toComplL.comp ⟨f.toPreGNS.toLinearMap, f.continuous_toPreGNS⟩

@[simp]
theorem toGNS_apply (f : A →ₚ[ℂ] ℂ) (a : A) : f.toGNS a = (f.toPreGNS a : f.GNS) :=
  (rfl)

/-- The classes of elements of `A` are dense in the GNS Hilbert space. -/
theorem denseRange_toGNS (f : A →ₚ[ℂ] ℂ) : DenseRange f.toGNS :=
  UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

end PositiveLinearMap
