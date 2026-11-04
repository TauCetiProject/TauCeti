/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# The GNS class map and cyclic vector

For a positive linear functional `f` on a possibly nonunital C⋆-algebra `A`, Mathlib's
`PositiveLinearMap.PreGNS` is `A` with the semi-inner product `⟪a, b⟫ = f (a⋆ b)`. Positive
functionals on C⋆-algebras are bounded, `PositiveLinearMap.exists_norm_apply_le`, so
`‖[a]‖ ^ 2 = f (a⋆ a) ≤ C ‖a‖ ^ 2` and the class map `f.toPreGNS : A → f.PreGNS` is continuous.
This lets norm-continuous families in `A`, such as orbits of point-norm continuous actions, be
transported to the GNS space. Composed with the embedding into the completion, it is the
continuous linear class map `f.toGNS : A →L[ℂ] f.GNS`, `a ↦ [a]`, which has dense range.

For a unital algebra, `PositiveLinearMap.gnsVector` is the class of the unit. Its orbit under
Mathlib's GNS representation is dense and its vector functional recovers the original positive
functional. It has norm one when the functional is normalized. This identifies a state with a
concrete vector state, allowing comparison of scalar laws with spectral measures.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
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

section Unital

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The canonical cyclic vector of the GNS representation of a positive functional: the class
of the unit. It is a unit vector precisely when the functional is normalized. -/
noncomputable def gnsVector (f : B →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS 1 : f.GNS)

/-- The canonical GNS vector is the class of the unit. -/
theorem gnsVector_def (f : B →ₚ[ℂ] ℂ) : f.gnsVector = (f.toPreGNS 1 : f.GNS) := (rfl)

/-- Acting on the canonical GNS vector produces the class of the acting element. -/
@[simp]
theorem gnsNonUnitalStarAlgHom_apply_gnsVector (f : B →ₚ[ℂ] ℂ) (a : B) :
    f.gnsNonUnitalStarAlgHom a f.gnsVector = (f.toPreGNS a : f.GNS) := by
  simp [gnsVector_def]

/-- Inner products of orbit vectors in the GNS representation recover the star pairing of
the original functional. -/
theorem inner_gnsStarAlgHom_gnsVector (f : B →ₚ[ℂ] ℂ) (a b : B) :
    inner ℂ (f.gnsStarAlgHom a f.gnsVector) (f.gnsStarAlgHom b f.gnsVector) =
      f (star a * b) := by
  simp [preGNS_inner_def]

/-- Pairing the canonical GNS vector with the class of `a` recovers the functional at `a`.
Together with the action formula, this identifies the functional with its GNS vector state. -/
@[simp]
theorem inner_gnsVector_coe (f : B →ₚ[ℂ] ℂ) (a : B) :
    inner ℂ f.gnsVector (f.toPreGNS a : f.GNS) = f a := by
  simp [gnsVector_def, preGNS_inner_def]

/-- The orbit of the canonical GNS vector is dense, so this vector is cyclic. -/
theorem denseRange_gnsStarAlgHom_gnsVector (f : B →ₚ[ℂ] ℂ) :
    DenseRange (fun a : B => f.gnsStarAlgHom a f.gnsVector) := by
  simpa [Function.comp_def] using
    UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
      (UniformSpace.Completion.continuous_coe f.PreGNS)

/-- The squared norm of the canonical GNS vector is the mass of the functional. -/
theorem norm_gnsVector_sq (f : B →ₚ[ℂ] ℂ) : (‖f.gnsVector‖ ^ 2 : ℂ) = f 1 := by
  simp [gnsVector_def, preGNS_norm_sq]

/-- A normalized positive functional has a unit canonical GNS vector. -/
theorem norm_gnsVector (f : B →ₚ[ℂ] ℂ) (hf : f 1 = 1) : ‖f.gnsVector‖ = 1 := by
  have h := f.norm_gnsVector_sq
  rw [hf, ← Complex.ofReal_pow, Complex.ofReal_eq_one] at h
  nlinarith [norm_nonneg f.gnsVector]

end Unital

end PositiveLinearMap
