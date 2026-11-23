/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Separation of points by states

Using spectral and norm attainment from `TauCeti.Analysis.CStarAlgebra.State.Spectrum`, states of a
possibly nonunital C⋆-algebra `A` separate points without assuming `[Nontrivial A]`:

* `TauCeti.eq_zero_of_forall_mem_stateSpace_apply_eq_zero`,
  `TauCeti.eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero`,
  `TauCeti.forall_mem_stateSpace_apply_eq_zero_iff`,
  `TauCeti.eq_of_forall_mem_stateSpace_apply_eq`, and `TauCeti.forall_mem_stateSpace_apply_eq_iff`:
  states separate all elements of `A`.

## References

* J. Peterson, *Notes on von Neumann algebras* (2013), Proposition 4.1.5, p. 56.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Theorem 3.3.6.
-/

public section

open WeakDual
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **State separation of zero.** If `φ a = 0` for every state `φ` of `A`, then `a = 0`. -/
theorem eq_zero_of_forall_mem_stateSpace_apply_eq_zero {a : A}
    (h : ∀ φ ∈ stateSpace A, φ a = 0) : a = 0 := by
  have hsa (x : selfAdjoint A) (hx : ∀ φ : stateSpace A, φ.val x = 0) : (x : A) = 0 := by
    have : IsStarNormal (x : A) := x.property.isStarNormal
    exact norm_eq_zero.1 <| by
      simp [norm_eq_iSup_norm_apply_stateSpace_of_isStarNormal (x : A), hx, Real.iSup_const_zero]
  have hre : (realPart a : A) = 0 := hsa (realPart a) fun φ => by
    simpa [h φ.val φ.property] using map_realPart (StateSpace.toPositiveLinearMap φ) a
  have him : (imaginaryPart a : A) = 0 := hsa (imaginaryPart a) fun φ => by
    simpa [h φ.val φ.property] using map_imaginaryPart (StateSpace.toPositiveLinearMap φ) a
  rw [← realPart_add_I_smul_imaginaryPart a]
  simp [hre, him]

/-- If `φ (star a * a) = 0` for every state `φ` of `A`, then `a = 0`. -/
theorem eq_zero_of_forall_mem_stateSpace_apply_star_mul_self_eq_zero {a : A}
    (h : ∀ φ ∈ stateSpace A, φ (star a * a) = 0) : a = 0 :=
  star_mul_self_eq_zero.1 (eq_zero_of_forall_mem_stateSpace_apply_eq_zero h)

/-- An element `a` of a C⋆-algebra is zero if and only if every state vanishes on `a`. -/
@[simp]
theorem forall_mem_stateSpace_apply_eq_zero_iff {a : A} :
    (∀ φ ∈ stateSpace A, φ a = 0) ↔ a = 0 :=
  ⟨eq_zero_of_forall_mem_stateSpace_apply_eq_zero, by rintro rfl φ _; simp⟩

/-- **States separate points.** Two elements of a C⋆-algebra are equal if every state takes the
same value on them. -/
theorem eq_of_forall_mem_stateSpace_apply_eq {a b : A}
    (h : ∀ φ ∈ stateSpace A, φ a = φ b) : a = b :=
  sub_eq_zero.1 <| eq_zero_of_forall_mem_stateSpace_apply_eq_zero fun φ hφ => by
    rw [map_sub, h φ hφ, sub_self]

/-- Two elements of a C⋆-algebra are equal if and only if every state takes the same value on
them. -/
@[simp]
theorem forall_mem_stateSpace_apply_eq_iff {a b : A} :
    (∀ φ ∈ stateSpace A, φ a = φ b) ↔ a = b :=
  ⟨eq_of_forall_mem_stateSpace_apply_eq, fun h _ _ => h ▸ rfl⟩

end TauCeti
