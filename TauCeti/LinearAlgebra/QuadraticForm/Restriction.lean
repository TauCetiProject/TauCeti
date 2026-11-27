/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Extensionality of quadratic maps along a spanning image

The values of a quadratic map on the image of a linear map determine it when that image spans
the domain over the scalars of the quadratic map. The proof extends equality of Mathlib's
bilinear companions using `LinearMap.ext_on_range`, then extends equality of the quadratic maps
by span induction.
-/

public section

namespace QuadraticMap

variable {R A M U D : Type*} [CommSemiring R] [CommSemiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid U] [Module R U] [Module A U]
  [AddCancelCommMonoid D] [Module A D]

/-- Two quadratic maps over an algebra agree everywhere if they agree along a linear map over
the base ring whose image spans their domain over the algebra. -/
theorem ext_of_span_range_eq_top (f : M →ₗ[R] U)
    (hf : Submodule.span A (LinearMap.range f : Set U) = ⊤)
    {Q Q' : QuadraticMap A U D} (h : ∀ x, Q (f x) = Q' (f x)) : Q = Q' := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  obtain ⟨B', hB'⟩ := Q'.exists_companion
  have hpair (x y : M) : B (f x) (f y) = B' (f x) (f y) := by
    apply add_left_cancel (a := Q' (f x) + Q' (f y))
    rw [← h x, ← h y, ← hB, ← map_add, h, map_add, hB', h x, h y]
  have hcompanion : B = B' := by
    apply LinearMap.ext_on_range hf
    intro x
    exact LinearMap.ext_on_range hf (hpair x)
  apply QuadraticMap.ext
  intro x
  have hx : x ∈ Submodule.span A (LinearMap.range f : Set U) := hf ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨y, rfl⟩ := hx
    exact h y
  | zero => simp
  | add x y _ _ hx hy => rw [hB, hB', hx, hy, hcompanion]
  | smul a x _ hx => rw [Q.map_smul, Q'.map_smul, hx]

end QuadraticMap
