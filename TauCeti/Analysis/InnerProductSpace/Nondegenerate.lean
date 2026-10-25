/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Nondegeneracy of the real inner product

The real inner product `innerₗ E` is a nondegenerate bilinear form on `E`
(`TauCeti.nondegenerate_inner`): a vector orthogonal to every vector is orthogonal to itself, hence
zero. This is the hypothesis under which Mathlib's bilinear-form constructions, such as the dual
basis `LinearMap.BilinForm.dualBasis`, apply to the inner product. In finite dimension it is
moreover a perfect pairing (`TauCeti.bijective_innerₗ`), as Mathlib's `exteriorPower.hodgeStar`
requires of its bilinear form. Its pullback along an injective linear map, such as the metric
induced by an immersion, is again nondegenerate (`TauCeti.nondegenerate_inner_comp`), so a vector
is determined by its pairings with it (`TauCeti.eq_of_forall_inner_comp`).
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real inner product is a nondegenerate bilinear form. -/
theorem nondegenerate_inner : (innerₗ E).Nondegenerate :=
  ⟨fun x hx ↦ inner_self_eq_zero.mp (hx x), fun y hy ↦ inner_self_eq_zero.mp (hy y)⟩

/-- In finite dimension the real inner product is a perfect pairing: `v ↦ ⟪v, ·⟫` is a bijection
onto the dual. -/
theorem bijective_innerₗ [FiniteDimensional ℝ E] : Function.Bijective (innerₗ E) := by
  convert (LinearMap.BilinForm.toDual (innerₗ E) nondegenerate_inner).bijective using 1
  ext v w
  exact (LinearMap.BilinForm.toDual_def nondegenerate_inner).symm

/-- The real inner product pulled back along an injective linear map is nondegenerate: a vector
`v` with `⟪L v, L w⟫ = 0` for every `w` has `⟪L v, L v⟫ = 0`, so `L v = 0`. -/
theorem nondegenerate_inner_comp {V : Type*} [AddCommGroup V] [Module ℝ V] {L : V →ₗ[ℝ] E}
    (hL : Function.Injective L) : (LinearMap.BilinForm.comp (innerₗ E) L L).Nondegenerate :=
  ⟨fun v hv ↦ hL <| by simpa using hv v, fun w hw ↦ hL <| by simpa using hw w⟩

/-- For an injective linear map `L`, a vector `u` is determined by the pairings `⟪L u, L w⟫` of the
pulled-back inner product. -/
theorem eq_of_forall_inner_comp {V : Type*} [AddCommGroup V] [Module ℝ V] {L : V →ₗ[ℝ] E}
    (hL : Function.Injective L) {u u' : V} (H : ∀ w, ⟪L u, L w⟫ = ⟪L u', L w⟫) : u = u' := by
  rw [← sub_eq_zero]
  refine (nondegenerate_inner_comp hL).1 _ fun w ↦ ?_
  simp [H]

end TauCeti
