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
requires of its bilinear form.
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

end TauCeti
