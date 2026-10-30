/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard

/-!
# Norms and linear isometries of exterior powers

The exterior powers `⋀[ℝ]^n E` of a finite-dimensional real inner product space carry Mathlib's
induced inner product, with `⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det ⟪vⱼ, wᵢ⟫`. This file proves that the
map `⋀ⁿ f` induced by a linear isometry `f` preserves it, so that rotations of an oriented space
act isometrically on its forms. It also records that the norm of a wedge `v₁ ∧ ⋯ ∧ vₙ` is the
volume of the parallelepiped spanned by the `vᵢ`, bounded by Hadamard's inequality.

## Main results

* `exteriorPower.inner_map_map`: `⟪⋀ⁿ f x, ⋀ⁿ f y⟫ = ⟪x, y⟫` for a linear isometry `f`.
* `exteriorPower.norm_ιMulti_sq`: `‖v₁ ∧ ⋯ ∧ vₙ‖ ^ 2` is the Gram determinant of `v`.
* `exteriorPower.norm_ιMulti_le_prod_norm`: Hadamard's inequality `‖v₁ ∧ ⋯ ∧ vₙ‖ ≤ ∏ ‖vᵢ‖`.
-/

public section

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

/-- The map of exterior powers induced by a linear isometry preserves the inner product. -/
theorem inner_map_map (f : E →ₗᵢ[ℝ] F) (x y : ⋀[ℝ]^n E) :
    ⟪map n f.toLinearMap x, map n f.toLinearMap y⟫ = ⟪x, y⟫ := by
  -- On wedge products both sides are the Gram determinants of the same inner products.
  have key (u v : Fin n → E) :
      ⟪map n f.toLinearMap (ιMulti ℝ n u), map n f.toLinearMap (ιMulti ℝ n v)⟫ =
        ⟪ιMulti ℝ n u, ιMulti ℝ n v⟫ := by
    simp [map_apply_ιMulti, inner_ιMulti_ιMulti, Function.comp_def]
  have hx : x ∈ Submodule.span ℝ (Set.range (ιMulti ℝ n)) := by rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hy : y ∈ Submodule.span ℝ (Set.range (ιMulti ℝ n)) := by rw [ιMulti_span]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨v, rfl⟩ := hy; exact key u v
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz]
    | smul r y _ hy => simp only [map_smul, real_inner_smul_right, hy]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz]
  | smul r x _ hx => simp only [map_smul, real_inner_smul_left, hx]

/-- The squared norm of a wedge of vectors is their Gram determinant. -/
theorem norm_ιMulti_sq (v : Fin n → E) : ‖ιMulti ℝ n v‖ ^ 2 = (Matrix.gram ℝ v).det := by
  rw [← real_inner_self_eq_norm_sq, inner_ιMulti_self]

/-- **Hadamard's inequality** for wedges: `‖v₁ ∧ ⋯ ∧ vₙ‖ ≤ ‖v₁‖ ⋯ ‖vₙ‖`. -/
theorem norm_ιMulti_le_prod_norm (v : Fin n → E) : ‖ιMulti ℝ n v‖ ≤ ∏ i, ‖v i‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_ιMulti_sq, ← Finset.prod_pow]
  simpa using Matrix.re_det_gram_le_prod_norm_sq (𝕜 := ℝ) v

end exteriorPower
