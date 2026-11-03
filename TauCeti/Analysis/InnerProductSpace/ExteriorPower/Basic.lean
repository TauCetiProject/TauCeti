/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.Algebra.Lie.ExteriorPower
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Norms and linear isometries of exterior powers

The exterior powers `⋀[ℝ]^n E` of a finite-dimensional real inner product space carry Mathlib's
induced inner product, with `⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det ⟪vⱼ, wᵢ⟫`. This file proves that the
map `⋀ⁿ f` induced by a linear isometry `f` preserves it, so that rotations of an oriented space
act isometrically on its forms, and that infinitesimal rotations, the skew-adjoint endomorphisms,
act skew-adjointly on forms of every degree. It also records that the norm of a wedge
`v₁ ∧ ⋯ ∧ vₙ` is the volume of the parallelepiped spanned by the `vᵢ`, bounded by Hadamard's
inequality.

## Main results

* `exteriorPower.inner_map_map`: `⟪⋀ⁿ f x, ⋀ⁿ f y⟫ = ⟪x, y⟫` for a linear isometry `f`.
* `exteriorPower.inner_ιMulti_two`: `⟪a ∧ b, u ∧ w⟫ = ⟪a, u⟫ ⟪b, w⟫ - ⟪a, w⟫ ⟪b, u⟫`.
* `exteriorPower.ext_inner_ιMulti`: elements of `⋀ⁿ E` with the same inner products against all
  wedges of vectors are equal, and `exteriorPower.linearMap_ext_inner_ιMulti` is the
  corresponding extensionality principle for linear maps between exterior powers;
  `exteriorPower.ext_inner_ιMulti_two` and `exteriorPower.linearMap_ext_inner_ιMulti_two` test
  only against wedges `u ∧ w` of two vectors.
* `exteriorPower.inner_lieMap_left`: the derivation action `D_A` of a skew-adjoint `A` on
  `⋀ⁿ E` is skew-adjoint, `⟪D_A x, y⟫ = -⟪x, D_A y⟫`.
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

/-- The inner product of two wedges of two vectors is their `2 × 2` Gram determinant. -/
theorem inner_ιMulti_two (a b u w : E) :
    ⟪ιMulti ℝ 2 ![a, b], ιMulti ℝ 2 ![u, w]⟫ = ⟪a, u⟫ * ⟪b, w⟫ - ⟪a, w⟫ * ⟪b, u⟫ := by
  simp [inner_ιMulti_ιMulti, Matrix.det_fin_two]
  ring

/-- Elements of `⋀ⁿ E` are determined by their inner products with wedges of vectors, since these
wedges span `⋀ⁿ E`. -/
theorem ext_inner_ιMulti {x y : ⋀[ℝ]^n E} (h : ∀ v, ⟪x, ιMulti ℝ n v⟫ = ⟪y, ιMulti ℝ n v⟫) :
    x = y := by
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
  have : innerₗ (⋀[ℝ]^n E) (x - y) = 0 := by
    refine LinearMap.ext_on (ιMulti_span ℝ n E) ?_
    rintro _ ⟨v, rfl⟩
    simp [h]
  simpa only [innerₗ_apply_apply, LinearMap.zero_apply] using LinearMap.congr_fun this (x - y)

omit [FiniteDimensional ℝ E] in
/-- Linear maps `⋀ⁿ E → ⋀ᵐ F` agree when their values on wedges of vectors have the same inner
products with all wedges of vectors. -/
theorem linearMap_ext_inner_ιMulti {m : ℕ} {f g : ⋀[ℝ]^n E →ₗ[ℝ] ⋀[ℝ]^m F}
    (h : ∀ v w, ⟪f (ιMulti ℝ n v), ιMulti ℝ m w⟫ = ⟪g (ιMulti ℝ n v), ιMulti ℝ m w⟫) :
    f = g :=
  linearMap_ext (AlternatingMap.ext fun v ↦ ext_inner_ιMulti (h v))

/-- Two-vectors are determined by their inner products with the wedges `u ∧ w` of two vectors:
the form of `ext_inner_ιMulti` whose hypothesis matches the lemmas stated for `ιMulti ℝ 2 ![u, w]`,
such as `inner_ιMulti_two`. -/
theorem ext_inner_ιMulti_two {x y : ⋀[ℝ]^2 E}
    (h : ∀ u w, ⟪x, ιMulti ℝ 2 ![u, w]⟫ = ⟪y, ιMulti ℝ 2 ![u, w]⟫) : x = y :=
  ext_inner_ιMulti fun v ↦ by
    rw [← FinVec.etaExpand_eq v]
    exact h (v 0) (v 1)

omit [FiniteDimensional ℝ E] in
/-- Linear maps `⋀² E → ⋀² F` agree when their values on wedges `a ∧ b` have the same inner
products with all wedges `u ∧ w`: the two-vector form of `linearMap_ext_inner_ιMulti`. -/
theorem linearMap_ext_inner_ιMulti_two {f g : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^2 F}
    (h : ∀ a b u w, ⟪f (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ =
      ⟪g (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫) :
    f = g :=
  linearMap_ext (AlternatingMap.ext fun v ↦ ext_inner_ιMulti_two fun u w ↦ by
    rw [← FinVec.etaExpand_eq v]
    exact h (v 0) (v 1) u w)

/-- **Skew-adjoint endomorphisms act skew-adjointly on exterior powers**: if
`⟪A u, w⟫ = -⟪u, A w⟫` for all `u, w`, then the derivation action `D_A` on `⋀ⁿ E`, which applies
`A` to one factor of a wedge at a time, satisfies `⟪D_A x, y⟫ = -⟪x, D_A y⟫`. -/
theorem inner_lieMap_left {A : E →ₗ[ℝ] E}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x y : ⋀[ℝ]^n E) :
    ⟪lieMap n A x, y⟫ = -⟪x, lieMap n A y⟫ := by
  -- On wedges, the two sides are sums of Gram determinants with one column, respectively one
  -- row, replaced; by Jacobi's formula both sums are traces against the adjugate.
  have key (v w : Fin n → E) :
      ⟪lieMap n A (ιMulti ℝ n v), ιMulti ℝ n w⟫ =
        -⟪ιMulti ℝ n v, lieMap n A (ιMulti ℝ n w)⟫ := by
    let G : Matrix (Fin n) (Fin n) ℝ := .of fun i j ↦ ⟪v j, w i⟫
    let B : Matrix (Fin n) (Fin n) ℝ := .of fun i j ↦ ⟪v j, A (w i)⟫
    have hcol (j : Fin n) : (Matrix.of fun i c ↦ ⟪Function.update v j (A (v j)) c, w i⟫) =
        G.updateCol j fun i ↦ (-B) i j := by
      ext i c
      rcases eq_or_ne c j with rfl | h
      · simp [G, B, hA]
      · simp [G, B, h]
    have hrow (i : Fin n) : (Matrix.of fun r c ↦ ⟪v c, Function.update w i (A (w i)) r⟫) =
        G.updateRow i (B i) := by
      ext r c
      rcases eq_or_ne r i with rfl | h
      · simp [G, B]
      · simp [G, B, h]
    simp only [lieMap_apply_ιMulti, sum_inner, inner_sum, inner_ιMulti_ιMulti, hcol, hrow,
      Matrix.sum_det_updateCol_eq_trace_adjugate_mul,
      Matrix.sum_det_updateRow_eq_trace_adjugate_mul, Matrix.mul_neg, Matrix.trace_neg]
  have hbil : (innerₗ (⋀[ℝ]^n E)).compl₁₂ (lieMap n A) LinearMap.id =
      -(innerₗ (⋀[ℝ]^n E)).compl₂ (lieMap n A) :=
    linearMap_ext (AlternatingMap.ext fun v ↦ linearMap_ext (AlternatingMap.ext fun w ↦ by
      simpa only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
        LinearMap.compl₂_apply, LinearMap.neg_apply, LinearMap.id_apply, innerₗ_apply_apply]
        using key v w))
  simpa using LinearMap.congr_fun₂ hbil x y

/-- The squared norm of a wedge of vectors is their Gram determinant. -/
theorem norm_ιMulti_sq (v : Fin n → E) : ‖ιMulti ℝ n v‖ ^ 2 = (Matrix.gram ℝ v).det := by
  rw [← real_inner_self_eq_norm_sq, inner_ιMulti_self]

/-- **Hadamard's inequality** for wedges: `‖v₁ ∧ ⋯ ∧ vₙ‖ ≤ ‖v₁‖ ⋯ ‖vₙ‖`. -/
theorem norm_ιMulti_le_prod_norm (v : Fin n → E) : ‖ιMulti ℝ n v‖ ≤ ∏ i, ‖v i‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_ιMulti_sq, ← Finset.prod_pow]
  simpa using Matrix.re_det_gram_le_prod_norm_sq (𝕜 := ℝ) v

end exteriorPower
