/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard

/-!
# Integral Gram matrices and weighted Euclidean realizations

An integer-valued family `x : α → ℤ` with nonnegative weights `w : α → ℝ` embeds `ℤ`-linearly
into `EuclideanSpace ℝ α` via `TauCeti.weightedToLp w x`, multiplying coordinate `a` by
`Real.sqrt (w a)` so that the Euclidean inner product equals `∑ a, w a * x a * y a`.

More generally, whenever an integer matrix `G : Matrix ι ι ℤ` agrees after coercion to `ℝ` with
the Gram matrix `Matrix.gram ℝ v` of a finite family `v` in a real inner product space,
`(G.det : ℝ) = (Matrix.gram ℝ v).det`. Linear independence of `v` therefore yields `1 ≤ G.det`
and Hadamard's logarithmic bound `Real.log (G.det : ℝ) ≤ ∑ i, 2 * Real.log ‖v i‖`.

## Main results

* `TauCeti.weightedToLp`: bundled `ℤ`-linear weighted Euclidean realization
  `(α → ℤ) →ₗ[ℤ] EuclideanSpace ℝ α`.
* `TauCeti.inner_weightedToLp`, `TauCeti.norm_sq_weightedToLp`: inner product and squared norm of
  `TauCeti.weightedToLp`.
* `Matrix.intCast_det_eq_det_gram`: determinant agreement between an integer matrix `G` and the
  real Gram matrix `Matrix.gram ℝ v` when `G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v`.
* `Matrix.one_le_det_of_map_eq_gram`, `Matrix.log_det_le_of_map_eq_gram`: positivity `1 ≤ G.det`
  and Hadamard's logarithmic upper bound for linearly independent `v`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- Weighted Euclidean realization `(α → ℤ) →ₗ[ℤ] EuclideanSpace ℝ α`, scaling coordinate `a` by
`Real.sqrt (w a)`. -/
noncomputable def weightedToLp {α : Type*} (w : α → ℝ) : (α → ℤ) →ₗ[ℤ] EuclideanSpace ℝ α where
  toFun x := WithLp.toLp 2 fun a ↦ Real.sqrt (w a) * (x a : ℝ)
  map_add' x y := by
    ext a
    simp [mul_add]
  map_smul' c x := by
    ext a
    simp [zsmul_eq_mul]
    ring

/-- Coordinate evaluation of `TauCeti.weightedToLp`. -/
@[simp]
theorem weightedToLp_ofLp {α : Type*} (w : α → ℝ) (x : α → ℤ) (a : α) :
    (weightedToLp w x).ofLp a = Real.sqrt (w a) * (x a : ℝ) := by
  rfl

/-- Inner product of two weighted Euclidean realizations when the weights `w` are nonnegative. -/
theorem inner_weightedToLp {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (x y : α → ℤ) :
    ⟪weightedToLp w x, weightedToLp w y⟫_ℝ = ∑ a : α, w a * (x a : ℝ) * (y a : ℝ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [weightedToLp_ofLp, RCLike.inner_apply, conj_trivial]
  linear_combination (x a : ℝ) * (y a : ℝ) * Real.mul_self_sqrt (hw a)

/-- Squared norm of a weighted Euclidean realization when the weights `w` are nonnegative. -/
theorem norm_sq_weightedToLp {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (x : α → ℤ) :
    ‖weightedToLp w x‖ ^ 2 = ∑ a : α, w a * (x a : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_weightedToLp hw]
  refine Finset.sum_congr rfl fun a _ ↦ by ring

end TauCeti

namespace Matrix

/-- If an integer matrix `G` agrees after coercion to `ℝ` with `Matrix.gram ℝ v`, then their
determinants agree in `ℝ`. -/
theorem intCast_det_eq_det_gram {ι E : Type*} [Fintype ι] [DecidableEq ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {G : Matrix ι ι ℤ} {v : ι → E}
    (hG : G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v) :
    (G.det : ℝ) = (Matrix.gram ℝ v).det := by
  rw [← hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]

/-- An integer matrix matching the Gram matrix of a linearly independent real family has
determinant at least `1`. -/
theorem one_le_det_of_map_eq_gram {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {G : Matrix ι ι ℤ} {v : ι → E}
    (hG : G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v) (hv : LinearIndependent ℝ v) :
    1 ≤ G.det := by
  have hpos : (0 : ℝ) < (G.det : ℝ) :=
    intCast_det_eq_det_gram hG ▸ Matrix.det_gram_pos_iff.mpr hv
  exact Int.add_one_le_of_lt (by exact_mod_cast hpos)

/-- Logarithmic Hadamard bound for an integer matrix matching the Gram matrix of a linearly
independent real family. -/
theorem log_det_le_of_map_eq_gram {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {G : Matrix ι ι ℤ} {v : ι → E}
    (hG : G.map (Int.castRingHom ℝ) = Matrix.gram ℝ v) (hv : LinearIndependent ℝ v) :
    Real.log (G.det : ℝ) ≤ ∑ i : ι, 2 * Real.log ‖v i‖ := by
  rw [intCast_det_eq_det_gram hG]
  exact Matrix.log_det_gram_le hv

end Matrix
