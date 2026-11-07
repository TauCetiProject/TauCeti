/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Corner
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Bounded operators from uniformly bounded finite matrices

A countable matrix represents a bounded operator in a Hilbert basis exactly when its
leading square matrices have uniformly bounded Euclidean operator norms. The same bound
works for the resulting operator. This permits constructing an infinite operator from
finite matrix estimates without assuming square summability of its columns in advance.

The construction uses Mathlib's `lp.memℓp_of_tendsto` for square summability of the
coordinatewise limits and `LinearMap.extendOfNorm` for extension from the dense span.
-/

public section

open scoped InnerProductSpace Topology
open Filter

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Finite compression is the Euclidean operator of the corresponding matrix of inner products. -/
theorem finiteSection_eq_toEuclideanCLM (T : H →L[𝕜] H) (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    T.finiteSection b n = Matrix.toEuclideanCLM (𝕜 := 𝕜)
      (Matrix.of fun i j : Fin (n + 1) ↦ ⟪b i, T (b j)⟫_𝕜) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (n + 1)) 𝕜).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  simpa [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct, PiLp.single_apply] using
    T.finiteSection_single_apply b n i j

end ContinuousLinearMap

namespace HilbertBasis

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Uniformly bounded leading square matrices determine a bounded operator, with the same
norm bound, in any natural-number-indexed Hilbert basis. -/
theorem exists_operator_iff_matrix_bound (b : HilbertBasis ℕ 𝕜 H)
    (A : ℕ → ℕ → 𝕜) {C : ℝ} (hC : 0 ≤ C) :
    (∃ T : H →L[𝕜] H, ‖T‖ ≤ C ∧ ∀ i j, ⟪b i, T (b j)⟫_𝕜 = A i j) ↔
      ∀ n : ℕ, ‖Matrix.toEuclideanCLM (𝕜 := 𝕜)
        (Matrix.of fun i j : Fin (n + 1) ↦ A i j)‖ ≤ C := by
  classical
  constructor
  · rintro ⟨T, hT, hentry⟩ n
    have hmatrix := T.finiteSection_eq_toEuclideanCLM b n
    simp only [hentry] at hmatrix
    rw [← hmatrix]
    exact (T.norm_finiteSection_le b n).trans hT
  intro hA
  let e : (ℕ →₀ 𝕜) →ₗ[𝕜] H := Finsupp.linearCombination 𝕜 b
  let a : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ → 𝕜) :=
    Finsupp.linearCombination 𝕜 (fun j i ↦ A i j)
  let Q (n : ℕ) : H →L[𝕜] H := (b.finiteInclusion n).cornerEmbedding
    (Matrix.toEuclideanCLM (𝕜 := 𝕜) (Matrix.of fun i j : Fin (n + 1) ↦ A i j))
  have hQ (n : ℕ) : ‖Q n‖ ≤ C := by
    simpa only [Q, LinearIsometry.norm_map] using hA n
  -- Each matrix entry of the zero extensions stabilizes once both indices are included.
  have hentry (i j : ℕ) : ∀ᶠ n : ℕ in atTop, b.repr (Q n (b j)) i = A i j := by
    filter_upwards [eventually_ge_atTop (max i j)] with n hn
    have hi : i < n + 1 := by omega
    have hj : j < n + 1 := by omega
    rw [b.repr_apply_apply, ← ContinuousLinearMap.finiteSection_single_apply
      (Q n) b n ⟨i, hi⟩ ⟨j, hj⟩, finiteSection_cornerEmbedding]
    simp [Matrix.mulVec, dotProduct, PiLp.single_apply]
  -- Finite linear combinations therefore converge coordinatewise under the zero extensions.
  have hlim (x : ℕ →₀ 𝕜) (i : ℕ) :
      ∀ᶠ n : ℕ in atTop, b.repr (Q n (e x)) i = a x i := by
    induction x using Finsupp.induction_linear with
    | zero => exact Eventually.of_forall fun n ↦ by simp [e, a]
    | add x y hx hy =>
      filter_upwards [hx, hy] with n hx hy
      simp only [map_add, lp.coeFn_add, Pi.add_apply, hx, hy]
    | single j c =>
      filter_upwards [hentry i j] with n hn
      simp [e, a, Finsupp.linearCombination_single, hn]
  have htendsto (x : ℕ →₀ 𝕜) :
      Tendsto (fun n ↦ ⇑(b.repr (Q n (e x)))) atTop (𝓝 (a x)) :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_const_nhds.congr' ((hlim x i).mono fun _ hn ↦ hn.symm)
  have hbound (x : ℕ →₀ 𝕜) (n : ℕ) : ‖b.repr (Q n (e x))‖ ≤ C * ‖e x‖ := by
    rw [b.repr.norm_map]
    exact (Q n).le_opNorm (e x) |>.trans (mul_le_mul_of_nonneg_right (hQ n) (norm_nonneg _))
  -- Semicontinuity of the native ℓ² norm supplies the actual square-summable output.
  have hmem (x : ℕ →₀ 𝕜) : Memℓp (a x) 2 :=
    lp.memℓp_of_tendsto (isBounded_iff_forall_norm_le.mpr
      ⟨C * ‖e x‖, by simpa only [Set.forall_mem_range] using hbound x⟩) (htendsto x)
  let f : (ℕ →₀ 𝕜) →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
    { toFun x := ⟨a x, hmem x⟩
      map_add' x y := lp.ext (a.map_add x y)
      map_smul' c x := lp.ext (a.map_smul c x) }
  let g : (ℕ →₀ 𝕜) →ₗ[𝕜] H := b.repr.symm.toLinearEquiv.toLinearMap.comp f
  have hg (x : ℕ →₀ 𝕜) : ‖g x‖ ≤ C * ‖e x‖ := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv,
      b.repr.symm.norm_map]
    exact lp.norm_le_of_tendsto (Eventually.of_forall (hbound x)) (htendsto x)
  have he : DenseRange e := by
    rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  refine ⟨g.extendOfNorm e, g.opNorm_extendOfNorm_le he hC hg, fun i j ↦ ?_⟩
  have hsingle := g.extendOfNorm_eq he ⟨C, hg⟩ (Finsupp.single j 1)
  simp only [e, Finsupp.linearCombination_single, one_smul] at hsingle
  rw [hsingle, ← b.repr_apply_apply]
  simp [g, f, a, Finsupp.linearCombination_single]

end HilbertBasis
