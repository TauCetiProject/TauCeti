/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The signature of the quadratic form of a symmetric operator

Let `T` be a symmetric operator on a finite-dimensional real inner product space `E`, and `Q` the
quadratic form `x ↦ ⟪T x, x⟫`. In an orthonormal eigenbasis of `T`, the form `Q` is the weighted
sum of squares whose weights are the eigenvalues of `T`. By Sylvester's law of inertia, the
negative index `sigNeg Q` of `Q` is therefore the number of negative eigenvalues of `T`, counted
with multiplicity, which is the dimension of the point-spectral subspace of `T` for `(-∞, 0)`;
likewise the positive index `sigPos Q` is the dimension of the point-spectral subspace for
`(0, ∞)`.

This identifies the two descriptions of a Morse index used side by side in the theory of the
trajectory operator `d/ds + A(s)`: as the negative index of a symmetric bilinear form, the form in
which crossing forms and their signatures are stated, and as the number of negative eigenvalues of
a symmetric operator, the form in which the Fredholm index is computed.

The form `Q` is passed together with the identity `Q x = ⟪T x, x⟫`, so the results apply to any
presentation of it, such as a Hessian quadratic form or the diagonal of a continuous bilinear form.

## Main results

In the namespace `LinearMap.IsSymmetric`:

* `equivalent_weightedSumSquares_eigenvalues`: `Q` is equivalent to the weighted sum of squares
  with the eigenvalues of `T` as weights.
* `sigNeg_eq_ncard_eigenvalues_neg`, `sigPos_eq_ncard_eigenvalues_pos`: the negative and positive
  indices of `Q` count the negative and positive eigenvalues of `T`.
* `sigNeg_eq_finrank_pointSpectralSubspace`: the negative index of `Q` is the dimension of the
  negative point-spectral subspace of `T`.
* `sigPos_eq_finrank_pointSpectralSubspace`: the positive index of `Q` is the dimension of the
  positive point-spectral subspace of `T`.
* `isSymm_toBilinForm_innerSL_comp`, `sigNeg_toBilinForm_innerSL_comp`,
  `sigPos_toBilinForm_innerSL_comp`: the continuous bilinear form `⟪T ·, ·⟫` is symmetric, and its
  negative and positive indices count the negative and positive eigenvalues of `T`.

In the namespace `ContinuousLinearMap`:

* `nondegenerate_toBilinForm_innerSL_comp_iff`: the form `⟪T ·, ·⟫` of an operator `T` is
  nondegenerate exactly when `T` is injective.
-/

public section

open Set
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →ₗ[ℝ] E} {Q : QuadraticForm ℝ E}

/-- The quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is equivalent to the weighted
sum of squares whose weights are the eigenvalues of `T`: an orthonormal eigenbasis diagonalizes
it. -/
theorem equivalent_weightedSumSquares_eigenvalues (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ (hT.eigenvalues hn)) := by
  subst hn
  let b := hT.eigenvectorBasis rfl
  -- The polar form of `Q` is `⟪T x, y⟫`, because `T` is symmetric.
  have hassoc (x y : E) : QuadraticMap.associated Q x y = ⟪T x, y⟫_ℝ := by
    rw [QuadraticMap.associated_apply, hQ, hQ, hQ, map_add, inner_add_left, inner_add_right,
      inner_add_right, hT y x, real_inner_comm (T x) y]
    simp [invOf_eq_inv]
    ring
  have hb (i : Fin (Module.finrank ℝ E)) : T (b i) = hT.eigenvalues rfl i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have horth : (QuadraticMap.associated Q).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    rw [hassoc, hb, real_inner_smul_left, orthonormal_iff_ite.mp b.orthonormal i j]
    simp [hij]
  have hweights : (fun i ↦ Q (b i)) = hT.eigenvalues rfl := by
    funext i
    rw [hQ, hb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow,
      mul_one]
  rw [← hweights]
  exact ⟨QuadraticForm.isometryEquivWeightedSumSquares Q b.toBasis horth⟩

/-- The negative index of the quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the
number of negative eigenvalues of `T`, counted with multiplicity. -/
theorem sigNeg_eq_ncard_eigenvalues_neg (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigNeg Q = {i | hT.eigenvalues hn i < 0}.ncard :=
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (hT.equivalent_weightedSumSquares_eigenvalues hn hQ)

/-- The positive index of the quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the
number of positive eigenvalues of `T`, counted with multiplicity. -/
theorem sigPos_eq_ncard_eigenvalues_pos (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigPos Q = {i | 0 < hT.eigenvalues hn i}.ncard :=
  QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (hT.equivalent_weightedSumSquares_eigenvalues hn hQ)

/-- **The negative index of the form of a symmetric operator.** The negative index of the
quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the dimension of the sum of the
eigenspaces of `T` at negative eigenvalues. -/
theorem sigNeg_eq_finrank_pointSpectralSubspace (hT : T.IsSymmetric)
    (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigNeg Q = Module.finrank ℝ (Module.End.pointSpectralSubspace T (Iio 0)) := by
  rw [hT.finrank_pointSpectralSubspace rfl, hT.sigNeg_eq_ncard_eigenvalues_neg rfl hQ]
  rfl

/-- **The positive index of the form of a symmetric operator.** The positive index of the
quadratic form `x ↦ ⟪T x, x⟫` of a symmetric operator `T` is the dimension of the sum of the
eigenspaces of `T` at positive eigenvalues. -/
theorem sigPos_eq_finrank_pointSpectralSubspace (hT : T.IsSymmetric)
    (hQ : ∀ x, Q x = ⟪T x, x⟫_ℝ) :
    sigPos Q = Module.finrank ℝ (Module.End.pointSpectralSubspace T (Ioi 0)) := by
  rw [hT.finrank_pointSpectralSubspace rfl, hT.sigPos_eq_ncard_eigenvalues_pos rfl hQ]
  rfl

/-! ### The bilinear form of an operator -/

omit [FiniteDimensional ℝ E] in
/-- The continuous bilinear form `⟪T ·, ·⟫` of a symmetric operator `T` is symmetric. -/
theorem isSymm_toBilinForm_innerSL_comp {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ((innerSL ℝ).comp T).toBilinForm.IsSymm :=
  ContinuousLinearMap.isSymm_toBilinForm_iff.2 fun u v ↦ by
    simpa [real_inner_comm u] using hT u v

/-- The negative index of the continuous bilinear form `⟪T ·, ·⟫` of a symmetric operator `T` is
the dimension of the sum of the eigenspaces of `T` at negative eigenvalues. -/
theorem sigNeg_toBilinForm_innerSL_comp {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    sigNeg ((innerSL ℝ).comp T).toBilinForm.toQuadraticMap =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Iio 0)) :=
  hT.sigNeg_eq_finrank_pointSpectralSubspace fun x ↦ by simp

/-- The positive index of the continuous bilinear form `⟪T ·, ·⟫` of a symmetric operator `T` is
the dimension of the sum of the eigenspaces of `T` at positive eigenvalues. -/
theorem sigPos_toBilinForm_innerSL_comp {T : E →L[ℝ] E} (hT : (T : E →ₗ[ℝ] E).IsSymmetric) :
    sigPos ((innerSL ℝ).comp T).toBilinForm.toQuadraticMap =
      Module.finrank ℝ (Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Ioi 0)) :=
  hT.sigPos_eq_finrank_pointSpectralSubspace fun x ↦ by simp

end LinearMap.IsSymmetric

/-- On a finite-dimensional real inner product space, the continuous bilinear form `⟪T ·, ·⟫` of an
operator `T` is nondegenerate exactly when `T` is injective. -/
theorem ContinuousLinearMap.nondegenerate_toBilinForm_innerSL_comp_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →L[ℝ] E} :
    ((innerSL ℝ).comp T).toBilinForm.Nondegenerate ↔ LinearMap.ker (T : E →ₗ[ℝ] E) = ⊥ := by
  rw [nondegenerate_toBilinForm_iff_injective, LinearMap.ker_eq_bot, coe_coe,
    injective_iff_map_eq_zero, injective_iff_map_eq_zero]
  refine forall_congr' fun u ↦ imp_congr_left ?_
  rw [comp_apply, ← norm_eq_zero, innerSL_apply_norm, norm_eq_zero]
