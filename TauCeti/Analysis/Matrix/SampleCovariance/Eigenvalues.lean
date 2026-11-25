/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Matrix.Eigenvalues.Gram
public import TauCeti.Analysis.Matrix.SampleSecondMoment
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.SampleCovariance.Rank
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Eigenvalues of sample covariance matrices

The square roots of the ordered eigenvalues of the sample covariance of a data matrix
are its ordered singular values divided by the square root of the sample size. This
gives a perturbation bound directly in the Euclidean operator norm of the data, including
near a zero eigenvalue. Applying the same identity to the adjoint compares the two
covariance matrices with their distinct normalizations.
-/

public section

open Filter
open scoped Matrix.Norms.L2Operator Topology

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype n]

/-- The sample covariance is the row Gram matrix of the data scaled by the reciprocal square
root of the sample size. Both sides are zero for an empty sample. -/
theorem sampleCovariance_eq_mul_conjTranspose_self_inv_sqrt_smul (X : Matrix m n 𝕜) :
    X.sampleCovariance =
      ((√(Fintype.card n : ℝ))⁻¹ • X) * ((√(Fintype.card n : ℝ))⁻¹ • X)ᴴ := by
  rw [sampleCovariance_def, conjTranspose_smul, star_trivial, smul_mul, Matrix.mul_smul,
    smul_smul, ← sq, inv_pow, Real.sq_sqrt (by positivity), one_div]

variable [Fintype m] [DecidableEq m] [DecidableEq n]

/-- The ordered eigenvalues of a sample covariance matrix are the squared singular values of
the data divided by the sample size. This includes the zero eigenvalues of a rank-deficient
covariance and the empty-sample convention. -/
theorem eigenvalues₀_sampleCovariance (X : Matrix m n 𝕜) (i : Fin (Fintype.card m)) :
    (isHermitian_sampleCovariance X).eigenvalues₀ i =
      (toEuclideanLin X).singularValues i ^ 2 / Fintype.card n := by
  rw [congrFun (IsHermitian.eigenvalues₀_congr
    (sampleCovariance_eq_mul_conjTranspose_self_inv_sqrt_smul X) (isHermitian_sampleCovariance X)
    (isHermitian_mul_conjTranspose_self _)) i,
    eigenvalues₀_mul_conjTranspose_self_eq_sq_singularValues,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smul, LinearMap.singularValues_smul,
    Finsupp.smul_apply, smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
    mul_pow, inv_pow, Real.sq_sqrt (by positivity), div_eq_mul_inv, mul_comm]

/-- The square root of each ordered sample covariance eigenvalue is Lipschitz in the data
matrix for the Euclidean operator norm, with constant the reciprocal square root of the
sample size. -/
theorem abs_sqrt_eigenvalues₀_sampleCovariance_sub_le (X Y : Matrix m n 𝕜)
    (i : Fin (Fintype.card m)) :
    |√((isHermitian_sampleCovariance X).eigenvalues₀ i) -
      √((isHermitian_sampleCovariance Y).eigenvalues₀ i)| ≤ ‖X - Y‖ / √(Fintype.card n) := by
  rw [eigenvalues₀_sampleCovariance, eigenvalues₀_sampleCovariance, Real.sqrt_div (by positivity),
    Real.sqrt_div (by positivity), Real.sqrt_sq (LinearMap.singularValues_nonneg _ _),
    Real.sqrt_sq (LinearMap.singularValues_nonneg _ _), ← sub_div, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  simpa only [l2_opNorm_def, LinearEquiv.trans_apply, map_sub] using
    (toEuclideanLin X).abs_singularValues_sub_singularValues_le (toEuclideanLin Y) i

/-- At a common index, the covariance eigenvalue of the data is the corresponding eigenvalue
of the covariance of the adjoint times the ratio of row count to column count. -/
theorem eigenvalues₀_sampleCovariance_eq_div_mul_eigenvalues₀_sampleCovariance_conjTranspose
    (X : Matrix m n 𝕜) (i : Fin (Fintype.card m)) (j : Fin (Fintype.card n)) (hij : i.val = j.val) :
    (isHermitian_sampleCovariance X).eigenvalues₀ i = ((Fintype.card m : ℝ) / Fintype.card n) *
      (isHermitian_sampleCovariance Xᴴ).eigenvalues₀ j := by
  have hm : (Fintype.card m : ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  rw [eigenvalues₀_sampleCovariance, eigenvalues₀_sampleCovariance,
    toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.singularValues_adjoint, hij,
    div_mul_div_comm, mul_comm (Fintype.card n : ℝ), ← div_div, mul_div_cancel_left₀ _ hm]

omit [DecidableEq n] in
/-- Every ordered covariance eigenvalue at or beyond the number of samples is zero. -/
theorem eigenvalues₀_sampleCovariance_eq_zero_of_card_le
    (X : Matrix m n 𝕜) (i : Fin (Fintype.card m)) (hi : Fintype.card n ≤ (i : ℕ)) :
    (isHermitian_sampleCovariance X).eigenvalues₀ i = 0 :=
  (posSemidef_sampleCovariance X).eigenvalues₀_eq_zero_of_rank_le
    ((rank_sampleCovariance X).trans_le X.rank_le_card_width) i hi

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- If the ratio of row count to sample size tends to a number greater than one, the
least covariance eigenvalue is eventually zero, for arbitrary data matrices. -/
theorem eventually_eigenvalues₀_card_sub_one_sampleCovariance_eq_zero_of_one_lt_ratio
    {ι : Type*} {p q : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (q i)]
    [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)] {l : Filter ι} {r : ℝ}
    (X : (i : ι) → Matrix (p i) (q i) 𝕜) (hr : 1 < r)
    (h : Tendsto (fun i ↦ (Fintype.card (p i) : ℝ) / Fintype.card (q i)) l (𝓝 r)) :
    ∀ᶠ i in l, (isHermitian_sampleCovariance (X i)).eigenvalues₀
      ⟨Fintype.card (p i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩ = 0 := by
  filter_upwards [h.eventually (lt_mem_nhds hr)] with i hi
  have hq : Fintype.card (q i) ≠ 0 := by
    intro hq
    norm_num [hq] at hi
  have hlt : Fintype.card (q i) < Fintype.card (p i) := by
    exact_mod_cast (one_lt_div (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq))).mp hi
  exact eigenvalues₀_sampleCovariance_eq_zero_of_card_le (X i) _ (Nat.le_sub_one_of_lt hlt)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- A lower spectral bound for sample covariances is stable under perturbations of the data
that tend to zero in operator norm after division by the square root of the sample size. -/
theorem eventually_lt_eigenvalues₀_sampleCovariance_of_tendsto_norm_sub_div_sqrt
    {ι : Type*} {p q : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (q i)]
    [∀ i, DecidableEq (p i)] [∀ i, DecidableEq (q i)] {l : Filter ι}
    {X Y : (i : ι) → Matrix (p i) (q i) 𝕜} {r : ℝ}
    (hXY : Tendsto (fun i ↦ ‖X i - Y i‖ / √(Fintype.card (q i))) l (𝓝 0))
    (hY : ∀ c < r, ∀ᶠ i in l, ∀ k, c < (isHermitian_sampleCovariance (Y i)).eigenvalues₀ k) :
    ∀ c < r, ∀ᶠ i in l, ∀ k, c < (isHermitian_sampleCovariance (X i)).eigenvalues₀ k := by
  intro c hc
  by_cases hc₀ : 0 ≤ c
  · let δ := (√r - √c) / 2
    have hδ : 0 < δ := half_pos (sub_pos.mpr (Real.sqrt_lt_sqrt hc₀ hc))
    have hmid : √c + δ < √r := by dsimp only [δ] at hδ ⊢; linarith
    have hnonneg : 0 ≤ √c + δ := add_nonneg (Real.sqrt_nonneg _) hδ.le
    filter_upwards [hY _ ((Real.lt_sqrt hnonneg).mp hmid),
      hXY.eventually (gt_mem_nhds hδ)] with i hi hdist k
    have hlow := (Real.lt_sqrt hnonneg).mpr (hi k)
    have hclose := (abs_le.mp (abs_sqrt_eigenvalues₀_sampleCovariance_sub_le (X i) (Y i) k)).1
    exact (Real.sqrt_lt_sqrt_iff hc₀).mp (by linarith)
  · exact .of_forall fun i k ↦ (lt_of_not_ge hc₀).trans_le
      ((posSemidef_sampleCovariance (X i)).eigenvalues₀_nonneg k)

end Matrix
