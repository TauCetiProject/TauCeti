/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.InnerProductSpace.CourantFischer

/-!
# Stability of Hermitian eigenvalue counts across a threshold

A perturbation smaller than the distance of an eigenvalue from a fixed real threshold
preserves the side of that threshold occupied by the corresponding sorted eigenvalue.
Consequently, if a Hermitian matrix has a spectral gap around the threshold, every
Hermitian perturbation smaller than the gap has the same number of eigenvalues in
`[c, ∞)`, counted with multiplicity. This is the rank stability used when selecting a
spectral subspace by a fixed threshold.

The norm in this file is the Euclidean operator norm, selected by
`Matrix.Norms.L2Operator`. The statements hold over any `RCLike` field and allow empty
matrix index types. They use Mathlib's decreasing enumeration `IsHermitian.eigenvalues₀`
and the operator Weyl inequality from
`TauCeti.Analysis.InnerProductSpace.CourantFischer`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press
  (2013), Theorem 4.3.1 (Weyl's perturbation inequality).
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {A B : Matrix ι ι 𝕜}

/-- A Hermitian perturbation smaller than the distance of a sorted eigenvalue from `c`
preserves whether that eigenvalue belongs to `[c, ∞)`. The norm is the Euclidean operator
norm. -/
theorem le_eigenvalues₀_iff_of_norm_sub_lt (hA : A.IsHermitian) (hB : B.IsHermitian)
    {c : ℝ} (i : Fin (Fintype.card ι))
    (hgap : ‖A - B‖ < |hA.eigenvalues₀ i - c|) :
    c ≤ hB.eigenvalues₀ i ↔ c ≤ hA.eigenvalues₀ i := by
  have hweyl : |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ := by
    -- The matrix enumeration is defined using the symmetric Euclidean operator.
    simp only [Matrix.IsHermitian.eigenvalues₀]
    apply LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le
      (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)
      finrank_euclideanSpace (fun x ↦ ?_) i
    rw [← map_sub, ← coe_toEuclideanCLM_eq_toEuclideanLin]
    simpa only [ContinuousLinearMap.coe_coe, l2_opNorm_toEuclideanCLM] using
      (toEuclideanCLM (𝕜 := 𝕜) (A - B)).le_opNorm x
  obtain ⟨hlower, hupper⟩ := abs_le.mp hweyl
  by_cases hside : c ≤ hA.eigenvalues₀ i
  · rw [abs_of_nonneg (sub_nonneg.mpr hside)] at hgap
    exact iff_of_true (by linarith) hside
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hside))] at hgap
    exact iff_of_false (by linarith) hside

/-- Hermitian perturbations of Euclidean operator norm less than a spectral gap around
`c` preserve the number of eigenvalues in `[c, ∞)`, with multiplicity. The gap bound may
be attained, and the matrix index type may be empty. -/
theorem card_eigenvalues₀_ge_eq_of_norm_sub_lt (hA : A.IsHermitian) (hB : B.IsHermitian)
    {c δ : ℝ} (hgap : ∀ i, δ ≤ |hA.eigenvalues₀ i - c|) (hpert : ‖A - B‖ < δ) :
    Nat.card {i : Fin (Fintype.card ι) // c ≤ hB.eigenvalues₀ i} =
      Nat.card {i : Fin (Fintype.card ι) // c ≤ hA.eigenvalues₀ i} := by
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i ↦
    hA.le_eigenvalues₀_iff_of_norm_sub_lt hB i (hpert.trans_le (hgap i)))

end Matrix.IsHermitian
