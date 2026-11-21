/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.InnerProductSpace.Positive.Superadditive
public import TauCeti.Analysis.Matrix.FunctionalCalculus
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# McCarthy's trace inequalities for positive semidefinite matrices

For positive semidefinite matrices `a₁, …, aₘ` over `ℝ` or `ℂ` and a function `φ` convex on
`[0, ∞)` with `φ 0 = 0`, the trace of the functional calculus is superadditive,

`∑ₖ Re tr φ(aₖ) ≤ Re tr φ(∑ₖ aₖ)`,

and it is subadditive when `φ` is concave on `[0, ∞)`. For the real powers `φ(t) = tʳ` these are
McCarthy's trace-power inequalities

`∑ₖ tr aₖʳ ≤ tr (∑ₖ aₖ)ʳ` for `1 ≤ r`,   `tr (∑ₖ aₖ)ʳ ≤ ∑ₖ tr aₖʳ` for `0 < r ≤ 1`,

with the unnormalized trace. They compare the Schatten `r`-th powers `‖·‖ᵣʳ = tr |·|ʳ` of a sum
of positive matrices with those of its terms; for `r ≤ 1` the second is the `r`-triangle
inequality of the Schatten quasi-norms on positive matrices.

The convex two-matrix inequality transfers
`LinearMap.IsPositive.sum_map_eigenvalues_add_sum_map_eigenvalues_le_sum_map_eigenvalues_add`
from the Euclidean operators of the matrices, using
`Matrix.IsHermitian.trace_cfc_eq_sum_eigenvalues₀`, and the convex finite-family inequality
follows by induction. The concave inequalities are the convex ones applied to `-φ`.

## Main results

* `Matrix.PosSemidef.re_trace_cfc_add_re_trace_cfc_le_re_trace_cfc_add`,
  `Matrix.PosSemidef.re_trace_cfc_add_le_re_trace_cfc_add_re_trace_cfc`: the convex and concave
  inequalities for two matrices.
* `Matrix.sum_re_trace_cfc_le_re_trace_cfc_sum`, `Matrix.re_trace_cfc_sum_le_sum_re_trace_cfc`:
  the same for finite families.
* `Matrix.sum_re_trace_rpow_le_re_trace_rpow_sum`,
  `Matrix.re_trace_rpow_sum_le_sum_re_trace_rpow`: McCarthy's trace-power inequalities.

## References

* C. A. McCarthy, *cₚ*, Israel J. Math. **5** (1967), 249–271.
* F. Hiai, *Lectures on selected topics in von Neumann algebras*, EMS Series of Lectures in
  Mathematics, EMS Press (2021), Lemma 11.27.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A B : Matrix n n 𝕜}
  {φ : ℝ → ℝ}

/-- **Superadditivity of convex trace functions** (McCarthy). For positive semidefinite `A` and
`B` and a function `φ` convex on `[0, ∞)` with `φ 0 ≤ 0`,
`Re tr φ(A) + Re tr φ(B) ≤ Re tr φ(A + B)`. -/
theorem PosSemidef.re_trace_cfc_add_re_trace_cfc_le_re_trace_cfc_add (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hφ : ConvexOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 ≤ 0) :
    RCLike.re (cfc φ A).trace + RCLike.re (cfc φ B).trace ≤ RCLike.re (cfc φ (A + B)).trace := by
  have h :=
    LinearMap.IsPositive.sum_map_eigenvalues_add_sum_map_eigenvalues_le_sum_map_eigenvalues_add
      (isPositive_toEuclideanLin_iff.mpr hA) (isPositive_toEuclideanLin_iff.mpr hB)
      finrank_euclideanSpace hφ hφ0
  rw [LinearMap.IsSymmetric.eigenvalues_congr (map_add toEuclideanLin A B).symm _
    (isSymmetric_toEuclideanLin_iff.mpr (hA.add hB).isHermitian)] at h
  rw [hA.isHermitian.trace_cfc_eq_sum_eigenvalues₀, hB.isHermitian.trace_cfc_eq_sum_eigenvalues₀,
    (hA.add hB).isHermitian.trace_cfc_eq_sum_eigenvalues₀]
  simpa only [map_sum, RCLike.ofReal_re, IsHermitian.eigenvalues₀] using h

/-- **Subadditivity of concave trace functions** (Rotfel'd). For positive semidefinite `A` and
`B` and a function `φ` concave on `[0, ∞)` with `0 ≤ φ 0`,
`Re tr φ(A + B) ≤ Re tr φ(A) + Re tr φ(B)`. -/
theorem PosSemidef.re_trace_cfc_add_le_re_trace_cfc_add_re_trace_cfc (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (hφ0 : 0 ≤ φ 0) :
    RCLike.re (cfc φ (A + B)).trace ≤ RCLike.re (cfc φ A).trace + RCLike.re (cfc φ B).trace := by
  have h := hA.re_trace_cfc_add_re_trace_cfc_le_re_trace_cfc_add hB hφ.neg (by simpa using hφ0)
  rw [cfc_neg'] at h
  simp only [Pi.neg_apply, trace_neg, map_neg] at h
  linarith

/-- **Superadditivity of convex trace functions for finite families.** For positive
semidefinite `a k`, `k ∈ s`, and a function `φ` convex on `[0, ∞)` with `φ 0 = 0`,
`∑ₖ Re tr φ(aₖ) ≤ Re tr φ(∑ₖ aₖ)`. -/
theorem sum_re_trace_cfc_le_re_trace_cfc_sum {ι : Type*} (s : Finset ι) {a : ι → Matrix n n 𝕜}
    (ha : ∀ k ∈ s, (a k).PosSemidef) (hφ : ConvexOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 = 0) :
    ∑ k ∈ s, RCLike.re (cfc φ (a k)).trace ≤ RCLike.re (cfc φ (∑ k ∈ s, a k)).trace := by
  induction s using Finset.cons_induction with
  | empty => simp [hφ0]
  | cons k s hk ih =>
    have ha' : ∀ j ∈ s, (a j).PosSemidef := fun j hj ↦ ha j (Finset.mem_cons_of_mem hj)
    have h := (ha k (Finset.mem_cons_self k s)).re_trace_cfc_add_re_trace_cfc_le_re_trace_cfc_add
      (posSemidef_sum s ha') hφ hφ0.le
    rw [Finset.sum_cons, Finset.sum_cons]
    linarith [ih ha']

/-- **Subadditivity of concave trace functions for finite families.** For positive semidefinite
`a k`, `k ∈ s`, and a function `φ` concave on `[0, ∞)` with `φ 0 = 0`,
`Re tr φ(∑ₖ aₖ) ≤ ∑ₖ Re tr φ(aₖ)`. -/
theorem re_trace_cfc_sum_le_sum_re_trace_cfc {ι : Type*} (s : Finset ι) {a : ι → Matrix n n 𝕜}
    (ha : ∀ k ∈ s, (a k).PosSemidef) (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (hφ0 : φ 0 = 0) :
    RCLike.re (cfc φ (∑ k ∈ s, a k)).trace ≤ ∑ k ∈ s, RCLike.re (cfc φ (a k)).trace := by
  have h := sum_re_trace_cfc_le_re_trace_cfc_sum s ha hφ.neg (by simp [hφ0])
  rw [cfc_neg'] at h
  simp only [Pi.neg_apply, trace_neg, map_neg, Finset.sum_neg_distrib] at h
  linarith

/-- **McCarthy's trace-power inequality for `1 ≤ r`.** For positive semidefinite `a k`, `k ∈ s`,
`∑ₖ tr aₖʳ ≤ tr (∑ₖ aₖ)ʳ`, stated for the real parts of the traces. -/
theorem sum_re_trace_rpow_le_re_trace_rpow_sum {ι : Type*} (s : Finset ι)
    {a : ι → Matrix n n 𝕜} (ha : ∀ k ∈ s, (a k).PosSemidef) {r : ℝ} (hr : 1 ≤ r) :
    ∑ k ∈ s, RCLike.re ((a k) ^ r).trace ≤ RCLike.re ((∑ k ∈ s, a k) ^ r).trace := by
  calc ∑ k ∈ s, RCLike.re ((a k) ^ r).trace
      = ∑ k ∈ s, RCLike.re (cfc (· ^ r) (a k)).trace :=
        Finset.sum_congr rfl fun k hk ↦ by rw [CFC.rpow_eq_cfc_real (ha k hk).nonneg]
    _ ≤ RCLike.re (cfc (· ^ r) (∑ k ∈ s, a k)).trace :=
        sum_re_trace_cfc_le_re_trace_cfc_sum s ha (convexOn_rpow hr)
          (Real.zero_rpow (by positivity))
    _ = RCLike.re ((∑ k ∈ s, a k) ^ r).trace := by
        rw [CFC.rpow_eq_cfc_real (posSemidef_sum s ha).nonneg]

/-- **McCarthy's trace-power inequality for `0 < r ≤ 1`.** For positive semidefinite `a k`,
`k ∈ s`, `tr (∑ₖ aₖ)ʳ ≤ ∑ₖ tr aₖʳ`, stated for the real parts of the traces. -/
theorem re_trace_rpow_sum_le_sum_re_trace_rpow {ι : Type*} (s : Finset ι)
    {a : ι → Matrix n n 𝕜} (ha : ∀ k ∈ s, (a k).PosSemidef) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    RCLike.re ((∑ k ∈ s, a k) ^ r).trace ≤ ∑ k ∈ s, RCLike.re ((a k) ^ r).trace := by
  calc RCLike.re ((∑ k ∈ s, a k) ^ r).trace
      = RCLike.re (cfc (· ^ r) (∑ k ∈ s, a k)).trace := by
        rw [CFC.rpow_eq_cfc_real (posSemidef_sum s ha).nonneg]
    _ ≤ ∑ k ∈ s, RCLike.re (cfc (· ^ r) (a k)).trace :=
        re_trace_cfc_sum_le_sum_re_trace_cfc s ha (Real.concaveOn_rpow hr₀.le hr₁)
          (Real.zero_rpow hr₀.ne')
    _ = ∑ k ∈ s, RCLike.re ((a k) ^ r).trace :=
        Finset.sum_congr rfl fun k hk ↦ by rw [CFC.rpow_eq_cfc_real (ha k hk).nonneg]

end Matrix
