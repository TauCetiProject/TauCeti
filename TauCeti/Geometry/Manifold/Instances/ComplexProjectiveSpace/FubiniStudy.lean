/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import TauCeti.Analysis.InnerProductSpace.FubiniStudy
public import TauCeti.Topology.ComplexProjectiveSpace.Charts

/-!
# The Fubini–Study Hermitian matrix in an affine chart of `CPⁿ`

In the chart `X_k ≠ 0` of complex projective space, the point with affine coordinates
`w : Fin n → ℂ` has the homogeneous coordinate vector `affineVector k w`, whose entry `k` is `1`
and whose other entries are those of `w`. The derivative of `affineVector k` is the map
`TauCeti.ComplexProjectiveSpace.insertZeroL k` inserting a zero in position `k`
(`TauCeti.ComplexProjectiveSpace.fderiv_affineVector`). It lifts the coordinate tangent vectors of
the chart to homogeneous representatives.

Evaluating the homogeneous Fubini–Study form `TauCeti.fubiniStudyHermitian` on these lifts gives
the Hermitian matrix of the Fubini–Study metric in the chart. With `r = 1 + ∑ |w_l|²`,

`h(e_i, e_j) = (δ_ij / r - w_i conj (w_j) / r²) / π`

(`TauCeti.ComplexProjectiveSpace.fubiniStudyHermitian_affineVector_insertZeroL_single`), the
coefficient order being the one fixed by Mathlib's inner product, conjugate-linear in its first
argument. The general formula for arbitrary tangent vectors is
`TauCeti.ComplexProjectiveSpace.fubiniStudyHermitian_affineVector_insertZeroL`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter V, §15, and Chapter VI,
  (4.4).
-/

public section

open RCLike Real
open scoped InnerProductSpace ComplexConjugate

namespace TauCeti.ComplexProjectiveSpace

noncomputable section

variable {n : ℕ}

/-- The derivative of the homogeneous coordinate vector of the chart `X_k ≠ 0` inserts a zero in
position `k`. -/
theorem hasFDerivAt_affineVector (k : Fin (n + 1)) (w : Fin n → ℂ) :
    HasFDerivAt (affineVector k) (insertZeroL k) w := by
  have h : affineVector k = fun v ↦ affineVector k 0 + insertZeroL k v := by
    ext v i
    induction i using Fin.succAboveCases k <;> simp [insertZeroL_apply]
  rw [h]
  exact (insertZeroL k).hasFDerivAt.const_add _

/-- The homogeneous coordinate vector of the chart `X_k ≠ 0` is differentiable. -/
@[fun_prop]
theorem differentiable_affineVector (k : Fin (n + 1)) :
    Differentiable ℂ (affineVector (n := n) k) :=
  fun w ↦ (hasFDerivAt_affineVector k w).differentiableAt

/-- The derivative of the homogeneous coordinate vector of the chart `X_k ≠ 0` is
`insertZeroL k`. -/
@[simp]
theorem fderiv_affineVector (k : Fin (n + 1)) (w : Fin n → ℂ) :
    fderiv ℂ (affineVector k) w = insertZeroL k :=
  (hasFDerivAt_affineVector k w).fderiv

/-- **The Fubini–Study form in an affine chart.** For the point with affine coordinates `w` in the
chart `X_k ≠ 0`, with `r = 1 + ∑ |w_l|²`, the homogeneous Fubini–Study form evaluated on the lifts
`insertZeroL k a`, `insertZeroL k b` of tangent vectors `a`, `b` (see `fderiv_affineVector`) is
`(r ⟪a, b⟫ - ⟪a, w⟫ ⟪w, b⟫) / (π r²)`, the inner products being the standard Hermitian ones of
`ℂⁿ`. -/
theorem fubiniStudyHermitian_affineVector_insertZeroL (k : Fin (n + 1)) (w a b : Fin n → ℂ) :
    fubiniStudyHermitian ℂ (affineVector k w) (insertZeroL k a) (insertZeroL k b) =
      (((1 + ∑ l, ‖w l‖ ^ 2 : ℝ) : ℂ) * ∑ l, conj (a l) * b l -
          (∑ l, conj (a l) * w l) * ∑ l, conj (w l) * b l) /
        ((π * (1 + ∑ l, ‖w l‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  have hinner : ∀ x y : EuclideanSpace ℂ (Fin (n + 1)), ⟪x, y⟫_ℂ = ∑ i, conj (x i) * y i :=
    fun x y ↦ by simp [PiLp.inner_apply, mul_comm]
  have h4 : ‖affineVector k w‖ ^ 4 = (‖affineVector k w‖ ^ 2) ^ 2 := by ring
  rw [fubiniStudyHermitian_apply, h4, norm_affineVector_sq]
  simp [hinner, Fin.sum_univ_succAbove _ k]

/-- **The Fubini–Study Hermitian matrix in an affine chart.** For the point with affine coordinates
`w` in the chart `X_k ≠ 0`, with `r = 1 + ∑ |w_l|²`, the homogeneous Fubini–Study form evaluated
on the lifts `insertZeroL k e_i`, `insertZeroL k e_j` of the coordinate vectors is
`(δ_ij / r - w_i conj (w_j) / r²) / π`. -/
theorem fubiniStudyHermitian_affineVector_insertZeroL_single (k : Fin (n + 1)) (w : Fin n → ℂ)
    (i j : Fin n) :
    fubiniStudyHermitian ℂ (affineVector k w) (insertZeroL k (Pi.single i 1))
        (insertZeroL k (Pi.single j 1)) =
      ((if i = j then 1 else 0) / ((1 + ∑ l, ‖w l‖ ^ 2 : ℝ) : ℂ) -
          w i * conj (w j) / ((1 + ∑ l, ‖w l‖ ^ 2 : ℝ) : ℂ) ^ 2) / π := by
  have hr : ((1 + ∑ l, ‖w l‖ ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2
    (add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun l _ ↦ by positivity)).ne'
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  have hden : ((π * (1 + ∑ l, ‖w l‖ ^ 2) ^ 2 : ℝ) : ℂ) =
      (π : ℂ) * ((1 + ∑ l, ‖w l‖ ^ 2 : ℝ) : ℂ) ^ 2 := by push_cast; ring
  rw [fubiniStudyHermitian_affineVector_insertZeroL, hden]
  simp only [Pi.single_apply, apply_ite, map_one, map_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one, mul_zero]
  generalize ((1 + ∑ l, ‖w l‖ ^ 2 : ℝ) : ℂ) = r at hr ⊢
  rcases eq_or_ne i j with rfl | hij
  · simp only [ite_true]
    field_simp
  · simp only [hij, hij.symm, ite_false]
    field_simp
    ring

/-- **The Fubini–Study metric is positive definite in an affine chart.** The lift
`insertZeroL k a` of a nonzero tangent vector `a` of the chart `X_k ≠ 0` has entry `0` in
position `k`, so it is not a multiple of the homogeneous coordinate vector `affineVector k w`,
whose entry there is `1`; hence the homogeneous Fubini–Study form is positive on it. -/
theorem re_fubiniStudyHermitian_affineVector_insertZeroL_self_pos (k : Fin (n + 1))
    (w : Fin n → ℂ) {a : Fin n → ℂ} (ha : a ≠ 0) :
    0 < re (fubiniStudyHermitian ℂ (affineVector k w) (insertZeroL k a) (insertZeroL k a)) := by
  refine (re_fubiniStudyHermitian_apply_self_pos_iff (affineVector_ne_zero k w)).2 fun hmem ↦ ha ?_
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hc0 : c = 0 := by simpa using congrArg (· k) hc
  funext j
  simpa [hc0] using (congrArg (· (k.succAbove j)) hc).symm

end

end TauCeti.ComplexProjectiveSpace
