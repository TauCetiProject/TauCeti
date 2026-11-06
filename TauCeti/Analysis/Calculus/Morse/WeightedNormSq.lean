/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.Morse.Pi

/-!
# Morse data of weighted sums of squared norms

For a finite family of weights `c : ι → ℝ` and a finite-dimensional real inner product space `F`,
the quadratic function `z ↦ ∑ k, c k * ‖z k‖ ^ 2` on `ι → F` is the model of a critical point at
which the Hessian acts by the scalar `2 c k` on the `k`-th factor. Its Morse index is
`finrank ℝ F` times the number of negative weights, at every point
(`TauCeti.morseIndex_sum_mul_norm_sq`), and the origin is a nondegenerate critical point exactly
when no weight vanishes (`TauCeti.isNondegenerateCriticalPoint_sum_mul_norm_sq_zero_iff`).

Both statements are reduced to the separated sums of `TauCeti.Analysis.Calculus.Morse.Pi`: in the
coordinates of an orthonormal basis of each factor the function is `∑ ⟨k, m⟩, c k * y ⟨k, m⟩ ^ 2`.
For `F = ℂ` the weights appear twice each, which is why complex Morse indices of such functions
are even; this is the local form of the moment functions on complex projective space.

## Main results

* `TauCeti.contDiff_sum_mul_norm_sq` and `TauCeti.hasFDerivAt_sum_mul_norm_sq_zero`: the function
  is smooth and the origin is a critical point.
* `TauCeti.morseIndex_sum_mul_norm_sq`: the Morse index is `finrank ℝ F * #{k | c k < 0}`.
* `TauCeti.isNondegenerateCriticalPoint_sum_mul_norm_sq_zero_iff`: the origin is nondegenerate
  exactly when every weight is nonzero.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §4, the example of complex projective space.
-/

public section

open Function Module Set

namespace TauCeti

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A weighted sum of squared norms is smooth. -/
theorem contDiff_sum_mul_norm_sq (c : ι → ℝ) {m : WithTop ℕ∞} :
    ContDiff ℝ m fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2 :=
  ContDiff.sum fun k _ ↦
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ : ι ↦ F) k))

/-- A weighted sum of squared norms has zero derivative at the origin. -/
theorem hasFDerivAt_sum_mul_norm_sq_zero (c : ι → ℝ) :
    HasFDerivAt (fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) (0 : (ι → F) →L[ℝ] ℝ) 0 := by
  have hsq (k : ι) : HasFDerivAt (fun z : ι → F ↦ ‖z k‖ ^ 2) (0 : (ι → F) →L[ℝ] ℝ) 0 := by
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ F) k).hasFDerivAt
      (x := 0)).norm_sq
    simpa using h
  simpa using HasFDerivAt.fun_sum fun k _ ↦ (hsq k).const_mul (c k)

private theorem contDiffAt_mul_sq (a t : ℝ) : ContDiffAt ℝ 2 (fun t : ℝ ↦ a * t ^ 2) t := by
  fun_prop

variable [FiniteDimensional ℝ F]

/-- Coordinates of `ι → F` in an orthonormal basis of each factor. -/
private noncomputable def sigmaCoords :
    ((Σ _ : ι, Fin (finrank ℝ F)) → ℝ) ≃L[ℝ] (ι → F) :=
  ((LinearEquiv.piCurry ℝ fun (_ : ι) (_ : Fin (finrank ℝ F)) ↦ ℝ).trans
    (LinearEquiv.piCongrRight fun _ ↦
      (EuclideanSpace.equiv (Fin (finrank ℝ F)) ℝ).symm.toLinearEquiv.trans
        (stdOrthonormalBasis ℝ F).repr.symm.toLinearEquiv)).toContinuousLinearEquiv

/-- In these coordinates `z ↦ ∑ k, c k * ‖z k‖ ^ 2` is a separated sum of squares. -/
private theorem sum_mul_norm_sq_comp_sigmaCoords (c : ι → ℝ) :
    (fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) ∘ sigmaCoords =
      fun y ↦ ∑ p, (fun t : ℝ ↦ c p.1 * t ^ 2) (y p) := by
  funext y
  have hk (k : ι) : ‖sigmaCoords y k‖ ^ 2 = ∑ m, y ⟨k, m⟩ ^ 2 := by
    simp [sigmaCoords, EuclideanSpace.norm_sq_eq]
    rfl
  simp [hk, Finset.mul_sum, Fintype.sum_sigma]

/-- **The Morse index of a weighted sum of squared norms.** On `ι → F`, for a finite-dimensional
real inner product space `F`, the function `z ↦ ∑ k, c k * ‖z k‖ ^ 2` has Morse index
`finrank ℝ F` times the number of negative weights, at every point. -/
theorem morseIndex_sum_mul_norm_sq (c : ι → ℝ) (x : ι → F) :
    morseIndex (fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) x = finrank ℝ F * {k | c k < 0}.ncard := by
  set L : ((Σ _ : ι, Fin (finrank ℝ F)) → ℝ) ≃L[ℝ] (ι → F) := sigmaCoords
  have hcomp := (L : ((Σ _ : ι, Fin (finrank ℝ F)) → ℝ) →L[ℝ] (ι → F)).hessianQuadraticForm_comp
    (f := fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) (b := L.symm x)
    (contDiff_sum_mul_norm_sq c).contDiffAt
  rw [ContinuousLinearEquiv.coe_coe, sum_mul_norm_sq_comp_sigmaCoords,
    L.apply_symm_apply] at hcomp
  -- The Hessian in the new coordinates is equivalent to the original one.
  have h1 : sigNeg (hessianQuadraticForm (fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) x) =
      sigNeg (hessianQuadraticForm (fun y ↦ ∑ p, (fun t : ℝ ↦ c p.1 * t ^ 2) (y p))
        (L.symm x)) := by
    rw [hcomp]
    exact QuadraticMap.Equivalent.sigNeg_eq ⟨QuadraticMap.isometryEquivOfCompLinearEquiv _
      L.toLinearEquiv⟩
  rw [morseIndex_def, h1, ← morseIndex_def, morseIndex_sum_comp_eval fun p ↦ contDiffAt_mul_sq _ _]
  -- The pairs `⟨k, m⟩` with `c k < 0` are `finrank ℝ F` copies of the negative weights.
  classical
  have h : {p : Σ _ : ι, Fin (finrank ℝ F) |
      deriv (deriv fun t ↦ c p.1 * t ^ 2) ((L.symm x) p) < 0} =
      ↑((Finset.univ.filter fun k ↦ c k < 0).sigma
        fun _ ↦ (Finset.univ : Finset (Fin (finrank ℝ F)))) := by
    ext p
    simp [mul_neg_iff]
  rw [h, ncard_coe_finset, Finset.card_sigma, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fin, mul_comm, ← Finset.coe_filter_univ, ncard_coe_finset]

/-- **Nondegeneracy of a weighted sum of squared norms.** On `ι → F`, for a nonzero
finite-dimensional real inner product space `F`, the origin is a nondegenerate critical point of
`z ↦ ∑ k, c k * ‖z k‖ ^ 2` exactly when no weight vanishes. -/
theorem isNondegenerateCriticalPoint_sum_mul_norm_sq_zero_iff [Nontrivial F] (c : ι → ℝ) :
    IsNondegenerateCriticalPoint (fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2) 0 ↔ ∀ k, c k ≠ 0 := by
  set L : ((Σ _ : ι, Fin (finrank ℝ F)) → ℝ) ≃L[ℝ] (ι → F) := sigmaCoords
  have h := isNondegenerateCriticalPoint_comp_iff (f := fun z : ι → F ↦ ∑ k, c k * ‖z k‖ ^ 2)
    (φ := L) (b := 0) (contDiff_sum_mul_norm_sq c).contDiffAt L.contDiff.contDiffAt
    (by rw [L.fderiv]; exact ⟨L, rfl⟩)
  rw [sum_mul_norm_sq_comp_sigmaCoords, map_zero,
    isNondegenerateCriticalPoint_sum_comp_eval_iff fun p ↦ contDiffAt_mul_sq _ _] at h
  rw [← h]
  have hd : 0 < finrank ℝ F := finrank_pos
  simp only [Pi.zero_apply]
  refine ⟨fun hc k ↦ ?_, fun hc p ↦ ⟨by simp, by simpa using hc p.1⟩⟩
  simpa using (hc ⟨k, ⟨0, hd⟩⟩).2

end TauCeti

end
