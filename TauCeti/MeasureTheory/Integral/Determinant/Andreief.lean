/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Andréief's integration identity

The integral of a product of two evaluation determinants over a finite product measure is
the factorial of the number of variables times the determinant of the pairwise integrals.
Only integrability of the pairwise products is needed; the reference measure need not be
finite. In particular, the identity applies to square-integrable orthonormal functions and
normalizes their determinantal probability density.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), Lemma 3.2.3.
-/

public section

open MeasureTheory Matrix Equiv Finset

namespace MeasureTheory

variable {ι E 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] [RCLike 𝕜]
  {μ : Measure E} [SigmaFinite μ] {f g : ι → E → 𝕜}

/-- Pairwise integrability makes the product of two evaluation determinants integrable. -/
theorem integrable_det_mul_det
    (hfg : ∀ i j, Integrable (fun x ↦ f i x * g j x) μ) :
    Integrable (fun x : ι → E ↦ det (Matrix.of fun i j ↦ f i (x j)) *
      det (Matrix.of fun i j ↦ g i (x j))) (Measure.pi fun _ ↦ μ) := by
  simp only [det_apply', Matrix.of_apply, sum_mul, mul_sum]
  apply integrable_finsetSum
  intro σ _
  apply integrable_finsetSum
  intro τ _
  have h := Integrable.fintype_prod (fun i ↦ hfg (τ i) (σ i))
  simpa only [prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm] using
    h.const_mul ((Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜))

private theorem integral_prod_mul_det
    (hfg : ∀ i j, Integrable (fun x ↦ f i x * g j x) μ) (σ : Perm ι) :
    ∫ x : ι → E, (∏ j, f (σ j) (x j)) * det (Matrix.of fun i j ↦ g i (x j))
      ∂Measure.pi (fun _ ↦ μ) = det (Matrix.of fun i j ↦ ∫ x, f (σ j) x * g i x ∂μ) := by
  simp only [det_apply', Matrix.of_apply, mul_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro τ _
    simp only [mul_left_comm (∏ _ : ι, _), ← prod_mul_distrib, integral_const_mul]
    exact congrArg ((Perm.sign τ : 𝕜) * ·)
      (integral_fintype_prod_eq_prod (fun j x ↦ f (σ j) x * g (τ j) x))
  · intro τ _
    simpa only [prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm] using
      (Integrable.fintype_prod (fun j ↦ hfg (σ j) (τ j))).const_mul (Perm.sign τ : 𝕜)

/-- **Andréief's identity**, for an arbitrary finite index type and a sigma-finite reference
measure. The integrability hypotheses concern the pairwise products, not the factors. -/
theorem integral_det_mul_det
    (hfg : ∀ i j, Integrable (fun x ↦ f i x * g j x) μ) :
    ∫ x : ι → E, det (Matrix.of fun i j ↦ f i (x j)) * det (Matrix.of fun i j ↦ g i (x j))
      ∂Measure.pi (fun _ ↦ μ) =
      (Fintype.card ι).factorial * det (Matrix.of fun i j ↦ ∫ x, f i x * g j x ∂μ) := by
  conv_lhs =>
    enter [2, x]
    rw [det_apply']
    simp only [Matrix.of_apply, sum_mul]
  rw [integral_finsetSum]
  · have hσ (σ : Perm ι) :
        (Perm.sign σ : 𝕜) * (∫ x : ι → E, (∏ j, f (σ j) (x j)) *
          det (Matrix.of fun i j ↦ g i (x j)) ∂Measure.pi (fun _ ↦ μ)) =
          det (Matrix.of fun i j ↦ ∫ x, f i x * g j x ∂μ) := by
      rw [integral_prod_mul_det hfg σ]
      have hp := det_permute' σ (Matrix.of fun i j ↦ ∫ x, f j x * g i x ∂μ)
      simp only [Matrix.submatrix, Matrix.of_apply, id_eq] at hp
      rw [hp, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
        Units.val_one, Int.cast_one, one_mul]
      exact det_transpose (Matrix.of fun i j ↦ ∫ x, f i x * g j x ∂μ)
    simp only [mul_assoc, integral_const_mul, hσ, sum_const, card_univ,
      Fintype.card_perm, nsmul_eq_mul]
  · intro σ _
    have hsum := integrable_finsetSum (s := univ) (fun τ _ ↦
      (Integrable.fintype_prod (fun j ↦ hfg (σ j) (τ j))).const_mul
        ((Perm.sign σ : 𝕜) * (Perm.sign τ : 𝕜)))
    simpa only [det_apply', Matrix.of_apply, mul_sum, prod_mul_distrib, mul_assoc,
      mul_left_comm, mul_comm]
      using hsum

section Hermitian

variable {φ : ι → E → 𝕜}

omit [MeasurableSpace E] in
private theorem weighted_det_identity (φ : ι → E → 𝕜) (u : E → 𝕜) (x : ι → E) :
    det (Matrix.of fun i j ↦ φ i (x j)) *
        det (Matrix.of fun i j ↦ u (x j) * star (φ i (x j))) =
      (∏ j, u (x j)) * (‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2 : ℝ) := by
  have hs : det (Matrix.of fun i j ↦ star (φ i (x j))) =
      star (det (Matrix.of fun i j ↦ φ i (x j))) := by
    simpa only [RingHom.mapMatrix_apply, Matrix.map, Matrix.of_apply, starRingEnd_apply] using
      ((starRingEnd 𝕜).map_det (Matrix.of fun i j ↦ φ i (x j))).symm
  have hd := Matrix.det_mul_row (fun j ↦ u (x j))
    (Matrix.of fun i j ↦ star (φ i (x j)))
  simp only [Matrix.of_apply] at hd
  rw [hd, hs, mul_left_comm]
  exact congrArg ((∏ j, u (x j)) * ·) (by
    simpa only [starRingEnd_apply, RCLike.ofReal_pow] using
      RCLike.mul_conj (det (Matrix.of fun i j ↦ φ i (x j))))

/-- A weighted squared evaluation determinant is integrable whenever the corresponding
weighted pairwise products are integrable. -/
theorem integrable_prod_mul_norm_det_sq {u : E → 𝕜}
    (hu : ∀ i j, Integrable (fun x ↦ φ i x * (u x * star (φ j x))) μ) :
    Integrable (fun x : ι → E ↦ (∏ j, u (x j)) *
      (‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2 : ℝ)) (Measure.pi fun _ ↦ μ) := by
  exact (integrable_det_mul_det hu).congr (.of_forall (weighted_det_identity φ u))

/-- **Weighted Hermitian Andréief identity.** Multiplying the squared evaluation determinant
by one weight per particle inserts that weight into every pairwise integral. -/
theorem integral_prod_mul_norm_det_sq {u : E → 𝕜}
    (hu : ∀ i j, Integrable (fun x ↦ φ i x * (u x * star (φ j x))) μ) :
    ∫ x : ι → E, (∏ j, u (x j)) * (‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2 : ℝ)
      ∂Measure.pi (fun _ ↦ μ) =
      (Fintype.card ι).factorial *
        det (Matrix.of fun i j ↦ ∫ x, φ i x * (u x * star (φ j x)) ∂μ) := by
  rw [← integral_det_mul_det hu]
  exact integral_congr_ae (.of_forall fun x ↦ (weighted_det_identity φ u x).symm)

/-- The squared evaluation determinant is integrable for square-integrable generators. -/
theorem integrable_norm_det_sq (hφ : ∀ i, MemLp (φ i) 2 μ) :
    Integrable (fun x : ι → E ↦ ‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2)
      (Measure.pi fun _ ↦ μ) := by
  have hi := integrable_prod_mul_norm_det_sq (φ := φ) (u := fun _ ↦ 1)
    (fun i j ↦ by
      have hi : Integrable (fun x ↦ φ i x * star (φ j x)) μ :=
        (hφ i).integrable_mul (hφ j).star
      simpa only [one_mul] using hi)
  simpa using hi.norm

/-- **The partition function** of an orthonormal evaluation determinant is `n!`. -/
theorem integral_norm_det_sq (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0) :
    ∫ x : ι → E, ‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2
      ∂Measure.pi (fun _ ↦ μ) = (Fintype.card ι).factorial := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [← integral_ofReal]
  have hi := integral_prod_mul_norm_det_sq (φ := φ) (u := fun _ ↦ 1)
    (fun i j ↦ by
      have hi : Integrable (fun x ↦ φ i x * star (φ j x)) μ :=
        (hφ i).integrable_mul (hφ j).star
      simpa only [one_mul] using hi)
  simp_rw [prod_const_one, one_mul, horth] at hi
  have hm : (Matrix.of fun i j : ι ↦ if i = j then (1 : 𝕜) else 0) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  simpa only [hm, det_one, mul_one, RCLike.ofReal_natCast] using hi

end Hermitian

end MeasureTheory
