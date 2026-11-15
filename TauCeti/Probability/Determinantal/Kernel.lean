/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite rank projection kernels

A finite family of real or complex functions defines its Gram kernel by summing their
outer products. For an orthonormal family, integration against this kernel is a projection:
it fixes the generating functions and reproduces the kernel itself. Its integrated diagonal
is the size of the family. Every finite evaluation matrix is positive semidefinite.

These identities apply in particular to orthogonal polynomial ensembles, where the
functions are orthonormal polynomials multiplied by the square root of the weight.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §3.2.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset

namespace TauCeti

variable {ι E 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- The Gram kernel of a finite family of functions. It is a projection kernel when the
family is orthonormal for the reference measure. -/
def finiteRankKernel (φ : ι → E → 𝕜) (x y : E) : 𝕜 :=
  ∑ i, φ i x * star (φ i y)

/-- The Gram kernel is Hermitian. -/
@[simp]
theorem star_finiteRankKernel (φ : ι → E → 𝕜) (x y : E) :
    star (finiteRankKernel φ x y) = finiteRankKernel φ y x := by
  simp [finiteRankKernel, mul_comm]

/-- The real diagonal of a Gram kernel is the sum of squared norms of the functions. -/
theorem re_finiteRankKernel_self (φ : ι → E → 𝕜) (x : E) :
    RCLike.re (finiteRankKernel φ x x) = ∑ i, ‖φ i x‖ ^ 2 := by
  simp [finiteRankKernel, RCLike.mul_conj]

/-- The diagonal of a Gram kernel is real. -/
@[simp]
theorem im_finiteRankKernel_self (φ : ι → E → 𝕜) (x : E) :
    RCLike.im (finiteRankKernel φ x x) = 0 := by
  simp [finiteRankKernel, RCLike.mul_conj]

/-- Every finite evaluation matrix of a Gram kernel is positive semidefinite. -/
theorem posSemidef_finiteRankKernel [PartialOrder 𝕜] [StarOrderedRing 𝕜]
    {κ : Type*} (φ : ι → E → 𝕜) (x : κ → E) :
    (Matrix.of fun i j ↦ finiteRankKernel φ (x i) (x j)).PosSemidef := by
  convert Matrix.posSemidef_self_mul_conjTranspose (Matrix.of fun j i ↦ φ i (x j)) using 1
  ext i j
  simp [finiteRankKernel, Matrix.mul_apply]

/-- A full-size kernel determinant is the squared norm of the evaluation determinant.
This identifies the joint density expressed using the functions with the density expressed
using their kernel. -/
theorem det_finiteRankKernel [DecidableEq ι] (φ : ι → E → 𝕜) (x : ι → E) :
    det (Matrix.of fun i j ↦ finiteRankKernel φ (x i) (x j)) =
      (‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2 : ℝ) := by
  have hm : (Matrix.of fun i j ↦ finiteRankKernel φ (x i) (x j)) =
      (Matrix.of fun i j ↦ φ j (x i)) * (Matrix.of fun i j ↦ φ j (x i))ᴴ := by
    ext i j
    simp [finiteRankKernel, Matrix.mul_apply]
  have ht : det (Matrix.of fun i j ↦ φ j (x i)) =
      det (Matrix.of fun i j ↦ φ i (x j)) :=
    Matrix.det_transpose (Matrix.of fun i j ↦ φ i (x j))
  rw [hm, Matrix.det_mul, Matrix.det_conjTranspose, ht]
  simpa only [starRingEnd_apply, RCLike.ofReal_pow] using
    RCLike.mul_conj (det (Matrix.of fun i j ↦ φ i (x j)))

section Measure

variable [MeasurableSpace E] {μ : Measure E} {φ : ι → E → 𝕜}

/-- Measurable functions give a jointly measurable finite rank kernel. -/
theorem measurable_finiteRankKernel (hφ : ∀ i, Measurable (φ i)) :
    Measurable (fun p : E × E ↦ finiteRankKernel φ p.1 p.2) := by
  unfold finiteRankKernel
  fun_prop

omit [MeasurableSpace E] in
/-- Continuity of the functions implies continuity of their Gram kernel. -/
theorem continuous_finiteRankKernel [TopologicalSpace E] (hφ : ∀ i, Continuous (φ i)) :
    Continuous (fun p : E × E ↦ finiteRankKernel φ p.1 p.2) := by
  unfold finiteRankKernel
  fun_prop

/-- Square-integrable generating functions give an integrable kernel diagonal. -/
theorem integrable_finiteRankKernel_self (hφ : ∀ i, MemLp (φ i) 2 μ) :
    Integrable (fun x ↦ finiteRankKernel φ x x) μ := by
  exact integrable_finsetSum _ fun i _ ↦ (hφ i).integrable_mul (hφ i).star

/-- The integrated diagonal of an orthonormal kernel is the rank, including rank zero. -/
theorem integral_finiteRankKernel_self [DecidableEq ι] (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0) :
    ∫ x, finiteRankKernel φ x x ∂μ = Fintype.card ι := by
  simp only [finiteRankKernel]
  have hi (i : ι) : Integrable (fun x ↦ φ i x * star (φ i x)) μ :=
    (hφ i).integrable_mul (hφ i).star
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  simp_rw [horth]
  simp

/-- Every section of a finite rank kernel is square-integrable when its generators are. -/
theorem memLp_finiteRankKernel (hφ : ∀ i, MemLp (φ i) 2 μ) (x : E) :
    MemLp (finiteRankKernel φ x) 2 μ := by
  exact memLp_finsetSum _ fun i _ ↦ (hφ i).star.const_mul (φ i x)

/-- The integral projection fixes each member of the orthonormal family. -/
theorem integral_finiteRankKernel_mul_generator [DecidableEq ι]
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    (x : E) (j : ι) :
    ∫ y, finiteRankKernel φ x y * φ j y ∂μ = φ j x := by
  have hi (i : ι) : Integrable (fun y ↦ φ i x * (φ j y * star (φ i y))) μ :=
    ((hφ j).integrable_mul (hφ i).star).const_mul _
  have heq (y : E) : finiteRankKernel φ x y * φ j y =
      ∑ i, φ i x * (φ j y * star (φ i y)) := by
    simp only [finiteRankKernel, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [heq]
  rw [integral_finsetSum _ fun i _ ↦ hi i]
  simp_rw [integral_const_mul, horth]
  simp

/-- Products of two kernel sections are integrable for square-integrable generators. -/
theorem integrable_finiteRankKernel_mul (hφ : ∀ i, MemLp (φ i) 2 μ) (x y : E) :
    Integrable (fun z ↦ finiteRankKernel φ x z * finiteRankKernel φ z y) μ := by
  have hi : Integrable (fun z ↦ finiteRankKernel φ x z * star (finiteRankKernel φ y z)) μ :=
    (memLp_finiteRankKernel hφ x).integrable_mul (memLp_finiteRankKernel hφ y).star
  simpa only [star_finiteRankKernel] using hi

/-- **The reproducing identity** for a finite orthonormal kernel. -/
theorem integral_finiteRankKernel_mul [DecidableEq ι] (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    (x y : E) :
    ∫ z, finiteRankKernel φ x z * finiteRankKernel φ z y ∂μ = finiteRankKernel φ x y := by
  have hint (i : ι) : Integrable (fun z ↦
      (finiteRankKernel φ x z * φ i z) * star (φ i y)) μ :=
    ((memLp_finiteRankKernel hφ x).integrable_mul (hφ i)).mul_const _
  have heq (z : E) : finiteRankKernel φ x z * finiteRankKernel φ z y =
      ∑ i, (finiteRankKernel φ x z * φ i z) * star (φ i y) := by
    simp [finiteRankKernel, Finset.mul_sum, mul_assoc]
  simp_rw [heq]
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [integral_mul_const, integral_finiteRankKernel_mul_generator hφ horth]
  rfl

end Measure

end TauCeti
