/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# Covariances and covariance matrices

Covariance is unchanged by almost-everywhere changes to either observable. This file also
packages the coordinate covariances of a measure on a finite-dimensional Euclidean space as a
matrix and connects that matrix to Mathlib's basis-free `covarianceBilin`.

The `MemLp id 2 μ` hypothesis in the comparison theorem is essential. Mathlib deliberately sets
`covarianceBilin μ` to zero when this hypothesis fails, whereas its scalar `covariance` is
totalized coordinate by coordinate.

## Main results

* `TauCeti.covMatrix` is the matrix of coordinate covariances of a measure.
* `TauCeti.covarianceBilin_eq_covMatrix` identifies the matrix and bilinear-form views of
  covariance when the measure has a finite second moment.
* `TauCeti.posSemidef_covMatrix` proves that covariance matrices are positive semidefinite under
  the same moment hypotheses.
* `TauCeti.integral_norm_sq_eq_norm_integral_sq_add_trace_covMatrix` decomposes the second
  moment into the squared norm of the mean and the trace of the covariance matrix.
* `TauCeti.covarianceBilin_eq_smul_innerSL` shows that a law invariant under every linear
  isometry has covariance equal to its second moment divided by the dimension, times the inner
  product.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 1,
  **Covariance matrices**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

namespace TauCeti

/-- Covariance is unchanged by almost-everywhere changes to either observable. -/
theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  simp only [covariance, integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with x hx hy
  rw [hx, hy]

variable {ι : Type*}


/-- The covariance matrix of a measure on a finite-dimensional Euclidean space. Its `(i, j)`
entry is the scalar covariance of the `i`th and `j`th coordinate projections. -/
def covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  fun i j => cov[fun z => z i, fun z => z j; μ]

/-- An entry of `covMatrix` is the covariance of the corresponding coordinate projections. -/
@[simp]
theorem covMatrix_apply (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j = cov[fun z => z i, fun z => z j; μ] := (rfl)

/-- Covariance matrices are symmetric. -/
theorem covMatrix_apply_comm (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j = covMatrix μ j i := by
  rw [covMatrix_apply, covMatrix_apply, covariance_comm]

/-- A covariance matrix is Hermitian (equivalently, symmetric over `ℝ`). -/
theorem isHermitian_covMatrix (μ : Measure (EuclideanSpace ℝ ι)) :
    (covMatrix μ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  exact fun i j => covMatrix_apply_comm μ j i

/-- For a finite measure with finite second moment, the entrywise covariance matrix represents
Mathlib's basis-free covariance bilinear form. -/
theorem covarianceBilin_eq_covMatrix [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ)
    (x y : EuclideanSpace ℝ ι) :
    covarianceBilin μ x y = ⟪x, (covMatrix μ).toEuclideanLin y⟫ := by
  classical
  have hcoord : ∀ i, MemLp (fun z : EuclideanSpace ℝ ι => z i) 2 μ := by
    intro i
    simpa only [id_eq, EuclideanSpace.coe_proj] using
      hμ.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj i)
  have hpi := covarianceBilin_apply_pi (μ := μ) (X := fun i z => z i) hcoord x y
  have hfun : (fun z : EuclideanSpace ℝ ι => WithLp.toLp 2 (fun i => z i)) = id := by
    funext z
    exact WithLp.toLp_ofLp 2 z
  rw [hfun, Measure.map_id] at hpi
  rw [hpi]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [covMatrix_apply]
  ring

/-- The covariance matrix of a finite measure with finite second moment is positive semidefinite. -/
theorem posSemidef_covMatrix [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) :
    (covMatrix μ).PosSemidef := by
  classical
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr (isHermitian_covMatrix μ), fun x => ?_⟩
  have hnonneg := covarianceBilin_self_nonneg (μ := μ) x
  rw [covarianceBilin_eq_covMatrix μ hμ x x] at hnonneg
  simpa only [RCLike.re_to_real, real_inner_comm] using hnonneg

/-- The second moment of a Euclidean-valued probability measure is the squared norm of its mean
plus the trace of its covariance matrix. -/
theorem integral_norm_sq_eq_norm_integral_sq_add_trace_covMatrix [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    ∫ x, ‖x‖ ^ 2 ∂μ = ‖∫ x, x ∂μ‖ ^ 2 + Matrix.trace (covMatrix μ) := by
  classical
  have hcoord (i : ι) : MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 μ := by
    simpa only [id_eq, EuclideanSpace.coe_proj] using
      hμ.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj i)
  have hsq (i : ι) : Integrable (fun x : EuclideanSpace ℝ ι => (x i) ^ 2) μ := by
    have h := (memLp_two_iff_integrable_sq_norm (hcoord i).aestronglyMeasurable).mp (hcoord i)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hmean (i : ι) : (∫ x, x ∂μ) i = ∫ x, x i ∂μ := by
    exact eval_integral_piLp (q := 2) (fun j => (hcoord j).integrable one_le_two) i
  have hnorm : (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) = fun x => ∑ i, (x i) ^ 2 :=
    funext EuclideanSpace.real_norm_sq_eq
  rw [hnorm, integral_finsetSum Finset.univ (fun i _ => hsq i),
    EuclideanSpace.real_norm_sq_eq, Matrix.trace]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, covMatrix_apply,
    covariance_self (hcoord i).aemeasurable, variance_eq_sub (hcoord i), hmean]
  ring_nf
  rfl

section IsometryInvariant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- For a measure with finite second moment invariant under every linear isometry, the variance
in a direction depends only on the length of the direction vector. -/
private lemma covarianceBilin_self_eq_of_norm_eq [IsFiniteMeasure μ]
    (hμ : ∀ f : E ≃ₗᵢ[ℝ] E, μ.map f = μ) (h : MemLp id 2 μ) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    covarianceBilin μ x x = covarianceBilin μ y y := by
  -- The reflection exchanging `x` and `y` is an isometry whose adjoint sends `y` to `x`.
  set f := (ℝ ∙ (x - y))ᗮ.reflection
  have hfy : f.symm y = x := by
    rw [LinearIsometryEquiv.symm_apply_eq, Submodule.reflection_sub hxy]
  have := covarianceBilin_map h (f : E →L[ℝ] E) y y
  simp only [LinearIsometryEquiv.adjoint_eq_symm] at this
  simpa [hμ f, hfy] using this.symm

/-- **Covariance of an isotropic law.** A finite measure on a finite-dimensional real inner
product space that is invariant under every linear isometry has covariance a multiple of the inner
product, the multiple being the second moment divided by the dimension. No moment hypothesis is
needed: without a finite second moment both sides vanish. -/
theorem covarianceBilin_eq_smul_innerSL [IsFiniteMeasure μ]
    (hμ : ∀ f : E ≃ₗᵢ[ℝ] E, μ.map f = μ) :
    covarianceBilin μ = ((∫ x, ‖x‖ ^ 2 ∂μ) / Module.finrank ℝ E) • innerSL ℝ := by
  by_cases h : MemLp id 2 μ
  swap
  · have : ¬ Integrable (fun x ↦ ‖x‖ ^ 2) μ := by
      rwa [memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id] at h
    rw [covarianceBilin_of_not_memLp h, integral_undef this]
    ext
    simp
  rcases subsingleton_or_nontrivial E with hE | hE
  · ext x y
    simp [Subsingleton.elim x 0]
  -- Invariance under `-1` makes the mean vanish, so covariance is the second-moment form.
  have hm : ∫ x, x ∂μ = 0 := by
    have : μ.IsNegInvariant := ⟨hμ (LinearIsometryEquiv.neg ℝ)⟩
    exact integral_eq_zero_of_odd fun x ↦ rfl
  set Q : E → ℝ := fun x ↦ covarianceBilin μ x x
  set d := Module.finrank ℝ E
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  set b := stdOrthonormalBasis ℝ E
  set e := b ⟨0, Module.finrank_pos⟩
  have he : ‖e‖ = 1 := b.orthonormal.1 _
  -- Summing the common value of `Q` over an orthonormal basis gives the second moment.
  have htrace : (d : ℝ) * Q e = ∫ x, ‖x‖ ^ 2 ∂μ := by
    have hQb : ∀ i, Q (b i) = Q e := fun i ↦
      covarianceBilin_self_eq_of_norm_eq hμ h (by rw [b.orthonormal.1 i, he])
    have hint : ∀ i, Integrable (fun z ↦ ⟪b i, z⟫ ^ 2) μ := fun i ↦ by
      have := ((innerSL ℝ (b i)).comp_memLp' h).integrable_mul ((innerSL ℝ (b i)).comp_memLp' h)
      simpa [sq, Pi.mul_def] using this
    calc (d : ℝ) * Q e = ∑ i, Q (b i) := by simp [hQb, d]
      _ = ∫ x, ∑ i, ⟪b i, x⟫ ^ 2 ∂μ := by
        rw [integral_finsetSum _ fun i _ ↦ hint i]
        simp [Q, covarianceBilin_apply h, hm, sq]
      _ = ∫ x, ‖x‖ ^ 2 ∂μ := by simp_rw [b.sum_sq_inner_right]
  have hQ : ∀ x, Q x = ‖x‖ ^ 2 * Q e := fun x ↦ by
    have := covarianceBilin_self_eq_of_norm_eq hμ h (x := x) (y := ‖x‖ • e)
      (by simp [norm_smul, he])
    simp only [Q, this, map_smul, smul_apply, smul_eq_mul]
    ring
  -- Polarization recovers the bilinear form from the quadratic form `Q`.
  ext x y
  have hpol : Q (x + y) = Q x + 2 * covarianceBilin μ x y + Q y := by
    simp only [Q, map_add, add_apply, covarianceBilin_comm y x]
    ring
  have hxy : covarianceBilin μ x y = Q e * ⟪x, y⟫ := by
    rw [hQ, hQ x, hQ y, norm_add_sq_real] at hpol
    linarith
  rw [hxy, ← htrace, smul_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    mul_div_cancel_left₀ _ hd]

end IsometryInvariant

end TauCeti
