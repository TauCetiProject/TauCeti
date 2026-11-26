/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Data.Matrix.Mul
import TauCeti.LinearAlgebra.Matrix.PosSemidef
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# Conditioning a Gaussian vector with rank-one covariance

A Gaussian vector with mean `m` and rank-one covariance `c cᵀ` is `m + Z • c` for a single
standard Gaussian factor `Z`. Observing a block whose loadings do not all vanish therefore
determines `Z`, and with it the whole vector: the conditional law of the retained block is a
point mass. The observed covariance is singular as soon as the observed block has two
coordinates, so this is a test of the pseudoinverse conditioning formulas of
`TauCeti.Probability.condDistrib_multivariateGaussian`.

Write `a` and `b` for the retained and observed loadings. The observed covariance `b bᵀ` has
pseudoinverse `b bᵀ / (b ⬝ b)²`, the generalized Schur complement vanishes when `b ≠ 0`, and the
regression mean is `m₁ + a (b ⬝ (x₂ - m₂)) / (b ⬝ b)` at every observation `x₂`. Almost surely
the observed deviation `x₂ - m₂` is a multiple of `b`, so the conditional law is the point mass
at `m₁ + a (x₂ k - m₂ k) / b k` for any observed coordinate `k` with `b k ≠ 0`.

Constant positive covariance `v` describes jointly Gaussian coordinates that are almost surely
identical up to their means. With a nonempty observed block, the pointwise kernel shifts the
retained means by the average observed deviation. Almost surely this agrees with the shift by
any one observed deviation.

## Main results

* `Matrix.gaussianCondCov_vecMulVec_self`: the conditional covariance vanishes when some
  observed loading is nonzero;
* `EuclideanSpace.gaussianCondMean_vecMulVec_self_apply`: the regression mean;
* `EuclideanSpace.gaussianCondKernel_vecMulVec_self`: the conditional kernel is a point mass;
* `EuclideanSpace.gaussianCondKernel_matrixOf_const`: for positive constant covariance the
  pointwise kernel uses the average observed deviation;
* `TauCeti.Probability.condDistrib_multivariateGaussian_vecMulVec_self`: the regular conditional
  law is the point mass determined by one observed coordinate;
* `TauCeti.Probability.condDistrib_multivariateGaussian_const`: the case of identical
  coordinates.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 2.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace Matrix

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A rank-one covariance conditions to zero covariance once some observed loading is nonzero:
the observed block then determines the common Gaussian factor. -/
@[simp]
theorem gaussianCondCov_vecMulVec_self {c : ι ⊕ κ → ℝ} (hc : ∃ k, c (Sum.inr k) ≠ 0) :
    (vecMulVec c c).gaussianCondCov = 0 := by
  obtain ⟨k, hk⟩ := hc
  have hb : (c ∘ Sum.inr) ⬝ᵥ (c ∘ Sum.inr) ≠ 0 := fun h ↦
    hk (congrFun (dotProduct_self_eq_zero.mp h) k)
  simp only [gaussianCondCov_def, submatrix_vecMulVec]
  rw [covariancePseudoInverse_vecMulVec_self]
  simp only [Matrix.mul_smul, Matrix.smul_mul, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  set s := (c ∘ Sum.inr) ⬝ᵥ (c ∘ Sum.inr)
  rw [show (s ^ 2)⁻¹ * s * s = 1 by field_simp, one_smul, sub_self]

end Matrix

namespace EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- For a rank-one covariance `c cᵀ`, the regression mean adds to `m₁` the retained loading
times the loading-weighted observed deviation, divided by the squared length of the observed
loadings. At zero observed loadings it is `m₁`. -/
theorem gaussianCondMean_vecMulVec_self_apply (m : EuclideanSpace ℝ (ι ⊕ κ)) (c : ι ⊕ κ → ℝ)
    (x₂ : EuclideanSpace ℝ κ) (i : ι) :
    m.gaussianCondMean (vecMulVec c c) x₂ i = m (Sum.inl i) +
      c (Sum.inl i) * (∑ k, c (Sum.inr k) * (x₂ k - m (Sum.inr k))) /
        ∑ k, c (Sum.inr k) ^ 2 := by
  simp only [gaussianCondMean_def, submatrix_vecMulVec]
  rw [covariancePseudoInverse_vecMulVec_self, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_smul]
  -- Read the Euclidean operator and the block-coordinate equivalence on coordinates.
  simp only [EuclideanSpace.sumEquivProd_apply_fst, map_smul, LinearMap.smul_apply, map_sub,
    toLin'_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, ofLp_toLpLin,
    smul_eq_mul, add_right_inj]
  have hmulVec (w : κ → ℝ) : (vecMulVec (c ∘ Sum.inl) (c ∘ Sum.inr) *ᵥ w) i =
      c (Sum.inl i) * ∑ k, c (Sum.inr k) * w k := by
    simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have hnorm : (c ∘ Sum.inr) ⬝ᵥ (c ∘ Sum.inr) = ∑ k, c (Sum.inr k) ^ 2 := by
    simp [dotProduct, pow_two]
  rw [hmulVec, hmulVec, hnorm, ← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, EuclideanSpace.sumEquivProd_apply_snd]
  rcases eq_or_ne (∑ k, c (Sum.inr k) ^ 2) 0 with h | h
  · simp [h]
  · field_simp

variable [DecidableEq ι]

/-- When some observed loading is nonzero, the conditional kernel of a rank-one covariance is
the point mass at the regression mean, at every observation. -/
theorem gaussianCondKernel_vecMulVec_self (m : EuclideanSpace ℝ (ι ⊕ κ)) {c : ι ⊕ κ → ℝ}
    (hc : ∃ k, c (Sum.inr k) ≠ 0) (x₂ : EuclideanSpace ℝ κ) :
    m.gaussianCondKernel (vecMulVec c c) x₂ =
      Measure.dirac (m.gaussianCondMean (vecMulVec c c) x₂) := by
  rw [gaussianCondKernel_apply, Matrix.gaussianCondCov_vecMulVec_self hc,
    TauCeti.Probability.multivariateGaussian_zero_right]

/-- With positive constant covariance and a nonempty observed block, the conditional Gaussian
kernel is Dirac at the retained means shifted by the average observed deviation. This holds at
every ambient observation, including outside the affine support. -/
theorem gaussianCondKernel_matrixOf_const [Nonempty κ] (m : EuclideanSpace ℝ (ι ⊕ κ))
    {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ κ) :
    m.gaussianCondKernel (Matrix.of fun _ _ ↦ c) x =
      Measure.dirac (WithLp.toLp 2 fun i ↦ m (Sum.inl i) +
        (∑ j, (x j - m (Sum.inr j))) / Fintype.card κ) := by
  have hcov : (Matrix.of fun _ _ ↦ c : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) =
      vecMulVec (fun _ ↦ √c) (fun _ ↦ √c) := by
    rw [vecMulVec_const_const, Real.mul_self_sqrt hc.le]
  have hload : ∃ j : κ, (fun _ : ι ⊕ κ ↦ √c) (Sum.inr j) ≠ 0 :=
    ⟨Classical.arbitrary κ, (Real.sqrt_pos.2 hc).ne'⟩
  rw [hcov, m.gaussianCondKernel_vecMulVec_self hload]
  congr 1
  ext i
  rw [gaussianCondMean_vecMulVec_self_apply]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.sq_sqrt hc.le, ← mul_assoc, Real.mul_self_sqrt hc.le]
  rw [mul_comm (Fintype.card κ : ℝ) c, mul_div_mul_left _ _ hc.ne']

end EuclideanSpace

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Conditioning a rank-one Gaussian vector.** If the joint covariance is `c cᵀ` and the
observed loading `c k` is nonzero, the regular conditional law of the retained block is almost
surely the point mass at `m₁ + a (x₂ k - m₂ k) / c k`, where `a` is the retained loading: the
`k`-th observed coordinate determines the common Gaussian factor, even though the observed
covariance is singular in dimension at least two. -/
theorem condDistrib_multivariateGaussian_vecMulVec_self {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (X : Ω → EuclideanSpace ℝ (ι ⊕ κ))
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {c : ι ⊕ κ → ℝ}
    (hX : HasLaw X (multivariateGaussian m (vecMulVec c c)) P) {k : κ}
    (hk : c (Sum.inr k) ≠ 0) :
    ∀ᵐ x₂ ∂P.map fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2,
      condDistrib (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).1)
          (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2) P x₂ =
        Measure.dirac (WithLp.toLp 2 fun i ↦
          m (Sum.inl i) + c (Sum.inl i) / c (Sum.inr k) * (x₂ k - m (Sum.inr k))) := by
  -- Almost surely the observed deviations are proportional to the observed loadings.
  have hline : ∀ᵐ ω ∂P, ∃ t : ℝ, ∀ j, X ω j - m j = t * c j :=
    ae_of_ae_map hX.aemeasurable
      (hX.map_eq ▸ ae_exists_sub_eq_mul_multivariateGaussian_vecMulVec_self m c)
  have hobs : ∀ᵐ x₂ ∂P.map fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2,
      ∀ j, (x₂ j - m (Sum.inr j)) * c (Sum.inr k) = (x₂ k - m (Sum.inr k)) * c (Sum.inr j) := by
    rw [ae_map_iff (by fun_prop) ?_]
    · filter_upwards [hline] with ω ⟨t, ht⟩ j
      have h₁ := ht (Sum.inr j)
      have h₂ := ht (Sum.inr k)
      simp only [EuclideanSpace.sumEquivProd_apply_snd]
      linear_combination c (Sum.inr k) * h₁ - c (Sum.inr j) * h₂
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j ↦ measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hpos : 0 < ∑ j, c (Sum.inr j) ^ 2 :=
    Finset.sum_pos' (fun j _ ↦ sq_nonneg _) ⟨k, Finset.mem_univ k, by positivity⟩
  filter_upwards [condDistrib_multivariateGaussian X m hX
    (posSemidef_vecMulVec_self c), hobs] with x₂ hx₂ hprop
  rw [hx₂, EuclideanSpace.gaussianCondKernel_vecMulVec_self m ⟨k, hk⟩]
  congr 1
  ext i
  rw [EuclideanSpace.gaussianCondMean_vecMulVec_self_apply]
  have hsum : ∑ j, c (Sum.inr j) * (x₂ j - m (Sum.inr j)) =
      (x₂ k - m (Sum.inr k)) / c (Sum.inr k) * ∑ j, c (Sum.inr j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
    linear_combination c (Sum.inr j) * hprop j
  rw [hsum]
  field_simp

/-- **Conditioning identical Gaussian coordinates.** If all covariances equal `v`, the
coordinates agree almost surely up to their means. Conditioning on any block of them, such as
on `(Z, Z)` despite its singular covariance, gives almost surely the point mass at the retained
means shifted by the deviation of any one observed coordinate. For `v ≤ 0` the law is the point
mass at `m` and the observed deviation vanishes almost surely. -/
theorem condDistrib_multivariateGaussian_const {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (X : Ω → EuclideanSpace ℝ (ι ⊕ κ))
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {v : ℝ}
    (hX : HasLaw X (multivariateGaussian m (Matrix.of fun _ _ ↦ v)) P) (k : κ) :
    ∀ᵐ x₂ ∂P.map fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2,
      condDistrib (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).1)
          (fun ω ↦ (EuclideanSpace.sumEquivProd (X ω)).2) P x₂ =
        Measure.dirac (WithLp.toLp 2 fun i ↦ m (Sum.inl i) + (x₂ k - m (Sum.inr k))) := by
  rcases lt_or_ge 0 v with hv | hv
  · -- Positive variance is the rank-one case with every loading equal to `√v`.
    have hcov : (Matrix.of fun _ _ ↦ v : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) =
        vecMulVec (fun _ ↦ √v) (fun _ ↦ √v) := by
      rw [vecMulVec_const_const, Real.mul_self_sqrt hv.le]
    rw [hcov] at hX
    have hsqrt : √v ≠ 0 := (Real.sqrt_pos.2 hv).ne'
    filter_upwards [condDistrib_multivariateGaussian_vecMulVec_self X m hX (k := k) hsqrt]
      with x₂ hx₂
    rw [hx₂, div_self hsqrt]
    simp
  -- Otherwise the joint law is the point mass at `m`, so both blocks are almost surely constant.
  have hdirac : multivariateGaussian m (Matrix.of fun _ _ ↦ v : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) =
      Measure.dirac m := by
    rcases hv.lt_or_eq with hv | rfl
    · exact multivariateGaussian_of_not_posSemidef m fun h ↦
        (h.diag_nonneg (i := Sum.inr k)).not_gt (by simpa using hv)
    · have hzero : (Matrix.of fun _ _ ↦ (0 : ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) = 0 := by
        ext
        simp
      rw [hzero, multivariateGaussian_zero_right]
  rw [hdirac] at hX
  filter_upwards [condDistrib_sumEquivProd_of_hasLaw_dirac X m hX] with x₂ ⟨hm, hx₂⟩
  rw [hx₂, hm]
  congr 1
  ext i
  simp only [EuclideanSpace.sumEquivProd_apply_fst, EuclideanSpace.sumEquivProd_apply_snd,
    sub_self, add_zero]

end TauCeti.Probability
