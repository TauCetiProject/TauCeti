/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional

/-!
# Multivariate Gaussian laws in one and two dimensions

A multivariate Gaussian law over a one-element index type is a real Gaussian law read on the
single coordinate.  Splitting a two-element index type into two singleton blocks turns the
conditional-law formulas of `TauCeti/Probability/Distributions/Gaussian/Conditional.lean` into
the classical bivariate ones: writing `v₁`, `v₂` for the two variances, `c` for the covariance
and `ρ = c / √(v₁ v₂)` for the correlation, the conditional mean of the first coordinate given
the second is the regression line `m₁ + ρ √(v₁ / v₂) (x₂ - m₂)` and the conditional variance is
`v₁ (1 - ρ ^ 2)`.

Both the mean and the variance are recorded twice.  Once for an arbitrary `2 × 2` matrix, with
regression slope `S₁₂ / S₂₂` and Schur complement `S₁₁ - S₁₂ S₂₁ / S₂₂`; these forms need no
hypothesis, but they are the regression slope and the residual variance only when the matrix is
a covariance matrix.  And once in the correlation form above, which needs positive
semidefiniteness: it supplies the symmetry `S₂₁ = S₁₂`, and it rules out the one degenerate
configuration the correlation form would otherwise miss, namely a vanishing variance alongside a
nonzero covariance.  In the correlation form the variances and the correlation are bound by
defining hypotheses rather than spelled out inside the conclusion, which would otherwise repeat
the four matrix entries several times.

## Main results

* `TauCeti.multivariateGaussian_eq_map_single` — over a one-element index type the multivariate
  Gaussian law is a real Gaussian law carried to the unique coordinate;
* `EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef` and
  `Matrix.gaussianCondCov_apply_of_unique_of_posSemidef` — the bivariate conditional mean and
  variance in terms of the correlation;
* `EuclideanSpace.gaussianCondKernel_apply_of_unique_of_posSemidef` — the bivariate conditional
  law itself.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

variable {ι κ : Type*}

namespace TauCeti

/-! ### The one-dimensional multivariate Gaussian -/

/-- **Over a one-element index type the multivariate Gaussian law is a real Gaussian law.**  It is
the image of `gaussianReal` with mean `μ default` and variance `S default default` under the
inclusion of the unique coordinate.

No hypothesis on `S` is needed because the two totalizations agree: a negative `S default default`
makes the left-hand side the Dirac law at `μ` and truncates the variance on the right to zero. -/
theorem multivariateGaussian_eq_map_single [Unique ι] [DecidableEq ι]
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    multivariateGaussian μ S =
      (gaussianReal (μ default) (S default default).toNNReal).map
        (EuclideanSpace.single default) := by
  have hsingle : Measurable (EuclideanSpace.single (default : ι) : ℝ → EuclideanSpace ℝ ι) := by
    have h : (EuclideanSpace.single (default : ι) : ℝ → EuclideanSpace ℝ ι) =
        (EuclideanSpace.equiv ι ℝ).symm ∘ Pi.single default := rfl
    rw [h]
    refine ((EuclideanSpace.equiv ι ℝ).symm.continuous.comp (continuous_pi fun j => ?_)).measurable
    simp only [Pi.single_apply]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have hcomp : (EuclideanSpace.single (default : ι)) ∘
      (fun x : EuclideanSpace ℝ ι => x default) = id := by
    funext x
    ext i
    simp [Unique.eq_default i]
  by_cases hS : S.PosSemidef
  · calc multivariateGaussian μ S
        = (multivariateGaussian μ S).map id := Measure.map_id.symm
      _ = ((multivariateGaussian μ S).map fun x => x default).map
            (EuclideanSpace.single default) := by
          rw [Measure.map_map hsingle (by fun_prop), hcomp]
      _ = _ := by rw [(measurePreserving_eval_multivariateGaussian hS).map_eq]
  · have hdiag : S default default ≤ 0 := by
      refine le_of_not_gt fun hpos => hS ?_
      have hS' : S = Matrix.diagonal fun _ : ι => S default default := by
        rw [Matrix.diagonal_unique]
        ext i j
        simp [Unique.eq_default i, Unique.eq_default j]
      rw [hS', Matrix.posSemidef_diagonal_iff]
      simp [hpos.le]
    rw [multivariateGaussian_of_not_posSemidef _ hS, Real.toNNReal_of_nonpos hdiag,
      gaussianReal_zero_var, Measure.map_dirac' hsingle]
    congr 1
    ext i
    simp [Unique.eq_default i]

/-! ### Degenerate bivariate covariance matrices -/

/-- A vanishing variance in a positive semidefinite matrix indexed by two singleton blocks forces
the covariance to vanish as well: otherwise the quadratic form takes a negative value at a
suitable vector. -/
private theorem posSemidef_apply_inl_inr_eq_zero [Unique ι] [Unique κ]
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef)
    (h₁₁ : S (Sum.inl default) (Sum.inl default) = 0) :
    S (Sum.inl default) (Sum.inr default) = 0 := by
  by_contra hc
  have hsymm : S (Sum.inr default) (Sum.inl default) = S (Sum.inl default) (Sum.inr default) := by
    simpa using hS.isHermitian.apply (Sum.inl default) (Sum.inr default)
  have h := hS.dotProduct_mulVec_nonneg (Sum.elim
    (fun _ => -(S (Sum.inr default) (Sum.inr default) + 1) /
      (2 * S (Sum.inl default) (Sum.inr default))) (fun _ => 1))
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fintype.sum_unique,
    Sum.elim_inl, Sum.elim_inr, star_trivial, h₁₁, hsymm] at h
  have hneg : (0 : ℝ) ≤ -1 := h.trans_eq (by field_simp; ring)
  norm_num at hneg

end TauCeti

/-! ### The bivariate conditional mean -/

namespace EuclideanSpace

/-- In the bivariate case the conditional mean is the regression line through the observed
coordinate, with slope the ratio of the covariance to the observed variance. -/
theorem gaussianCondMean_apply_of_unique [Unique ι] [Unique κ] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x₂ : EuclideanSpace ℝ κ) :
    m.gaussianCondMean S x₂ default =
      m (Sum.inl default) +
        S (Sum.inl default) (Sum.inr default) / S (Sum.inr default) (Sum.inr default) *
          (x₂ default - m (Sum.inr default)) := by
  have hlin : ∀ (A : Matrix ι κ ℝ) (y : EuclideanSpace ℝ κ),
      (A.toEuclideanLin y).ofLp = Matrix.mulVec A y.ofLp := fun A y => by
    simpa only [Matrix.toLin'_apply] using Matrix.ofLp_toLpLin (p := 2) (q := 2) A y
  rw [EuclideanSpace.gaussianCondMean_def]
  -- The sum of two Euclidean vectors has to be read through its underlying function to be
  -- evaluated at the unique coordinate.
  change (_ : EuclideanSpace ℝ ι).ofLp default = _
  rw [WithLp.ofLp_add, Pi.add_apply, hlin]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, EuclideanSpace.sumEquivProd,
    div_eq_mul_inv, Matrix.inv_subsingleton]

/-- **The bivariate conditional mean.**  Write `v₁`, `v₂` for the two variances of a positive
semidefinite `2 × 2` covariance matrix and `ρ` for the correlation.  The conditional mean of the
first coordinate given the second is the regression line `m₁ + ρ √(v₁ / v₂) (x₂ - m₂)`. -/
theorem gaussianCondMean_apply_of_unique_of_posSemidef [Unique ι] [Unique κ] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef)
    (x₂ : EuclideanSpace ℝ κ) {v₁ v₂ ρ : ℝ}
    (hv₁ : v₁ = S (Sum.inl default) (Sum.inl default))
    (hv₂ : v₂ = S (Sum.inr default) (Sum.inr default))
    (hρ : ρ = S (Sum.inl default) (Sum.inr default) / Real.sqrt (v₁ * v₂)) :
    m.gaussianCondMean S x₂ default =
      m (Sum.inl default) + ρ * Real.sqrt (v₁ / v₂) * (x₂ default - m (Sum.inr default)) := by
  have hv₁nonneg : 0 ≤ v₁ := by rw [hv₁]; exact hS.diag_nonneg
  have hv₂nonneg : 0 ≤ v₂ := by rw [hv₂]; exact hS.diag_nonneg
  have hslope : ρ * Real.sqrt (v₁ / v₂) =
      S (Sum.inl default) (Sum.inr default) / S (Sum.inr default) (Sum.inr default) := by
    rcases hv₁nonneg.eq_or_lt with hv₁zero | hv₁pos
    · -- A vanishing first variance forces a vanishing covariance, so both sides vanish.
      have hc : S (Sum.inl default) (Sum.inr default) = 0 :=
        TauCeti.posSemidef_apply_inl_inr_eq_zero hS (by rw [← hv₁, ← hv₁zero])
      simp [hρ, hc]
    rcases hv₂nonneg.eq_or_lt with hv₂zero | hv₂pos
    · -- A vanishing observed variance makes both sides vanish by division by zero.
      rw [← hv₂]
      simp [hρ, ← hv₂zero]
    have hs₂ : Real.sqrt v₂ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hv₂pos)
    rw [hρ, ← hv₂, Real.sqrt_mul hv₁pos.le, Real.sqrt_div hv₁pos.le]
    field_simp
    rw [Real.sq_sqrt hv₂pos.le]
  rw [gaussianCondMean_apply_of_unique, hslope]

end EuclideanSpace

/-! ### The bivariate conditional variance -/

namespace Matrix

/-- In the bivariate case the Schur complement of the observed block is
`S₁₁ - S₁₂ S₂₁ / S₂₂`.  For a covariance matrix this is the residual variance of the
regression. -/
theorem gaussianCondCov_apply_of_unique [Unique ι] [Unique κ] [DecidableEq κ]
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    S.gaussianCondCov default default =
      S (Sum.inl default) (Sum.inl default) -
        S (Sum.inl default) (Sum.inr default) * S (Sum.inr default) (Sum.inl default) /
          S (Sum.inr default) (Sum.inr default) := by
  simp only [Matrix.gaussianCondCov_def, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.submatrix_apply, Matrix.inv_subsingleton, Matrix.diagonal_apply,
    Fintype.sum_unique, ite_true, Ring.inverse_eq_inv, div_eq_mul_inv]
  ring

/-- **The bivariate conditional variance.**  With the notation of
`EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef`, the conditional variance of the
first coordinate given the second is `v₁ (1 - ρ ^ 2)`. -/
theorem gaussianCondCov_apply_of_unique_of_posSemidef [Unique ι] [Unique κ] [DecidableEq κ]
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef) {v₁ v₂ ρ : ℝ}
    (hv₁ : v₁ = S (Sum.inl default) (Sum.inl default))
    (hv₂ : v₂ = S (Sum.inr default) (Sum.inr default))
    (hρ : ρ = S (Sum.inl default) (Sum.inr default) / Real.sqrt (v₁ * v₂)) :
    S.gaussianCondCov default default = v₁ * (1 - ρ ^ 2) := by
  have hv₁nonneg : 0 ≤ v₁ := by rw [hv₁]; exact hS.diag_nonneg
  have hv₂nonneg : 0 ≤ v₂ := by rw [hv₂]; exact hS.diag_nonneg
  have hsymm : S (Sum.inr default) (Sum.inl default) = S (Sum.inl default) (Sum.inr default) := by
    simpa using hS.isHermitian.apply (Sum.inl default) (Sum.inr default)
  rw [gaussianCondCov_apply_of_unique, hsymm, ← hv₁, ← hv₂]
  rcases hv₁nonneg.eq_or_lt with hv₁zero | hv₁pos
  · -- A vanishing first variance forces a vanishing covariance, so both sides vanish.
    have hc : S (Sum.inl default) (Sum.inr default) = 0 :=
      TauCeti.posSemidef_apply_inl_inr_eq_zero hS (by rw [← hv₁, ← hv₁zero])
    simp [hc, ← hv₁zero]
  rcases hv₂nonneg.eq_or_lt with hv₂zero | hv₂pos
  · -- A vanishing observed variance makes `ρ` vanish and deletes the Schur correction, by
    -- division by zero on both sides.
    simp [hρ, ← hv₂zero]
  have hsq : Real.sqrt (v₁ * v₂) ^ 2 = v₁ * v₂ :=
    Real.sq_sqrt (mul_nonneg hv₁pos.le hv₂pos.le)
  rw [hρ, div_pow, hsq]
  field_simp

end Matrix

/-! ### The bivariate conditional law -/

namespace EuclideanSpace

/-- **The conditional law of a bivariate Gaussian.**  Conditionally on the second coordinate
taking the value `x₂`, the first coordinate of a jointly Gaussian pair with positive semidefinite
covariance is Gaussian with mean `m₁ + ρ √(v₁ / v₂) (x₂ - m₂)` and variance `v₁ (1 - ρ ^ 2)`,
read on the unique coordinate of the first block.  Together with
`TauCeti.condDistrib_multivariateGaussian` this identifies the regular conditional distribution
of a bivariate Gaussian pair. -/
theorem gaussianCondKernel_apply_of_unique_of_posSemidef [Unique ι] [Unique κ] [DecidableEq ι]
    [DecidableEq κ] (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS : S.PosSemidef) (x₂ : EuclideanSpace ℝ κ) {v₁ v₂ ρ : ℝ}
    (hv₁ : v₁ = S (Sum.inl default) (Sum.inl default))
    (hv₂ : v₂ = S (Sum.inr default) (Sum.inr default))
    (hρ : ρ = S (Sum.inl default) (Sum.inr default) / Real.sqrt (v₁ * v₂)) :
    m.gaussianCondKernel S x₂ =
      (gaussianReal
          (m (Sum.inl default) + ρ * Real.sqrt (v₁ / v₂) * (x₂ default - m (Sum.inr default)))
          (v₁ * (1 - ρ ^ 2)).toNNReal).map (EuclideanSpace.single default) := by
  rw [EuclideanSpace.gaussianCondKernel_apply, TauCeti.multivariateGaussian_eq_map_single,
    EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef m hS x₂ hv₁ hv₂ hρ,
    Matrix.gaussianCondCov_apply_of_unique_of_posSemidef hS hv₁ hv₂ hρ]

end EuclideanSpace
