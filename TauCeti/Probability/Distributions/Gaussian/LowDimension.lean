/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef
public import TauCeti.Probability.Distributions.Gaussian.Conditional

/-!
# One-dimensional Gaussian laws and conditioning on one coordinate

A multivariate Gaussian law over a one-element index type is a real Gaussian law read on the
single coordinate.  Splitting a two-element index type into two singleton blocks turns the
conditional-law formulas of `TauCeti/Probability/Distributions/Gaussian/Conditional.lean` into
the classical bivariate ones: writing `v₁`, `v₂` for the two variances, `c` for the covariance
and `ρ = c / √(v₁ v₂)` for the correlation, the conditional mean of the first coordinate given
the second is the regression line `m₁ + ρ √(v₁ / v₂) (x₂ - m₂)` and the conditional variance is
`v₁ (1 - ρ ^ 2)`.

When the observed block has one coordinate, the retained block can have any finite dimension;
the covariance formulas also allow arbitrary retained index types. For an arbitrary matrix, the
mean at retained coordinate `i` has slope `Sᵢ₂ / S₂₂`, and the conditional covariance entry at
`(i, j)` is `Sᵢⱼ - Sᵢ₂ S₂ⱼ / S₂₂`. These algebraic identities
need no covariance hypothesis. For a positive-semidefinite covariance, the mean and diagonal
covariance entries also have the correlation forms above: symmetry identifies `S₂ᵢ` with `Sᵢ₂`,
and a vanishing variance forces the corresponding covariance to vanish. The variances and
correlation are named through defining hypotheses to keep the formulas readable.

`ρ` is the correlation of the pair only when both variances are positive.  When one of them
vanishes there is no correlation to speak of and `ρ` is instead the totalized value `0 / 0 = 0`;
the correlation forms are then still true, but as algebraic identities in which every term
carrying `ρ` has disappeared.  Likewise, the conditional-law statement below is an identity of
kernels for any positive semidefinite covariance. The regular-conditional-distribution theorem
assumes a positive observed variance.

## Main results

* `EuclideanSpace.multivariateGaussian_eq_map_single` — over a one-element index type the
  multivariate Gaussian law is a real Gaussian law carried to the unique coordinate;
* `Matrix.gaussianCondCov_apply_of_unique` — with one observed coordinate, the Schur correction
  formula for any pair of retained coordinates;
* `EuclideanSpace.gaussianCondMean_apply_of_unique` — the regression formula at each retained
  coordinate when there is one observed coordinate;
* `EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef` and
  `Matrix.gaussianCondCov_apply_of_unique_of_posSemidef` — the conditional mean and variance at
  any retained coordinate, in terms of its correlation with the unique observed coordinate;
* `EuclideanSpace.gaussianCondKernel_apply_of_unique_of_posSemidef` — the bivariate conditional
  law itself;
* `TauCeti.Probability.condDistrib_multivariateGaussian_of_unique` — that law as the regular
  conditional distribution of a bivariate Gaussian pair, for a positive observed variance.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

variable {ι κ : Type*}

namespace EuclideanSpace

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
    exact ((EuclideanSpace.equiv ι ℝ).symm.continuous.comp
      (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) default).continuous).measurable
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

/-! ### Conditional mean with one observed coordinate -/

/-- With one observed coordinate, each coordinate of the conditional mean is a regression line,
with slope the ratio of its covariance with the observed coordinate to the observed variance. -/
theorem gaussianCondMean_apply_of_unique [Fintype ι] [Unique κ] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x₂ : EuclideanSpace ℝ κ) (i : ι) :
    m.gaussianCondMean S x₂ i =
      m (Sum.inl i) +
        S (Sum.inl i) (Sum.inr default) / S (Sum.inr default) (Sum.inr default) *
          (x₂ default - m (Sum.inr default)) := by
  rw [EuclideanSpace.gaussianCondMean_def]
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    EuclideanSpace.sumEquivProd, div_eq_mul_inv, Matrix.inv_subsingleton]

/-- With one observed coordinate, write `v₁` for the variance of retained coordinate `i`, `v₂`
for the observed variance, and `ρ` for their correlation. The conditional mean at `i` is the
regression line `m₁ + ρ √(v₁ / v₂) (x₂ - m₂)`.

`ρ` is the correlation only when both variances are positive; when one of them vanishes it is the
totalized `0 / 0 = 0`, and the identity holds because the regression slope vanishes as well. -/
theorem gaussianCondMean_apply_of_unique_of_posSemidef [Fintype ι] [Unique κ] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef)
    (x₂ : EuclideanSpace ℝ κ) (i : ι) {v₁ v₂ ρ : ℝ}
    (hv₁ : v₁ = S (Sum.inl i) (Sum.inl i))
    (hv₂ : v₂ = S (Sum.inr default) (Sum.inr default))
    (hρ : ρ = S (Sum.inl i) (Sum.inr default) / Real.sqrt (v₁ * v₂)) :
    m.gaussianCondMean S x₂ i =
      m (Sum.inl i) + ρ * Real.sqrt (v₁ / v₂) * (x₂ default - m (Sum.inr default)) := by
  have hv₁nonneg : 0 ≤ v₁ := by rw [hv₁]; exact hS.diag_nonneg
  have hv₂nonneg : 0 ≤ v₂ := by rw [hv₂]; exact hS.diag_nonneg
  have hslope : ρ * Real.sqrt (v₁ / v₂) =
      S (Sum.inl i) (Sum.inr default) / S (Sum.inr default) (Sum.inr default) := by
    rcases hv₁nonneg.eq_or_lt with hv₁zero | hv₁pos
    · -- A vanishing retained variance forces a vanishing covariance, so both sides vanish.
      have hc : S (Sum.inl i) (Sum.inr default) = 0 :=
        hS.eq_zero_of_apply_self_eq_zero_left (by rw [← hv₁, ← hv₁zero])
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

/-! ### Conditional covariance with one observed coordinate -/

namespace Matrix

/-- With one observed coordinate, each entry of the conditional covariance is the original
covariance minus the Schur correction `Sᵢ₂ S₂ⱼ / S₂₂`. The retained block can have arbitrary
dimension. -/
theorem gaussianCondCov_apply_of_unique [Unique κ] [DecidableEq κ]
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (i j : ι) :
    S.gaussianCondCov i j =
      S (Sum.inl i) (Sum.inl j) -
        S (Sum.inl i) (Sum.inr default) * S (Sum.inr default) (Sum.inl j) /
          S (Sum.inr default) (Sum.inr default) := by
  simp only [Matrix.gaussianCondCov_def, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.submatrix_apply, Matrix.inv_subsingleton, Matrix.diagonal_apply,
    Fintype.sum_unique, ite_true, Ring.inverse_eq_inv, div_eq_mul_inv]
  ring

/-- With the notation of `EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef`, the
conditional variance of retained coordinate `i` given the unique observed coordinate is
`v₁ (1 - ρ ^ 2)`.

As there, `ρ` is the correlation only when both variances are positive; when one of them vanishes
it is the totalized `0 / 0 = 0`, and the identity reduces to one with no `ρ` left in it. -/
theorem gaussianCondCov_apply_of_unique_of_posSemidef [Unique κ] [DecidableEq κ]
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef) (i : ι) {v₁ v₂ ρ : ℝ}
    (hv₁ : v₁ = S (Sum.inl i) (Sum.inl i))
    (hv₂ : v₂ = S (Sum.inr default) (Sum.inr default))
    (hρ : ρ = S (Sum.inl i) (Sum.inr default) / Real.sqrt (v₁ * v₂)) :
    S.gaussianCondCov i i = v₁ * (1 - ρ ^ 2) := by
  have hv₁nonneg : 0 ≤ v₁ := by rw [hv₁]; exact hS.diag_nonneg
  have hv₂nonneg : 0 ≤ v₂ := by rw [hv₂]; exact hS.diag_nonneg
  have hsymm : S (Sum.inr default) (Sum.inl i) = S (Sum.inl i) (Sum.inr default) := by
    simpa using hS.isHermitian.apply (Sum.inl i) (Sum.inr default)
  rw [gaussianCondCov_apply_of_unique, hsymm, ← hv₁, ← hv₂]
  rcases hv₁nonneg.eq_or_lt with hv₁zero | hv₁pos
  · -- A vanishing retained variance forces a vanishing covariance, so both sides vanish.
    have hc : S (Sum.inl i) (Sum.inr default) = 0 :=
      hS.eq_zero_of_apply_self_eq_zero_left (by rw [← hv₁, ← hv₁zero])
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

/-- For a positive-semidefinite bivariate covariance, the conditional Gaussian kernel at `x₂`
is a real Gaussian law with mean `m₁ + ρ √(v₁ / v₂) (x₂ - m₂)` and variance
`v₁ (1 - ρ ^ 2)`, read on the unique coordinate of the retained block.

This is an identity between the conditional Gaussian kernel and a real Gaussian law, and as such
needs no constraint on the observed variance. The regular-conditional-distribution theorem
`TauCeti.Probability.condDistrib_multivariateGaussian_of_unique` assumes a positive observed
variance. -/
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
  rw [EuclideanSpace.gaussianCondKernel_apply, multivariateGaussian_eq_map_single,
    EuclideanSpace.gaussianCondMean_apply_of_unique_of_posSemidef m hS x₂ default hv₁ hv₂ hρ,
    Matrix.gaussianCondCov_apply_of_unique_of_posSemidef hS default hv₁ hv₂ hρ]

end EuclideanSpace

namespace TauCeti.Probability

/-- **The regular conditional distribution of a bivariate Gaussian pair.**  For a jointly Gaussian
pair with positive semidefinite covariance and a positive observed variance, the conditional law
of the first coordinate given the second is the real Gaussian law with mean
`m₁ + ρ √(v₁ / v₂) (x₂ - m₂)` and variance `v₁ (1 - ρ ^ 2)`, read on the unique coordinate of the
first block.  Positive definiteness of the observed block says exactly that `v₂` is positive; if
`v₁` vanishes as well then `ρ` is again the totalized `0` and the law is the Dirac law at `m₁`. -/
theorem condDistrib_multivariateGaussian_of_unique {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] [Unique ι] [Unique κ] [DecidableEq ι] [DecidableEq κ]
    (X : Ω → EuclideanSpace ℝ (ι ⊕ κ)) (m : EuclideanSpace ℝ (ι ⊕ κ))
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hX : HasLaw X (multivariateGaussian m S) P)
    (hS : S.PosSemidef) (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) {v₁ v₂ ρ : ℝ}
    (hv₁ : v₁ = S (Sum.inl default) (Sum.inl default))
    (hv₂ : v₂ = S (Sum.inr default) (Sum.inr default))
    (hρ : ρ = S (Sum.inl default) (Sum.inr default) / Real.sqrt (v₁ * v₂)) :
    ∀ᵐ x₂ ∂P.map fun ω => (EuclideanSpace.sumEquivProd (X ω)).2,
      condDistrib (fun ω => (EuclideanSpace.sumEquivProd (X ω)).1)
          (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2) P x₂ =
        (gaussianReal
            (m (Sum.inl default) + ρ * Real.sqrt (v₁ / v₂) * (x₂ default - m (Sum.inr default)))
            (v₁ * (1 - ρ ^ 2)).toNNReal).map (EuclideanSpace.single default) := by
  filter_upwards [condDistrib_multivariateGaussian X m hX hS hS₂₂] with x₂ hx₂
  rw [hx₂, EuclideanSpace.gaussianCondKernel_apply_of_unique_of_posSemidef m hS x₂ hv₁ hv₂ hρ]

end TauCeti.Probability
