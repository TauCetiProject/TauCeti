/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Quantile
public import TauCeti.Probability.Distributions.Wishart.LowDimension
public import TauCeti.Probability.Distributions.Wishart.Marginal

/-!
# Diagonal entries of Wishart matrices

A diagonal entry `W i i` of a Wishart matrix of degree `n` and scale `S` has the law of `S i i`
times a chi-squared variable with `n` degrees of freedom. This holds for the Gaussian-Gram law at
every natural degree and positive-semidefinite scale, and for the nonsingular density law at every
real degree `n > p - 1` and positive-definite scale. For the Gram law it includes the Dirac mass
at zero, which occurs at degree zero and when the diagonal scale entry vanishes.

Congruence by the `i`-th row of the identity matrix takes a symmetric matrix to its `1 × 1`
principal submatrix at `i`. Both laws are thereby reduced to their one-dimensional cases
`TauCeti.Probability.map_symmetricFinOneEquiv_wishartGramMeasure` and
`TauCeti.Probability.map_symmetricFinOneEquiv_nonsingularWishartMeasure`.

At an interior level `u`, the diagonal quantile is
`S i i * (2 * inverseRegularizedGamma (n / 2) u)`.
Its lower endpoint limit is zero. Its upper endpoint limit is infinite, except for the Dirac
Gram laws, whose quantiles stay at zero.

## Main results

* `TauCeti.Probability.map_coe_apply_wishartGramMeasure` and
  `TauCeti.Probability.map_coe_apply_nonsingularWishartMeasure`: the diagonal laws.
* `TauCeti.Probability.quantile_map_coe_apply_wishartGramMeasure` and
  `TauCeti.Probability.quantile_map_coe_apply_nonsingularWishartMeasure`: the diagonal quantiles.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Section 3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-! ### Diagonal laws -/

/-- **The diagonal entries of a Gaussian-Gram Wishart matrix are scaled chi-squared.** For a
positive-semidefinite scale `S`, the entry `(i, i)` of a Gram matrix of `ν` independent centred
Gaussian vectors of covariance `S` has the law of `S i i` times a chi-squared variable with `ν`
degrees of freedom. It is the Dirac mass at zero when `ν = 0` or `S i i = 0`. -/
theorem map_coe_apply_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef) (i : Fin p) :
    (wishartGramMeasure ν S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i) =
      (chiSquaredMeasure ν).map (S i i * ·) := by
  rw [← map_symmetricFinOneEquiv_symmetricCongruenceLinearMap_row,
    map_symmetricCongruenceLinearMap_wishartGramMeasure ν _ hS, Matrix.transpose_submatrix,
    Matrix.transpose_one, Matrix.submatrix_one_mul_mul_submatrix_one,
    map_symmetricFinOneEquiv_wishartGramMeasure ν hS.diag_nonneg, Matrix.submatrix_apply]

/-- **The diagonal entries of a nonsingular Wishart matrix are scaled chi-squared.** For a
positive-definite scale `S` and a real degree `n > p - 1`, the entry `(i, i)` of a Wishart matrix
has the law of `S i i` times a chi-squared variable with `n` degrees of freedom. -/
theorem map_coe_apply_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (i : Fin p) :
    (nonsingularWishartMeasure n S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i) =
      (chiSquaredMeasure n).map (S i i * ·) := by
  have hp : (1 : ℝ) ≤ p := Nat.one_le_cast.2 i.pos
  rw [← map_symmetricFinOneEquiv_symmetricCongruenceLinearMap_row,
    map_symmetricCongruenceLinearMap_submatrix_one_nonsingularWishartMeasure _
      (fun _ _ _ ↦ Subsingleton.elim _ _) hS hn,
    map_symmetricFinOneEquiv_nonsingularWishartMeasure (by linarith) hS.diag_pos,
    Matrix.submatrix_apply]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A diagonal entry of a random Gaussian-Gram Wishart matrix of positive-semidefinite scale `S`
has the law of `S i i` times a chi-squared variable with `ν` degrees of freedom. -/
theorem hasLaw_coe_apply_wishartGramMeasure
    {W : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} {ν : ℕ}
    (hW : HasLaw W (wishartGramMeasure ν S) P) (hS : S.PosSemidef) (i : Fin p) :
    HasLaw (fun ω ↦ (W ω : Matrix (Fin p) (Fin p) ℝ) i i)
      ((chiSquaredMeasure ν).map (S i i * ·)) P :=
  (⟨(selfAdjoint.measurable_coe_apply i i).aemeasurable,
      map_coe_apply_wishartGramMeasure ν hS i⟩ :
    HasLaw _ _ (wishartGramMeasure ν S)).fun_comp hW

/-- A diagonal entry of a random nonsingular Wishart matrix of degree `n > p - 1` and
positive-definite scale `S` has the law of `S i i` times a chi-squared variable with `n` degrees
of freedom. -/
theorem hasLaw_coe_apply_nonsingularWishartMeasure
    {W : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hW : HasLaw W (nonsingularWishartMeasure n S) P) (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (i : Fin p) :
    HasLaw (fun ω ↦ (W ω : Matrix (Fin p) (Fin p) ℝ) i i)
      ((chiSquaredMeasure n).map (S i i * ·)) P :=
  (⟨(selfAdjoint.measurable_coe_apply i i).aemeasurable,
      map_coe_apply_nonsingularWishartMeasure hS hn i⟩ :
    HasLaw _ _ (nonsingularWishartMeasure n S)).fun_comp hW

/-! ### Diagonal quantiles -/

/-- The quantile of a diagonal entry of a Gaussian-Gram Wishart matrix is the diagonal scale
entry times the chi-squared quantile. This includes the Dirac laws at zero degree or zero
diagonal scale entry, whose quantile is zero. -/
@[simp]
theorem quantile_map_coe_apply_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef) (i : Fin p)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((wishartGramMeasure ν S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u =
      S i i * (2 * inverseRegularizedGamma (ν / 2) u) := by
  rw [map_coe_apply_wishartGramMeasure ν hS i,
    quantile_map_const_mul_chiSquaredMeasure hS.diag_nonneg ν.cast_nonneg hu]

/-- The diagonal quantiles of a Gaussian-Gram Wishart matrix tend to zero as the level tends to
zero from above. -/
theorem tendsto_quantile_map_coe_apply_wishartGramMeasure_nhdsGT_zero (ν : ℕ)
    (hS : S.PosSemidef) (i : Fin p) :
    Tendsto (fun u ↦ (((wishartGramMeasure ν S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  rw [map_coe_apply_wishartGramMeasure ν hS i]
  exact tendsto_quantile_map_const_mul_chiSquaredMeasure_nhdsGT_zero hS.diag_nonneg
    ν.cast_nonneg

/-- The diagonal quantiles of a Gaussian-Gram Wishart matrix tend to positive infinity as the level
tends to one from below, unless the degree or the diagonal scale entry vanishes, when they remain
at zero. -/
theorem tendsto_quantile_map_coe_apply_wishartGramMeasure_nhdsLT_one (ν : ℕ)
    (hS : S.PosSemidef) (i : Fin p) :
    Tendsto (fun u ↦ (((wishartGramMeasure ν S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if S i i = 0 ∨ ν = 0 then 0 else ⊤)) := by
  rw [map_coe_apply_wishartGramMeasure ν hS i]
  simpa only [Nat.cast_eq_zero] using
    tendsto_quantile_map_const_mul_chiSquaredMeasure_nhdsLT_one hS.diag_nonneg ν.cast_nonneg

/-- The quantile of a diagonal entry of a nonsingular Wishart matrix is the diagonal scale entry
times the chi-squared quantile. -/
@[simp]
theorem quantile_map_coe_apply_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (i : Fin p) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((nonsingularWishartMeasure n S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u =
      S i i * (2 * inverseRegularizedGamma (n / 2) u) := by
  have hn₀ : 0 ≤ n := by linarith [(Nat.one_le_cast (α := ℝ)).2 i.pos]
  rw [map_coe_apply_nonsingularWishartMeasure hS hn i,
    quantile_map_const_mul_chiSquaredMeasure hS.diag_pos.le hn₀ hu]

/-- The diagonal quantiles of a nonsingular Wishart matrix tend to zero as the level tends to zero
from above. -/
theorem tendsto_quantile_map_coe_apply_nonsingularWishartMeasure_nhdsGT_zero (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    Tendsto (fun u ↦ (((nonsingularWishartMeasure n S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hn₀ : 0 ≤ n := by linarith [(Nat.one_le_cast (α := ℝ)).2 i.pos]
  rw [map_coe_apply_nonsingularWishartMeasure hS hn i]
  exact tendsto_quantile_map_const_mul_chiSquaredMeasure_nhdsGT_zero hS.diag_pos.le hn₀

/-- The diagonal quantiles of a nonsingular Wishart matrix tend to positive infinity as the level
tends to one from below. -/
theorem tendsto_quantile_map_coe_apply_nonsingularWishartMeasure_nhdsLT_one (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    Tendsto (fun u ↦ (((nonsingularWishartMeasure n S).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ) i i)).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  have hn₀ : 0 < n := by linarith [(Nat.one_le_cast (α := ℝ)).2 i.pos]
  have h := tendsto_quantile_map_const_mul_chiSquaredMeasure_nhdsLT_one
    (hS.diag_pos (i := i)).le hn₀.le
  rw [ite_eq_right (by simp [hS.diag_pos.ne', hn₀.ne'])] at h
  rwa [map_coe_apply_nonsingularWishartMeasure hS hn i]

end TauCeti.Probability
