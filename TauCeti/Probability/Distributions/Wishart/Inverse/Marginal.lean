/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Wishart.Inverse.Moments

import TauCeti.LinearAlgebra.Matrix.Cholesky.Basic

/-!
# Diagonal marginals of the inverse-Wishart law

For a positive-definite scale `S`, every diagonal entry of an inverse-Wishart matrix of degree `n`
has the inverse-gamma law of shape `(n - p + 1) / 2` and scale `S i i / 2`. Equivalently, if `W`
is Wishart of degree `n > p - 1` and scale `S⁻¹`, the reciprocal of the diagonal entry
`(W⁻¹) i i` — the Schur complement of the complementary principal block of `W` — is `(S i i)⁻¹`
times a chi-squared variable with `n - p + 1` degrees of freedom. These scalar laws are what the
inverse-Wishart family offers to one-dimensional observables, such as its diagonal quantiles.
The general-scale laws extend the standard-scale case
`TauCeti.Probability.map_coe_apply_inverseWishartMeasure_one`.

When the degree is at most `p - 1` the inverse-Wishart law is zero, and so is the inverse-gamma
law of nonpositive shape, so the inverse-gamma statement needs no hypothesis on the degree.

## Main results

* `TauCeti.Probability.map_coe_apply_inverseWishartMeasure`: the diagonal entries of an
  inverse-Wishart matrix are inverse gamma.
* `TauCeti.Probability.map_inv_inv_apply_nonsingularWishartMeasure`: the reciprocal diagonal
  entries of the inverse of a Wishart matrix are scaled chi-squared.
* `TauCeti.Probability.hasLaw_coe_apply_inverseWishartMeasure` and
  `TauCeti.Probability.hasLaw_inv_inv_apply_nonsingularWishartMeasure`: the corresponding
  statements for random matrices.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Theorem 3.2.10 and
  Section 3.2.2.
* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes 53,
  chapter 8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped Matrix

namespace TauCeti.Probability

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- **The diagonal entries of an inverse-Wishart matrix are inverse gamma.** For a
positive-definite scale `S`, the entry `(i, i)` of an inverse-Wishart matrix of degree `n` has the
inverse-gamma law of shape `(n - p + 1) / 2` and scale `S i i / 2`. For degrees at most `p - 1`
both sides are the zero measure. -/
theorem map_coe_apply_inverseWishartMeasure (hS : S.PosDef) (i : Fin p) :
    (inverseWishartMeasure n S).map
        (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (B : Matrix (Fin p) (Fin p) ℝ) i i) =
      inverseGammaMeasure ((n - p + 1) / 2) (S i i / 2) := by
  rcases le_or_gt n ((p : ℝ) - 1) with hn | hn
  · rw [inverseWishartMeasure_of_le S hn, Measure.map_zero, inverseGammaMeasure_of_not_pos]
    exact fun h ↦ by linarith [h.1]
  -- Factor `S = C * Cᵀ` with the `i`-th row of `C` supported at `j`. Congruence by `C` carries
  -- the standard inverse-Wishart law to scale `S`, and on the entry `(i, i)` it multiplies the
  -- entry `(j, j)` by `C i j ^ 2 = S i i`.
  obtain ⟨C, j, hC, hrow⟩ := hS.exists_generalLinearGroup_mul_transpose_eq_and_apply_eq_zero i
  have hSii : S i i = (C : Matrix (Fin p) (Fin p) ℝ) i j ^ 2 := by
    rw [← hC, Matrix.mul_apply, Fintype.sum_eq_single j fun a ha ↦ by rw [hrow a ha, zero_mul],
      Matrix.transpose_apply, sq]
  have hmap := map_symmetricCongruence_inverseWishartMeasure n 1 C
  rw [Matrix.mul_one, hC] at hmap
  have hfun : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (B : Matrix (Fin p) (Fin p) ℝ) i i) ∘ Matrix.GeneralLinearGroup.symmetricCongruence C =
      ((C : Matrix (Fin p) (Fin p) ℝ) i j ^ 2 * ·) ∘
        fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (B : Matrix (Fin p) (Fin p) ℝ) j j :=
    funext (Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply_self_of_apply_eq_zero hrow)
  calc (inverseWishartMeasure n S).map
          (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
            (B : Matrix (Fin p) (Fin p) ℝ) i i)
      _ = ((inverseWishartMeasure n 1).map
            (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
              (B : Matrix (Fin p) (Fin p) ℝ) j j)).map
            ((C : Matrix (Fin p) (Fin p) ℝ) i j ^ 2 * ·) := by
        rw [← hmap, Measure.map_map (selfAdjoint.measurable_coe_apply i i)
            (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable, hfun,
          Measure.map_map (measurable_const_mul _) (selfAdjoint.measurable_coe_apply j j)]
      _ = (inverseGammaMeasure ((n - p + 1) / 2) (1 / 2)).map
            ((C : Matrix (Fin p) (Fin p) ℝ) i j ^ 2 * ·) := by
        rw [map_coe_apply_inverseWishartMeasure_one hn j]
      _ = inverseGammaMeasure ((n - p + 1) / 2) (S i i / 2) := by
        rw [inverseGammaMeasure_map_const_mul (hSii ▸ hS.diag_pos), ← hSii, mul_one_div]

/-- **The reciprocal diagonal entries of an inverted Wishart matrix are scaled chi-squared.** If
`W` is Wishart of degree `n > p - 1` and positive-definite scale `S⁻¹`, the reciprocal of the
diagonal entry `(W⁻¹) i i`, which is the Schur complement in `W` of the principal block away from
`i`, has the law of `(S i i)⁻¹` times a chi-squared variable with `n - p + 1` degrees of
freedom. -/
theorem map_inv_inv_apply_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (i : Fin p) :
    (nonsingularWishartMeasure n S⁻¹).map
        (fun W : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          ((W : Matrix (Fin p) (Fin p) ℝ)⁻¹ i i)⁻¹) =
      (chiSquaredMeasure (n - p + 1)).map ((S i i)⁻¹ * ·) := by
  have hk : 0 < n - p + 1 := by linarith
  have hSii : 0 < S i i := hS.diag_pos
  have hfun : (fun W : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((W : Matrix (Fin p) (Fin p) ℝ)⁻¹ i i)⁻¹) =
      Inv.inv ∘ (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (B : Matrix (Fin p) (Fin p) ℝ) i i) ∘ symmetricInv := by
    funext W
    rw [Function.comp_apply, Function.comp_apply, coe_symmetricInv]
  have hiw : (nonsingularWishartMeasure n S⁻¹).map
        ((fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (B : Matrix (Fin p) (Fin p) ℝ) i i) ∘ symmetricInv) =
      (gammaMeasure ((n - p + 1) / 2) (S i i / 2)).map Inv.inv := by
    rw [← Measure.map_map (selfAdjoint.measurable_coe_apply i i) measurable_symmetricInv,
      ← inverseWishartMeasure_def, map_coe_apply_inverseWishartMeasure hS i,
      inverseGammaMeasure_of_pos (by linarith) (by linarith)]
  calc (nonsingularWishartMeasure n S⁻¹).map
          (fun W : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
            ((W : Matrix (Fin p) (Fin p) ℝ)⁻¹ i i)⁻¹)
      _ = ((gammaMeasure ((n - p + 1) / 2) (S i i / 2)).map Inv.inv).map Inv.inv := by
        rw [hfun, ← Measure.map_map measurable_inv
          ((selfAdjoint.measurable_coe_apply i i).comp measurable_symmetricInv), hiw]
      _ = gammaMeasure ((n - p + 1) / 2) (S i i / 2) := by
        rw [Measure.map_map measurable_inv measurable_inv, inv_involutive.comp_self,
          Measure.map_id]
      _ = (chiSquaredMeasure (n - p + 1)).map ((S i i)⁻¹ * ·) := by
        rw [chiSquaredMeasure_eq_gammaMeasure hk,
          gammaMeasure_map_const_mul (by linarith) (by norm_num) (inv_pos.2 hSii)]
        congr 1
        field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A diagonal entry of a random inverse-Wishart matrix of positive-definite scale `S` has the
inverse-gamma law of shape `(n - p + 1) / 2` and scale `S i i / 2`. -/
theorem hasLaw_coe_apply_inverseWishartMeasure
    {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hX : HasLaw X (inverseWishartMeasure n S) P) (hS : S.PosDef) (i : Fin p) :
    HasLaw (fun ω ↦ (X ω : Matrix (Fin p) (Fin p) ℝ) i i)
      (inverseGammaMeasure ((n - p + 1) / 2) (S i i / 2)) P :=
  (⟨(selfAdjoint.measurable_coe_apply i i).aemeasurable,
      map_coe_apply_inverseWishartMeasure hS i⟩ :
    HasLaw _ _ (inverseWishartMeasure n S)).fun_comp hX

/-- For a random Wishart matrix `W` of degree `n > p - 1` and positive-definite scale `S⁻¹`, the
reciprocal of the diagonal entry `(W⁻¹) i i` has the law of `(S i i)⁻¹` times a chi-squared
variable with `n - p + 1` degrees of freedom. -/
theorem hasLaw_inv_inv_apply_nonsingularWishartMeasure
    {W : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hW : HasLaw W (nonsingularWishartMeasure n S⁻¹) P) (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    HasLaw (fun ω ↦ ((W ω : Matrix (Fin p) (Fin p) ℝ)⁻¹ i i)⁻¹)
      ((chiSquaredMeasure (n - p + 1)).map ((S i i)⁻¹ * ·)) P := by
  have hm : Measurable fun W : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      ((symmetricInv W : Matrix (Fin p) (Fin p) ℝ) i i)⁻¹ :=
    ((selfAdjoint.measurable_coe_apply i i).comp measurable_symmetricInv).inv
  simp only [coe_symmetricInv] at hm
  exact (⟨hm.aemeasurable, map_inv_inv_apply_nonsingularWishartMeasure hS hn i⟩ :
    HasLaw _ _ (nonsingularWishartMeasure n S⁻¹)).fun_comp hW

end TauCeti.Probability
