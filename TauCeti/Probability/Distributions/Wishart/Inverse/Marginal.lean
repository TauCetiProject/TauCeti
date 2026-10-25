/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Wishart.Inverse.Moments

import TauCeti.LinearAlgebra.Matrix.Cholesky.Basic
import Mathlib.LinearAlgebra.Matrix.Swap

/-!
# Diagonal marginals of the inverse-Wishart law

For a positive-definite scale `S`, every diagonal entry of an inverse-Wishart matrix of degree `n`
has the inverse-gamma law of shape `(n - p + 1) / 2` and scale `S i i / 2`. Equivalently, if `W`
is Wishart of degree `n` and scale `S⁻¹`, the reciprocal of the diagonal entry `(W⁻¹) i i` — the
Schur complement of the complementary principal block of `W` — is `(S i i)⁻¹` times a chi-squared
variable with `n - p + 1` degrees of freedom. These scalar laws are what the inverse-Wishart
family offers to one-dimensional observables, such as its diagonal quantiles.

The proof reduces to the standard scale, where the law of each diagonal entry is
`TauCeti.Probability.map_coe_apply_inverseWishartMeasure_one`. Factor `S = C * Cᵀ` with `C`
invertible and with its `i`-th row vanishing off a single column `j`: the Cholesky factor of `S`
after swapping the indices `i` and `0`, swapped back, has this shape because the first row of a
lower-triangular matrix is supported on its first entry. Congruence by `C` carries the standard
inverse-Wishart law to the one of scale `S`, and on the diagonal entry `(i, i)` it acts as the
scalar multiplication of the entry `(j, j)` by `C i j ^ 2 = S i i`, which multiplies the
inverse-gamma scale by `S i i`.

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

/-- A positive-definite matrix factors as `C * Cᵀ` with `C` invertible and with the `i`-th row of
`C` vanishing off a single column. Swapping the indices `i` and `0` and taking the Cholesky factor
gives a factor whose first row is supported on its first entry; swapping back moves that row to
position `i`. -/
private theorem exists_mul_transpose_eq_and_apply_eq_zero (hS : S.PosDef) (i : Fin p) :
    ∃ (C : Matrix.GeneralLinearGroup (Fin p) ℝ) (j : Fin p),
      (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = S ∧
        ∀ a, a ≠ j → (C : Matrix (Fin p) (Fin p) ℝ) i a = 0 := by
  set j : Fin p := ⟨0, i.pos⟩
  set P : Matrix (Fin p) (Fin p) ℝ := Matrix.swap ℝ i j with hPdef
  have hPP : P * P = 1 := Matrix.swap_mul_self i j
  have hPt : Pᵀ = P := Matrix.transpose_swap i j
  have hPS : (P * S * P).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hPt] using
      hS.mul_mul_conjTranspose_same
        (Matrix.vecMul_injective_iff_isUnit.2 ⟨⟨P, P, hPP, hPP⟩, rfl⟩)
  let A : PosDefMatrix p := ⟨⟨P * S * P, Matrix.isHermitian_iff_isSelfAdjoint.1 hPS.1⟩, hPS⟩
  set L : Matrix (Fin p) (Fin p) ℝ := (cholesky A).1
  have hL : L * Lᵀ = P * S * P := cholesky_mul_transpose A
  have hC : P * L * (P * L)ᵀ = S := by
    calc P * L * (P * L)ᵀ = P * (L * Lᵀ) * P := by
          rw [Matrix.transpose_mul, hPt, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (P * P) * S * (P * P) := by rw [hL]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  have hdet : (P * L).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hC
    rw [Matrix.det_mul, Matrix.det_transpose, h, zero_mul] at this
    exact hS.det_pos.ne' this.symm
  set C := Matrix.GeneralLinearGroup.mkOfDetNeZero (P * L) hdet
  have hcoe : (C : Matrix (Fin p) (Fin p) ℝ) = P * L := rfl
  refine ⟨C, j, hcoe ▸ hC, fun a ha ↦ ?_⟩
  -- the `i`-th row of `P * L` is the first row of the lower-triangular `L`
  have hja : j < a := Fin.lt_def.2 (Nat.pos_of_ne_zero fun h ↦ ha (Fin.ext h))
  rw [hcoe, hPdef, Matrix.swap_mul_apply_left]
  exact (cholesky A).2.1 (by simpa using hja)

/-- Congruence by a matrix whose `i`-th row vanishes off the column `j` reads the diagonal entry
`(i, i)` off the diagonal entry `(j, j)`, scaled by the square of the surviving entry. -/
private theorem coe_symmetricCongruence_apply_self_of_apply_eq_zero
    {C : Matrix.GeneralLinearGroup (Fin p) ℝ} {i j : Fin p}
    (hrow : ∀ a, a ≠ j → (C : Matrix (Fin p) (Fin p) ℝ) i a = 0)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (Matrix.GeneralLinearGroup.symmetricCongruence C B : Matrix (Fin p) (Fin p) ℝ) i i =
      (C : Matrix (Fin p) (Fin p) ℝ) i j ^ 2 * (B : Matrix (Fin p) (Fin p) ℝ) j j := by
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, Matrix.mul_apply,
    Fintype.sum_eq_single j fun a ha ↦ by rw [Matrix.transpose_apply, hrow a ha, mul_zero],
    Matrix.mul_apply, Fintype.sum_eq_single j fun a ha ↦ by rw [hrow a ha, zero_mul],
    Matrix.transpose_apply]
  ring

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
  obtain ⟨C, j, hC, hrow⟩ := exists_mul_transpose_eq_and_apply_eq_zero hS i
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
    funext (coe_symmetricCongruence_apply_self_of_apply_eq_zero hrow)
  rw [← hmap, Measure.map_map (selfAdjoint.measurable_coe_apply i i)
      (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable, hfun,
    ← Measure.map_map (measurable_const_mul _) (selfAdjoint.measurable_coe_apply j j),
    map_coe_apply_inverseWishartMeasure_one hn j,
    inverseGammaMeasure_map_const_mul (hSii ▸ hS.diag_pos), ← hSii, mul_one_div]

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
  rw [hfun, ← Measure.map_map measurable_inv
      ((selfAdjoint.measurable_coe_apply i i).comp measurable_symmetricInv),
    ← Measure.map_map (selfAdjoint.measurable_coe_apply i i) measurable_symmetricInv,
    ← inverseWishartMeasure_def, map_coe_apply_inverseWishartMeasure hS i,
    inverseGammaMeasure_of_pos (by linarith) (by linarith),
    Measure.map_map measurable_inv measurable_inv, inv_involutive.comp_self, Measure.map_id,
    chiSquaredMeasure_eq_gammaMeasure hk,
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
