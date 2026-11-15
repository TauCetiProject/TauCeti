/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Rank perturbation bound for the empirical spectral measure

A perturbation of rank `r` of an `n × n` Hermitian matrix moves the distribution function of its
empirical spectral measure by at most `r / n`, uniformly in the point. This is the rank inequality
used to truncate or modify finitely many rows and columns of a random matrix without changing its
limiting spectral distribution.

The proof reads the distribution function of the spectral measure as the proportion of sorted
eigenvalues in `(-∞, t]` and applies the rank perturbation bound for eigenvalue counts. For Gram
matrices, `X Xᴴ - Y Yᴴ = (X - Y) Xᴴ + Y (X - Y)ᴴ` has rank at most twice the rank of `X - Y`.

## Main results

* `Matrix.IsHermitian.abs_spectralMeasure_Iic_sub_le_rank_div_card`: the distribution functions of
  the spectral measures of Hermitian `A` and `B` differ by at most `rank (A - B) / card n`;
* `Matrix.abs_spectralMeasure_mul_conjTranspose_self_Iic_sub_le_two_mul_rank_div_card`: the
  corresponding bound for the spectral measures of Gram matrices.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  Theorem A.43.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder

namespace Matrix

variable {ι m n 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] [Fintype n]
  [RCLike 𝕜]

/-- **Rank perturbation bound for the spectral measure.** The distribution functions of the
empirical spectral measures of two Hermitian matrices differ by at most the rank of their
difference divided by the size. -/
theorem IsHermitian.abs_spectralMeasure_Iic_sub_le_rank_div_card [Nonempty ι]
    {A B : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    |(A.spectralMeasure hA : Measure ℝ).real (Set.Iic t) -
        (B.spectralMeasure hB : Measure ℝ).real (Set.Iic t)| ≤
      ((A - B).rank : ℝ) / Fintype.card ι := by
  have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h := hA.abs_card_eigenvalues₀_le_sub_card_le_rank hB t
  rw [hA.spectralMeasure_real_Iic, hB.spectralMeasure_real_Iic, ← sub_div, abs_div,
    abs_of_pos hpos]
  gcongr
  exact_mod_cast h

/-- **Rank perturbation bound for Gram matrices.** The distribution functions of the spectral
measures of `X Xᴴ` and `Y Yᴴ` differ by at most `2 * rank (X - Y) / card m`. -/
theorem abs_spectralMeasure_mul_conjTranspose_self_Iic_sub_le_two_mul_rank_div_card [Nonempty m]
    (X Y : Matrix m n 𝕜) (t : ℝ) :
    |((X * Xᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self X) : Measure ℝ).real
          (Set.Iic t) -
        ((Y * Yᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self Y) : Measure ℝ).real
          (Set.Iic t)| ≤
      2 * ((X - Y).rank : ℝ) / Fintype.card m := by
  refine (IsHermitian.abs_spectralMeasure_Iic_sub_le_rank_div_card _ _ t).trans ?_
  gcongr
  exact_mod_cast rank_mul_conjTranspose_self_sub_mul_conjTranspose_self_le X Y

end Matrix
