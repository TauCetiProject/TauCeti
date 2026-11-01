/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import TauCeti.Analysis.Matrix.SpectralMeasure

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

* `Matrix.IsHermitian.spectralMeasure_real_Iic`: the distribution function of the spectral measure
  is the proportion of eigenvalues at most `t`;
* `Matrix.IsHermitian.abs_spectralMeasure_Iic_sub_le_rank_div_card`: the distribution functions of
  the spectral measures of Hermitian `A` and `B` differ by at most `rank (A - B) / card n`;
* `Matrix.rank_add_le`: the rank of a sum is at most the sum of the ranks;
* `Matrix.rank_mul_conjTranspose_sub_le`: `rank (X Xᴴ - Y Yᴴ) ≤ 2 * rank (X - Y)`;
* `Matrix.abs_spectralMeasure_mul_conjTranspose_Iic_sub_le`: the corresponding bound for the
  spectral measures of Gram matrices.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices* (2010),
  Theorem A.43.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ComplexOrder

namespace Matrix

variable {ι m n 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] [Fintype n]
  [RCLike 𝕜]

/-- The distribution function of the spectral measure at `t` is the proportion of eigenvalues at
most `t`, counted with multiplicity. -/
theorem IsHermitian.spectralMeasure_real_Iic [Nonempty ι] {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (t : ℝ) :
    (A.spectralMeasure hA : Measure ℝ).real (Set.Iic t) =
      (#{i | hA.eigenvalues₀ i ≤ t} : ℝ) / Fintype.card ι := by
  rw [Measure.real, spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀,
    TauCeti.Probability.empiricalMeasureOfFintype_apply measurableSet_Iic, Fintype.card_fin,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum
      (fun i _ => by by_cases h : hA.eigenvalues₀ i ∈ Set.Iic t <;> simp [h])]
  rw [div_eq_inv_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : hA.eigenvalues₀ i ≤ t <;> simp [h]

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

omit [Fintype m] [DecidableEq m] in
/-- The rank of a sum of matrices over a field is at most the sum of the ranks. -/
theorem rank_add_le (A B : Matrix m n 𝕜) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, mulVecLin_add]
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))
  rintro _ ⟨v, rfl⟩
  exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩

omit [DecidableEq m] in
/-- The rank of the difference of two Gram matrices is at most twice the rank of the difference
of the factors. -/
theorem rank_mul_conjTranspose_sub_le (X Y : Matrix m n 𝕜) :
    (X * Xᴴ - Y * Yᴴ).rank ≤ 2 * (X - Y).rank := by
  have h : X * Xᴴ - Y * Yᴴ = (X - Y) * Xᴴ + Y * (X - Y)ᴴ := by
    rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h, two_mul]
  refine (rank_add_le _ _).trans (add_le_add (rank_mul_le_left _ _) ?_)
  exact (rank_mul_le_right _ _).trans (rank_conjTranspose _).le

/-- **Rank perturbation bound for Gram matrices.** The distribution functions of the spectral
measures of `X Xᴴ` and `Y Yᴴ` differ by at most `2 * rank (X - Y) / card m`. -/
theorem abs_spectralMeasure_mul_conjTranspose_Iic_sub_le [Nonempty m] (X Y : Matrix m n 𝕜)
    (t : ℝ) :
    |((X * Xᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self X) : Measure ℝ).real
          (Set.Iic t) -
        ((Y * Yᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self Y) : Measure ℝ).real
          (Set.Iic t)| ≤
      2 * ((X - Y).rank : ℝ) / Fintype.card m := by
  refine (IsHermitian.abs_spectralMeasure_Iic_sub_le_rank_div_card _ _ t).trans ?_
  gcongr
  exact_mod_cast rank_mul_conjTranspose_sub_le X Y

end Matrix
