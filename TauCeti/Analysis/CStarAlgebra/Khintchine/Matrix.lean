/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Khintchine.Matrix.Gauge

import TauCeti.Analysis.CStarAlgebra.Khintchine.Dual
import TauCeti.Analysis.CStarAlgebra.Matrix.LinearMap
import TauCeti.Analysis.CStarAlgebra.Matrix.Trace.Duality
import TauCeti.Analysis.CStarAlgebra.RademacherSum
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# The `p = 1` noncommutative Khintchine inequality for matrices

For a finite family `a : ι → CStarMatrix m m ℂ`, `TauCeti.randomSumGauge` and
`TauCeti.rowColumnSumGauge` (defined in `TauCeti.Analysis.CStarAlgebra.Khintchine.Matrix.Gauge`)
measure the Rademacher `Lᵖ` sum norm and the infimal row/column `Lᵖ` sum norm.

At `p = 1`, Lust-Piquard and Pisier proved uniform equivalence of these norms, and Haagerup–Musat /
Pisier established the explicit universal lower constant `(√3)⁻¹` (with upper constant `1`). We
prove this by combining:
1. Rectangular Schatten realization of `columnSquare`/`rowSquare` and infimal convolution `⊓`
   (`rowColumnSumSeminorm`) from `TauCeti.Analysis.CStarAlgebra.Khintchine.Matrix.Gauge`.
2. Column/row trace-pairing duality from `TauCeti.Analysis.CStarAlgebra.Matrix.Schatten` lifted to
   `rowColumnSumGauge 1`.
3. `Seminorm.exists_dual_apply_eq_and_norm_le`, `CStarMatrix.existsUnique_sum_trace_mul_eq`, and
   `TauCeti.exists_rademacherCoeff_eq_and_norm_le` for `(√3)⁻¹`, plus sign-cube Bessel duality
   (`TauCeti.norm_rowSquare_rademacherCoeff_le`) for `1`.

## Main declarations

* `TauCeti.norm_sum_trace_mul_le_rowColumnSumGauge_one`,
  `TauCeti.exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one`
* `TauCeti.isGreatest_rowColumnSumGauge_one`, `TauCeti.rowColumnSumGauge_one_eq_sSup`,
  `TauCeti.sum_trace_rademacherCoeff_mul`, `TauCeti.isGreatest_randomSumGauge_one`,
  `TauCeti.randomSumGauge_one_eq_sSup`
* `TauCeti.randomSumGauge_one_le_matrixLpGauge_columnSquare`,
  `TauCeti.randomSumGauge_one_le_matrixLpGauge_rowSquare`
* `TauCeti.matrix_khintchine_one`

## References

* F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
  Ark. Mat. 29 (1991), 241–260.
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), 588–624, Theorem 2.11.
* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  Theorem 9.1.
-/

public section

noncomputable section

open scoped BigOperators ComplexOrder ComplexStarModule InnerProductSpace NNReal ENNReal

namespace TauCeti

/-! ### Trace-pairing duality for `rowColumnSumGauge 1` -/

section TraceDuality

variable {ι m : Type*} [Fintype ι] [Fintype m]

/-- **Row/column trace-pairing bound**: if `‖columnSquare x‖ ≤ 1` and `‖rowSquare x‖ ≤ 1`, then
`‖∑ k, tr(x k * a k)‖ ≤ rowColumnSumGauge 1 a`. -/
theorem norm_sum_trace_mul_le_rowColumnSumGauge_one {x a : ι → CStarMatrix m m ℂ}
    (hx_col : ‖columnSquare x‖ ≤ 1) (hx_row : ‖rowSquare x‖ ≤ 1) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k))‖ ≤ rowColumnSumGauge 1 a :=
  le_rowColumnSumGauge fun b c hbc => by
    have hadd : ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k)) =
        (∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))) +
          ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * c k)) := by
      simp only [hbc, Pi.add_apply, mul_add, ← CStarMatrix.traceLinearMap_apply (R := ℂ),
        map_add, Finset.sum_add_distrib]
    rw [hadd]
    exact (norm_add_le _ _).trans <| add_le_add
      ((norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare x b).trans
        (mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _) hx_row))
      ((norm_sum_trace_mul_le_norm_columnSquare_mul_matrixLpGauge_one_rowSquare x c).trans
        (mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _) hx_col))

/-- **Row/column duality attainment**: there exists `x : ι → CStarMatrix m m ℂ` in the
row/column unit ball (`‖columnSquare x‖ ≤ 1` and `‖rowSquare x‖ ≤ 1`) attaining
`∑ k, tr(x k * a k) = rowColumnSumGauge 1 a`. -/
theorem exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one
    (a : ι → CStarMatrix m m ℂ) :
    ∃ x : ι → CStarMatrix m m ℂ,
      ‖columnSquare x‖ ≤ 1 ∧ ‖rowSquare x‖ ≤ 1 ∧
        ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k)) =
          (rowColumnSumGauge 1 a : ℂ) := by
  obtain ⟨φ, hφ_a, hφ_le⟩ := (rowColumnSumSeminorm ι m 1 le_rfl).exists_dual_apply_eq_and_norm_le a
  simp only [rowColumnSumSeminorm_apply, RCLike.ofReal_eq_complex_ofReal] at hφ_a hφ_le
  obtain ⟨x, hφ_tr⟩ := (CStarMatrix.existsUnique_sum_trace_mul_eq φ).exists
  have hx_row : ‖rowSquare x‖ ≤ 1 := norm_rowSquare_le_of_forall_norm_sum_trace_mul_le zero_le_one
    fun b => by
      rw [one_mul, ← hφ_tr b]
      exact (hφ_le b).trans (rowColumnSumGauge_le_matrixLpGauge_columnSquare zero_lt_one b)
  have hx_col : ‖columnSquare x‖ ≤ 1 := norm_columnSquare_le_of_forall_norm_sum_trace_mul_le
    zero_le_one fun c => by
      rw [one_mul, ← hφ_tr c]
      exact (hφ_le c).trans (rowColumnSumGauge_le_matrixLpGauge_rowSquare zero_lt_one c)
  exact ⟨x, hx_col, hx_row, by rw [← hφ_tr a, hφ_a]⟩

/-- **Matrix duality for `rowColumnSumGauge 1` (attained maximum)**: `rowColumnSumGauge 1 a` is
the greatest value of `‖∑ k, tr(x k * a k)‖` over the row/column unit ball
(`‖columnSquare x‖ ≤ 1` and `‖rowSquare x‖ ≤ 1`). -/
theorem isGreatest_rowColumnSumGauge_one (a : ι → CStarMatrix m m ℂ) :
    IsGreatest {r : ℝ | ∃ x : ι → CStarMatrix m m ℂ,
      ‖columnSquare x‖ ≤ 1 ∧ ‖rowSquare x‖ ≤ 1 ∧
        r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k))‖}
      (rowColumnSumGauge 1 a) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx_col, hx_row, htr⟩ :=
      exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one a
    exact ⟨x, hx_col, hx_row, by
      rw [htr, Complex.norm_real, Real.norm_of_nonneg (rowColumnSumGauge_nonneg 1 a)]⟩
  · rintro r ⟨x, hx_col, hx_row, rfl⟩
    exact norm_sum_trace_mul_le_rowColumnSumGauge_one hx_col hx_row

/-- **Matrix duality for `rowColumnSumGauge 1`**: `rowColumnSumGauge 1 a` equals the supremum of
`‖∑ k, tr(x k * a k)‖` over the row/column unit ball (`‖columnSquare x‖ ≤ 1`,
`‖rowSquare x‖ ≤ 1`). -/
theorem rowColumnSumGauge_one_eq_sSup (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge 1 a = sSup {r : ℝ | ∃ x : ι → CStarMatrix m m ℂ,
      ‖columnSquare x‖ ≤ 1 ∧ ‖rowSquare x‖ ≤ 1 ∧
        r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * a k))‖} :=
  (isGreatest_rowColumnSumGauge_one a).csSup_eq.symm

end TraceDuality

/-! ### Sign-cube duality and the `p = 1` Khintchine inequality -/

section KhintchineOne

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]

/-- **Fourier-coefficient trace pairing**: the trace pairing of `rademacherCoeff ℝ Φ` with `a`
equals the expectation over `ε : ι → ℤˣ` of `tr(Φ ε * ∑ k, ε k • a k)`. -/
theorem sum_trace_rademacherCoeff_mul
    (Φ : (ι → ℤˣ) → CStarMatrix m m ℂ) (a : ι → CStarMatrix m m ℂ) :
    ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k)) =
      𝔼 ε : ι → ℤˣ, Matrix.trace (CStarMatrix.ofMatrix.symm (Φ ε * ∑ k, ε k • a k)) := by
  simpa only [LinearMap.compr₂_apply, LinearMap.mul_apply', CStarMatrix.traceLinearMap_apply] using
    sum_bilinear_rademacherCoeff_eq_expect
      ((LinearMap.mul ℝ (CStarMatrix m m ℂ)).compr₂ (CStarMatrix.traceLinearMap m ℝ ℂ)) Φ a

/-- **Sign-cube trace-pairing bound**: if `∀ ε, ‖Φ ε‖ ≤ C`, then the Fourier-coefficient pairing
of `Φ` with `a` satisfies
`‖∑ k, tr(rademacherCoeff ℝ Φ k * a k)‖ ≤ C * randomSumGauge 1 a`. -/
theorem norm_sum_trace_rademacherCoeff_mul_le
    {Φ : (ι → ℤˣ) → CStarMatrix m m ℂ} {C : ℝ} (hΦ : ∀ ε, ‖Φ ε‖ ≤ C)
    (a : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k))‖ ≤
      C * randomSumGauge 1 a := by
  rw [sum_trace_rademacherCoeff_mul, randomSumGauge_one_eq_expect_units, Finset.mul_expect]
  refine (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le_expect fun ε _ => ?_)
  exact (norm_trace_mul_le_norm_mul_matrixLpGauge_one _ _).trans
    (mul_le_mul_of_nonneg_right (hΦ ε) (matrixLpGauge_nonneg 1 _))

/-- **Sign-cube duality attainment**: there exists a pointwise contraction
`Φ : (ι → ℤˣ) → CStarMatrix m m ℂ` (`∀ ε, ‖Φ ε‖ ≤ 1`) whose Fourier coefficients attain
`∑ k, tr(rademacherCoeff ℝ Φ k * a k) = randomSumGauge 1 a`. -/
theorem exists_norm_le_one_and_sum_trace_rademacherCoeff_mul_eq_randomSumGauge_one
    (a : ι → CStarMatrix m m ℂ) :
    ∃ Φ : (ι → ℤˣ) → CStarMatrix m m ℂ, (∀ ε, ‖Φ ε‖ ≤ 1) ∧
      ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k)) =
        (randomSumGauge 1 a : ℂ) := by
  choose Φ hΦ_norm hΦ_tr using fun ε : ι → ℤˣ =>
    exists_norm_le_one_and_trace_mul_eq_matrixLpGauge_one (∑ k, ε k • a k)
  refine ⟨Φ, hΦ_norm, ?_⟩
  rw [sum_trace_rademacherCoeff_mul, randomSumGauge_one_eq_expect_units, Complex.ofReal_expect]
  exact Finset.expect_congr rfl fun ε _ => hΦ_tr ε

/-- **Matrix duality for `randomSumGauge 1` (attained maximum)**: `randomSumGauge 1 a` is the
greatest value of `‖∑ k, tr(rademacherCoeff ℝ Φ k * a k)‖` over pointwise contractions
`Φ : (ι → ℤˣ) → CStarMatrix m m ℂ` (`∀ ε, ‖Φ ε‖ ≤ 1`). -/
theorem isGreatest_randomSumGauge_one (a : ι → CStarMatrix m m ℂ) :
    IsGreatest {r : ℝ | ∃ Φ : (ι → ℤˣ) → CStarMatrix m m ℂ, (∀ ε, ‖Φ ε‖ ≤ 1) ∧
      r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k))‖}
      (randomSumGauge 1 a) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, hΦ_norm, htr⟩ :=
      exists_norm_le_one_and_sum_trace_rademacherCoeff_mul_eq_randomSumGauge_one a
    exact ⟨Φ, hΦ_norm, by
      rw [htr, Complex.norm_real, Real.norm_of_nonneg (randomSumGauge_nonneg 1 a)]⟩
  · rintro r ⟨Φ, hΦ_norm, rfl⟩
    simpa only [one_mul] using norm_sum_trace_rademacherCoeff_mul_le hΦ_norm a

/-- **Matrix duality for `randomSumGauge 1`**: `randomSumGauge 1 a` equals the supremum of
`‖∑ k, tr(rademacherCoeff ℝ Φ k * a k)‖` over sign-cube Fourier coefficients of pointwise
contractions `Φ : (ι → ℤˣ) → CStarMatrix m m ℂ` (`∀ ε, ‖Φ ε‖ ≤ 1`). -/
theorem randomSumGauge_one_eq_sSup (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a = sSup {r : ℝ | ∃ Φ : (ι → ℤˣ) → CStarMatrix m m ℂ,
      (∀ ε, ‖Φ ε‖ ≤ 1) ∧
        r = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (rademacherCoeff ℝ Φ k * a k))‖} :=
  (isGreatest_randomSumGauge_one a).csSup_eq.symm

/-- Column upper bound at `p = 1`: `randomSumGauge 1 b ≤ matrixLpGauge 1 (columnSquare b)`. -/
theorem randomSumGauge_one_le_matrixLpGauge_columnSquare (b : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 b ≤ matrixLpGauge 1 (columnSquare b) := by
  obtain ⟨Φ, hΦ_norm, hexp⟩ :=
    exists_norm_le_one_and_sum_trace_rademacherCoeff_mul_eq_randomSumGauge_one b
  rw [← Real.norm_of_nonneg (randomSumGauge_nonneg 1 b), ← Complex.norm_real, ← hexp]
  exact (norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare
    (rademacherCoeff ℝ Φ) b).trans <|
    mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _) (norm_rowSquare_rademacherCoeff_le hΦ_norm)

/-- Row upper bound at `p = 1`: `randomSumGauge 1 c ≤ matrixLpGauge 1 (rowSquare c)`. -/
theorem randomSumGauge_one_le_matrixLpGauge_rowSquare (c : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 c ≤ matrixLpGauge 1 (rowSquare c) := by
  rw [← randomSumGauge_star 1 c, rowSquare_eq_columnSquare_star]
  exact randomSumGauge_one_le_matrixLpGauge_columnSquare (fun k => star (c k))

/-- Upper bound in the `p = 1` noncommutative Khintchine inequality:
`randomSumGauge 1 a ≤ rowColumnSumGauge 1 a`. -/
theorem randomSumGauge_one_le_rowColumnSumGauge (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a ≤ rowColumnSumGauge 1 a :=
  le_rowColumnSumGauge fun b c h => h ▸ (randomSumGauge_add_le le_rfl b c).trans
    (add_le_add (randomSumGauge_one_le_matrixLpGauge_columnSquare b)
      (randomSumGauge_one_le_matrixLpGauge_rowSquare c))

/-- Lower bound in the `p = 1` noncommutative Khintchine inequality:
`(Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a`. -/
theorem inv_sqrt_three_mul_rowColumnSumGauge_le_randomSumGauge_one (a : ι → CStarMatrix m m ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a := by
  obtain ⟨x, hx_col, hx_row, htr⟩ :=
    exists_norm_square_le_one_and_sum_trace_mul_eq_rowColumnSumGauge_one a
  obtain ⟨Φ, hΦ_avg, hΦ_norm⟩ := exists_rademacherCoeff_eq_and_norm_le x
  have hΦ_le (ε : ι → ℤˣ) : ‖Φ ε‖ ≤ Real.sqrt 3 :=
    (hΦ_norm ε).trans <| mul_le_of_le_one_right (Real.sqrt_nonneg 3) (max_le hx_col hx_row)
  have hbound := norm_sum_trace_rademacherCoeff_mul_le hΦ_le a
  -- Re-elaborate `hΦ_avg` with the concrete `CStarMatrix` `Module ℝ` instance
  -- (rather than `NonUnitalCStarAlgebra`'s `complexToReal` instance) so `rw` matches syntactically.
  have hΦ_eq : rademacherCoeff ℝ Φ = x := hΦ_avg
  rw [hΦ_eq, htr, Complex.norm_real, Real.norm_of_nonneg (rowColumnSumGauge_nonneg 1 a)] at hbound
  exact (inv_mul_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hbound

/-- **The `p = 1` noncommutative Khintchine inequality for matrices** (Lust-Piquard–Pisier,
Haagerup–Musat, Pisier): for any finite index types `ι` and `m` and any family
`a : ι → CStarMatrix m m ℂ`,
`(√3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ≤ rowColumnSumGauge 1 a`. -/
theorem matrix_khintchine_one (a : ι → CStarMatrix m m ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ∧
      randomSumGauge 1 a ≤ rowColumnSumGauge 1 a :=
  ⟨inv_sqrt_three_mul_rowColumnSumGauge_le_randomSumGauge_one a,
    randomSumGauge_one_le_rowColumnSumGauge a⟩

end KhintchineOne

end TauCeti
