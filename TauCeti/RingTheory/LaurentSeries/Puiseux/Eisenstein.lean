/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation
public import TauCeti.RingTheory.PowerSeries.Eisenstein
import TauCeti.RingTheory.LaurentSeries.RatFunc
import TauCeti.RingTheory.PowerSeries.SqrtOneAddFour

/-!
# Eisenstein denominators for algebraic Puiseux series

Let `K` be an algebraic extension of `ℚ` in characteristic zero, and let `x ∈ puiseuxField K`
be a Puiseux series that is algebraic over the rational function field `K(X)`. Any Puiseux series
lies in some ramified level `K⸨t ^ (1 / N)⸩`, i.e., `x = levelEmbedding K N g` for some `N : ℕ+`
and `g ∈ K⸨X⸩`. Pulling back rational functions along `X ↦ X ^ N` shows that `g` is itself
algebraic over `K(X)` (`TauCeti.puiseuxField.isAlgebraic_of_levelEmbedding`).

When `x` has nonnegative rational order (`0 ≤ addVal K x`, equivalently `x` is integral over
`K⟦X⟧`), the Laurent series `g` is a power series `f ∈ K⟦X⟧` algebraic over `K(X)`.
Applying Eisenstein's theorem for power series (`TauCeti.RingTheory.PowerSeries.Eisenstein`) to `f`
yields positive rational integers `c` and `M` such that `(c : K) * (M : K)ⁿ * x_{n / N}` is an
algebraic integer for all `n ≥ 0`, with `c = 1` when the constant term `x₀` is integral over `ℤ`
(and in particular for `x - x₀`). Moreover, for every algebraic Puiseux series `x` (without
assuming nonnegative valuation), all coefficients of `x` lie in a single intermediate number field
of `K`.

## Main results

* `TauCeti.puiseuxField.isAlgebraic_of_levelEmbedding`: if `levelEmbedding K N g` is algebraic
  over `K(X)`, then `g ∈ K⸨X⸩` is algebraic over `K(X)`.
* `TauCeti.puiseuxField.exists_levelEmbedding_powerSeries_isAlgebraic`: if `x` has nonnegative
  additive valuation and is algebraic over `K(X)`, then `x = levelEmbedding K N (f : K⸨X⸩)` for
  some `N : ℕ+` and some algebraic power series `f ∈ K⟦X⟧`.
* `TauCeti.puiseuxField.exists_finiteDimensional_intermediateField_of_isAlgebraic` and
  `TauCeti.puiseuxField.exists_numberField_of_isAlgebraic`: all coefficients of an algebraic
  Puiseux series lie in a single finite-dimensional intermediate field (and hence in an intermediate
  `NumberField` over `ℚ`).
* `TauCeti.puiseuxField.exists_pos_nat_sub_C_mem_scaledIntegralSeries`,
  `TauCeti.puiseuxField.exists_pos_nat_smul_mem_scaledIntegralSeries`,
  `TauCeti.puiseuxField.exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral`,
  `TauCeti.puiseuxField.exists_pos_nat_mul_isIntegral_coeff`, and
  `TauCeti.puiseuxField.exists_pos_nat_smul_mem_scaledIntegralSeries_rat`: Eisenstein denominator
  bounds for algebraic Puiseux series of nonnegative order.

## References

* Yu. Bilu and M. Borichev, *Remarks on Eisenstein*, J. Aust. Math. Soc. **94** (2013), 158–180
  (`arXiv:1112.2290v2`), §1 and Theorem 6.1.
-/

public section

open HahnSeries LaurentSeries PowerSeries
open scoped LaurentSeries Polynomial PowerSeries RatFunc

namespace TauCeti.puiseuxField

section Pullback

variable {K : Type*} [Field K]

/-- If `levelEmbedding K N f` is algebraic over `K(X)` in the Puiseux field, then `f ∈ K⸨X⸩` is
algebraic over `K(X)`. -/
theorem isAlgebraic_of_levelEmbedding {N : ℕ+} {f : K⸨X⸩}
    (hf : IsAlgebraic K⟮X⟯ (levelEmbedding K N f)) : IsAlgebraic K⟮X⟯ f := by
  obtain ⟨P, hP_ne, hP_eval⟩ := hf
  refine ⟨P.map (RatFunc.expand K N), Polynomial.map_ne_zero hP_ne, ?_⟩
  apply (levelEmbedding K N).toRingHom.injective
  rw [map_zero, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  have hcomp :
      (levelEmbedding K N).toRingHom.comp
          ((algebraMap K⟮X⟯ K⸨X⸩).comp (RatFunc.expand K N)) =
        algebraMap K⟮X⟯ (puiseuxField K) :=
    RingHom.ext fun r ↦ by
      simp [← LaurentSeries.expand_algebraMap_ratFunc, algebraMap_ratFunc_apply]
  rw [hcomp]
  simpa [Polynomial.aeval_def] using hP_eval

/-- If `x ∈ puiseuxField K` has nonnegative additive valuation and is algebraic over `K(X)`, then
`x = levelEmbedding K N (f : K⸨X⸩)` for some `N : ℕ+` and some power series `f ∈ K⟦X⟧` algebraic
over `K(X)`. -/
theorem exists_levelEmbedding_powerSeries_isAlgebraic {x : puiseuxField K} (hx : 0 ≤ addVal K x)
    (halg : IsAlgebraic K⟮X⟯ x) :
    ∃ (N : ℕ+) (f : K⟦X⟧), x = levelEmbedding K N (f : K⸨X⸩) ∧ IsAlgebraic K⟮X⟯ (f : K⸨X⸩) := by
  obtain ⟨N, f, rfl⟩ := exists_levelEmbedding_powerSeries_of_addVal_nonneg hx
  exact ⟨N, f, rfl, isAlgebraic_of_levelEmbedding halg⟩

end Pullback

section Eisenstein

/-- If `K / F` is an algebraic extension in characteristic zero and `x ∈ puiseuxField K` is
algebraic over `K(X)`, then all coefficients of `x` lie in a single finite-dimensional intermediate
field of `K / F`. -/
theorem exists_finiteDimensional_intermediateField_of_isAlgebraic {F K : Type*} [Field F]
    [Field K] [CharZero K] [Algebra F K] [Algebra.IsAlgebraic F K] (x : puiseuxField K)
    (halg : IsAlgebraic K⟮X⟯ x) :
    ∃ E : IntermediateField F K, FiniteDimensional F E ∧
      ∀ q : ℚ, (x : HahnSeries ℚ K).coeff q ∈ E := by
  obtain ⟨N, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hn
  have hfa : IsAlgebraic K⟮X⟯ (g.powerSeriesPart : K⸨X⸩) :=
    LaurentSeries.isAlgebraic_powerSeriesPart (isAlgebraic_of_levelEmbedding halg)
  obtain ⟨E, hfd, hmem⟩ :=
    PowerSeries.exists_finiteDimensional_intermediateField_of_isAlgebraic
      (F := F) g.powerSeriesPart hfa
  refine ⟨E, hfd, fun q ↦ ?_⟩
  by_cases hq : q.den ∣ N
  · obtain ⟨m, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div N.ne_zero).mp hq
    rw [coe_levelEmbedding, coeff_ramifiedEmbedding_intCast_div]
    have hcm : g.coeff m = (g.powerSeriesPart : K⸨X⸩).coeff (-g.order + m) := by
      rw [LaurentSeries.ofPowerSeries_powerSeriesPart g, coeff_single_mul, one_mul,
        add_sub_cancel_left]
    rw [hcm, PowerSeries.coeff_coe]
    split_ifs with hlt
    · exact E.zero_mem
    · simpa using hmem (-g.order + m).natAbs
  · rw [coe_levelEmbedding, coeff_ramifiedEmbedding_of_not_den_dvd N g hq]
    exact E.zero_mem

/-- If `K / ℚ` is an algebraic extension and `x ∈ puiseuxField K` is algebraic over `K(X)`,
then all coefficients of `x` lie in a single intermediate number field of `K`. -/
theorem exists_numberField_of_isAlgebraic {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] (x : puiseuxField K) (halg : IsAlgebraic K⟮X⟯ x) :
    ∃ (E : IntermediateField ℚ K) (_ : NumberField E),
      ∀ q : ℚ, (x : HahnSeries ℚ K).coeff q ∈ E := by
  obtain ⟨E, hfd, hmem⟩ :=
    exists_finiteDimensional_intermediateField_of_isAlgebraic (F := ℚ) x halg
  have : FiniteDimensional ℚ E := hfd
  exact ⟨E, ⟨⟩, hmem⟩

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- **Eisenstein's theorem for nonnegative Puiseux series (nonconstant part).** If `K / ℚ` is an
algebraic extension and `x ∈ puiseuxField K` of nonnegative rational order is algebraic over
`K(X)`, then `x = levelEmbedding K N (f : K⸨X⸩)` for some `N : ℕ+` and `f ∈ K⟦X⟧` with
`f - C (constantCoeff f) ∈ scaledIntegralSeries (integralClosure ℤ K) M` for some `M > 0`. -/
theorem exists_pos_nat_sub_C_mem_scaledIntegralSeries {x : puiseuxField K}
    (hx : 0 ≤ addVal K x) (halg : IsAlgebraic K⟮X⟯ x) :
    ∃ (N : ℕ+) (M : ℕ) (f : K⟦X⟧), 0 < M ∧ x = levelEmbedding K N (f : K⸨X⸩) ∧
      f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
        TauCeti.scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨N, f, rfl, hf⟩ := exists_levelEmbedding_powerSeries_isAlgebraic hx halg
  obtain ⟨M, hM, hmem⟩ := TauCeti.exists_pos_nat_sub_C_mem_scaledIntegralSeries hf
  exact ⟨N, M, f, hM, rfl, hmem⟩

/-- **Eisenstein's theorem for nonnegative Puiseux series.** If `K / ℚ` is an algebraic
extension and `x ∈ puiseuxField K` of nonnegative rational order is algebraic over `K(X)`, then
`x = levelEmbedding K N (f : K⸨X⸩)` for some `N : ℕ+` and `f ∈ K⟦X⟧` with
`(c : K) • f ∈ scaledIntegralSeries (integralClosure ℤ K) M` for some positive integers `c, M`. -/
theorem exists_pos_nat_smul_mem_scaledIntegralSeries {x : puiseuxField K}
    (hx : 0 ≤ addVal K x) (halg : IsAlgebraic K⟮X⟯ x) :
    ∃ (N : ℕ+) (c M : ℕ) (f : K⟦X⟧), 0 < c ∧ 0 < M ∧ x = levelEmbedding K N (f : K⸨X⸩) ∧
      (c : K) • f ∈ TauCeti.scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨N, f, rfl, hf⟩ := exists_levelEmbedding_powerSeries_isAlgebraic hx halg
  obtain ⟨c, M, hc, hM, hmem⟩ := TauCeti.exists_pos_nat_smul_mem_scaledIntegralSeries hf
  exact ⟨N, c, M, f, hc, hM, rfl, hmem⟩

/-- **Eisenstein's theorem for nonnegative Puiseux series (integral constant term).** If `K / ℚ` is
algebraic, `x ∈ puiseuxField K` has `0 ≤ addVal K x`, `x` is algebraic over `K(X)`, and its
constant coefficient `(x : HahnSeries ℚ K).coeff 0` is integral over `ℤ`, then
`x = levelEmbedding K N (f : K⸨X⸩)` for some `N : ℕ+` and `f ∈ scaledIntegralSeries
(integralClosure ℤ K) M` with `M > 0`. -/
theorem exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral {x : puiseuxField K}
    (hx : 0 ≤ addVal K x) (halg : IsAlgebraic K⟮X⟯ x)
    (hx₀ : IsIntegral ℤ ((x : HahnSeries ℚ K).coeff 0)) :
    ∃ (N : ℕ+) (M : ℕ) (f : K⟦X⟧), 0 < M ∧ x = levelEmbedding K N (f : K⸨X⸩) ∧
      f ∈ TauCeti.scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨N, f, rfl, hf⟩ := exists_levelEmbedding_powerSeries_isAlgebraic hx halg
  have hf₀ : IsIntegral ℤ (PowerSeries.constantCoeff f) := by
    have hc0 : ((levelEmbedding K N (f : K⸨X⸩) : puiseuxField K) : HahnSeries ℚ K).coeff 0 =
        PowerSeries.constantCoeff f := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simpa using coeff_levelEmbedding_coe_natCast_div N f 0
    exact hc0 ▸ hx₀
  obtain ⟨M, hM, hmem⟩ := TauCeti.exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral hf hf₀
  exact ⟨N, M, f, hM, rfl, hmem⟩

/-- **Coefficientwise Eisenstein bound for nonnegative Puiseux series.** Every exponent in the
support of `x` is of the form `n / N` (`n : ℕ`), and `(c : K) * (M : K)ⁿ * x_{n / N}` is integral
over `ℤ` for all `n : ℕ`. -/
theorem exists_pos_nat_mul_isIntegral_coeff {x : puiseuxField K} (hx : 0 ≤ addVal K x)
    (halg : IsAlgebraic K⟮X⟯ x) :
    ∃ (N : ℕ+) (c M : ℕ), 0 < c ∧ 0 < M ∧
      (∀ q ∈ (x : HahnSeries ℚ K).support, ∃ n : ℕ, q = (n : ℚ) / N) ∧
      ∀ n : ℕ, IsIntegral ℤ ((c : K) * (M : K) ^ n * (x : HahnSeries ℚ K).coeff ((n : ℚ) / N)) := by
  obtain ⟨N, c, M, f, hc, hM, rfl, hmem⟩ := exists_pos_nat_smul_mem_scaledIntegralSeries hx halg
  refine ⟨N, c, M, hc, hM, fun q hq ↦ ?_, fun n ↦ ?_⟩
  · rw [coe_levelEmbedding, support_ramifiedEmbedding] at hq
    obtain ⟨k, hk_supp, rfl⟩ := hq
    have hk0 : 0 ≤ k := by
      by_contra hlt
      exact hk_supp (by simp [PowerSeries.coeff_coe, not_le.mp hlt])
    lift k to ℕ using hk0 with n
    exact ⟨n, by simp⟩
  · have hint := TauCeti.mem_scaledIntegralSeries_integralClosure_iff.mp hmem n
    rw [PowerSeries.coeff_smul, smul_eq_mul, ← mul_assoc, mul_comm ((M : K) ^ n) (c : K)] at hint
    rwa [coeff_levelEmbedding_coe_natCast_div]

/-- Specialization of `TauCeti.puiseuxField.exists_pos_nat_smul_mem_scaledIntegralSeries` to
rational Puiseux series: if `x ∈ puiseuxField ℚ` has `0 ≤ addVal ℚ x` and is algebraic over `ℚ(X)`,
then `x = levelEmbedding ℚ N (f : ℚ⸨X⸩)` for some `N : ℕ+` and `(c : ℚ) • f ∈ scaledIntegralSeries
ℤ M` with `c, M > 0`. -/
theorem exists_pos_nat_smul_mem_scaledIntegralSeries_rat {x : puiseuxField ℚ}
    (hx : 0 ≤ addVal ℚ x) (halg : IsAlgebraic ℚ⟮X⟯ x) :
    ∃ (N : ℕ+) (c M : ℕ) (f : ℚ⟦X⟧), 0 < c ∧ 0 < M ∧ x = levelEmbedding ℚ N (f : ℚ⸨X⸩) ∧
      (c : ℚ) • f ∈ TauCeti.scaledIntegralSeries ℤ (M : ℚ) := by
  obtain ⟨N, f, rfl, hf⟩ := exists_levelEmbedding_powerSeries_isAlgebraic hx halg
  obtain ⟨c, M, hc, hM, hmem⟩ := TauCeti.exists_pos_nat_smul_mem_scaledIntegralSeries_rat hf
  exact ⟨N, c, M, f, hc, hM, rfl, hmem⟩

end Eisenstein

/-! ### Example -/

section Example

/-- The ramified Catalan Puiseux series `√(1 + 4 t^(1/2)) = 1 + 2 ∑ (-1)ⁿ Cₙ t^((n+1)/2)` lies in
level `2` (and not level `1`), has nonnegative rational order, is algebraic over `K(X)` via
`(y² - 1)² - 16 t = 0`, and has all integer coefficients (`c = 1`, `M = 1`). -/
example {K : Type*} [Field K] [CharZero K] :
    let f : K⟦X⟧ := sqrtOneAddFour.map (Int.castRingHom K)
    let y : puiseuxField K := levelEmbedding K 2 (f : K⸨X⸩)
    0 ≤ addVal K y ∧ IsAlgebraic K⟮X⟯ y ∧ y ∉ (levelEmbedding K 1).range ∧
      f ∈ TauCeti.scaledIntegralSeries (integralClosure ℤ K) (1 : K) := by
  intro f y
  have h0 : 0 ≤ addVal K y := by
    have hf_ord : (0 : WithTop ℤ) ≤ (f : K⸨X⸩).orderTop := by
      rw [PowerSeries.orderTop_coe]
      cases f.order with
      | top => simp
      | coe n => exact WithTop.coe_le_coe.mpr (Nat.cast_nonneg n)
    simpa [y] using (div_le_addVal_levelEmbedding_iff 2 (f : K⸨X⸩) 0).mpr hf_ord
  have hsq : f ^ 2 = 1 + 4 * PowerSeries.X := by
    rw [← map_pow, sqrtOneAddFour_sq, map_add, map_one, map_mul, map_X]; simp [map_ofNat]
  have hy_sq : y ^ 2 - 1 = 4 * levelEmbedding K 2 (HahnSeries.single 1 1) := by
    have hy2 : y ^ 2 = levelEmbedding K 2 ((1 + 4 * PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
      rw [← hsq, PowerSeries.coe_pow]; simp [y, map_pow]
    rw [hy2, PowerSeries.coe_add, PowerSeries.coe_one, PowerSeries.coe_mul, PowerSeries.coe_X,
      map_add, map_one, map_mul]
    simp only [map_ofNat]; ring
  have halg : IsAlgebraic K⟮X⟯ y := by
    let P : K⟮X⟯[X] := (Polynomial.X ^ 2 - 1) ^ 2 - Polynomial.C (16 * RatFunc.X)
    refine ⟨P, Polynomial.ne_zero_of_natDegree_gt (n := 0) ?_, ?_⟩
    · have hdeg2 : ((Polynomial.X ^ 2 - 1 : K⟮X⟯[X]) ^ 2).natDegree = 4 := by
        rw [← Polynomial.C_1, (Polynomial.monic_X_pow_sub_C 1 (by decide)).natDegree_pow,
          Polynomial.natDegree_X_pow_sub_C]
      dsimp [P]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
        (by rw [hdeg2, Polynomial.natDegree_C]; decide), hdeg2]
      decide
    · have hu2 : (levelEmbedding K 2 (HahnSeries.single 1 1)) ^ 2 =
          algebraMap K⟮X⟯ (puiseuxField K) RatFunc.X := by
        rw [← map_pow, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
        simpa using (levelEmbedding_single_self (K := K) 2).trans algebraMap_ratFunc_X.symm
      have h4 : (y ^ 2 - 1) ^ 2 = 16 * algebraMap K⟮X⟯ (puiseuxField K) RatFunc.X := by
        rw [hy_sq, mul_pow, hu2]; ring
      simp [P, h4, map_ofNat]
  have hnot1 : y ∉ (levelEmbedding K 1).range := by
    rintro ⟨g, hg⟩
    have hc := congrArg (fun z : puiseuxField K ↦ (z : HahnSeries ℚ K).coeff (1 / 2 : ℚ)) hg
    have hdiv := coeff_levelEmbedding_coe_natCast_div 2 f 1
    rw [show ((1 : ℕ) : ℚ) / ((2 : ℕ+) : ℚ) = 1 / 2 by norm_num] at hdiv
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_levelEmbedding] at hc
    rw [coeff_ramifiedEmbedding_of_not_den_dvd 1 g (by norm_num)] at hc
    dsimp [y] at hc
    rw [hdiv] at hc
    simp [f] at hc
  refine ⟨h0, halg, hnot1, TauCeti.mem_scaledIntegralSeries_integralClosure_iff.mpr fun n ↦ ?_⟩
  simp [f, isIntegral_intCast]

end Example

end TauCeti.puiseuxField
