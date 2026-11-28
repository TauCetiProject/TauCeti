/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.PowerSeries.ScaledIntegral
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.RingTheory.Algebraic.Denominator
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.PowerSeries.Basic
import TauCeti.RingTheory.PowerSeries.SqrtOneAddFour
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Eisenstein denominators for algebraic power series

Let `K` be an algebraic extension of `ℚ` in characteristic zero, and let `f = ∑ aₙ Xⁿ ∈ K⟦X⟧`
be algebraic over the rational function field `K(X)`. **Eisenstein's theorem** states that there
exist positive rational integers `c` and `M` such that `c * Mⁿ * aₙ` is an algebraic integer for
every `n ≥ 0`, and that all coefficients `aₙ` lie in a single number field. Moreover, subtracting
the constant term already lies in the integral lattice at some positive scale `M`, so if `a₀` is
an algebraic integer then `f` itself lies in `TauCeti.scaledIntegralSeries (integralClosure ℤ K) M`.
Over `ℚ`, integrality over `ℤ` means integer values, so `c • f` (respectively `f` when `a₀ ∈ ℤ`)
lies in `TauCeti.scaledIntegralSeries ℤ M`.

The proof follows the elementary tail-series argument of Bilu and Borichev. Clearing rational
denominators of the minimal polynomial of `f` over `K(X)` gives a bivariate polynomial `P ∈ K[X][Y]`
with `P(f) = 0` and `P_Y(f) ≠ 0`, since `K(X)` has characteristic zero and `minpoly K(X) f` is
separable. Writing `s` for the `X`-adic order of `P_Y(f)`, setting `N = s + 1`, and decomposing
`f = b + X ^ N * (g₀ + u)` where `b` is the truncation below `N` and `u` has zero constant term,
Taylor expansion of `P` around `b` divided by `X ^ (N + s)` isolates a linear constant term in `X`
with nonzero scalar coefficient and yields `u = X * R(X, u)` for a polynomial `R ∈ K[X][Y]`.
Since the recurrence expresses each coefficient of `u` as a polynomial in earlier coefficients and
the finitely many coefficients of `R`, it preserves any subring of `K` containing the coefficients
of `R`. Taking the subring to be a finite extension containing the coefficients of `b`, `g₀`, and
`R` places every coefficient of `f` in a finite-dimensional intermediate field; rescaling by a
positive integer `M` clearing the coefficients of `R`, the nonconstant coefficients of `b`, and
`g₀` places `Mⁿ aₙ` in `integralClosure ℤ K` for all `n ≥ 1`.

## Main results

* `PowerSeries.exists_aeval_eq_zero_aeval_derivative_ne_zero_of_isAlgebraic`: clearing
  denominators of the minimal polynomial yields `P ∈ K[X][Y]` with `P(f) = 0` and `P_Y(f) ≠ 0`.
* `PowerSeries.exists_finiteDimensional_intermediateField_of_isAlgebraic`: all coefficients of an
  algebraic series over `K(X)` lie in a common finite-dimensional intermediate field of `K / F` when
  `K / F` is algebraic in characteristic zero.
* `PowerSeries.exists_numberField_of_isAlgebraic`: when `K / ℚ` is algebraic in characteristic zero,
  all coefficients of `f` lie in a common intermediate `NumberField`.
* `TauCeti.exists_pos_nat_sub_C_mem_scaledIntegralSeries`: `f - C (constantCoeff f)` lies in
  `scaledIntegralSeries (integralClosure ℤ K) M` for some positive integer `M`.
* `TauCeti.exists_pos_nat_smul_mem_scaledIntegralSeries`: `(c : K) • f` lies in
  `scaledIntegralSeries (integralClosure ℤ K) M` for some positive integers `c, M`.
* `TauCeti.exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral`: if `constantCoeff f` is
  integral over `ℤ`, then `f ∈ scaledIntegralSeries (integralClosure ℤ K) M` for some `M > 0`.
* `TauCeti.exists_pos_nat_smul_mem_scaledIntegralSeries_rat` and
  `TauCeti.exists_pos_nat_mem_scaledIntegralSeries_rat`: the specializations to `ℚ⟦X⟧` and
  `scaledIntegralSeries ℤ M`.

## References

* Yu. Bilu and M. Borichev, *Remarks on Eisenstein*, J. Aust. Math. Soc. **94** (2013), 158–180
  (`arXiv:1112.2290v2`), §1 (p. 1) and Theorem 6.1 (pp. 10–11).
-/

public section

open PowerSeries
open scoped LaurentSeries Polynomial RatFunc

namespace PowerSeries

/-- Clearing the rational-function denominators of the minimal polynomial of an algebraic series
`f ∈ K⟦X⟧` over `K(X)` produces a bivariate polynomial `P ∈ K[X][Y]` annihilating `f` whose
`Y`-derivative is nonzero at `f`. -/
theorem exists_aeval_eq_zero_aeval_derivative_ne_zero_of_isAlgebraic {K : Type*} [Field K]
    [CharZero K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ P : K[X][X], Polynomial.aeval f P = 0 ∧ Polynomial.aeval f P.derivative ≠ 0 := by
  set Q := minpoly K⟮X⟯ (f : K⸨X⸩)
  have hQd_ne : Polynomial.aeval (f : K⸨X⸩) Q.derivative ≠ 0 :=
    (minpoly.irreducible hf.isIntegral).separable.aeval_derivative_ne_zero
      (minpoly.aeval K⟮X⟯ (f : K⸨X⸩))
  set P := IsLocalization.integerNormalization (nonZeroDivisors K[X]) Q
  obtain ⟨D, hD_mem, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors K[X]) Q
  have hD_ne : D ≠ 0 := nonZeroDivisors.ne_zero hD_mem
  have hmap' : P.map (algebraMap K[X] K⟮X⟯) = Polynomial.C (algebraMap K[X] K⟮X⟯ D) * Q := by
    rw [hmap, Algebra.smul_def, Polynomial.algebraMap_apply]
  have haeval (A : K[X][X]) (B : K⟮X⟯[X])
      (hAB : A.map (algebraMap K[X] K⟮X⟯) = Polynomial.C (algebraMap K[X] K⟮X⟯ D) * B) :
      ((Polynomial.aeval f A : K⟦X⟧) : K⸨X⸩) =
        algebraMap K[X] K⸨X⸩ D * Polynomial.aeval (f : K⸨X⸩) B := by
    rw [coe_aeval_polynomial_powerSeries, Polynomial.aeval_def,
      IsScalarTower.algebraMap_eq K[X] K⟮X⟯ K⸨X⸩, ← Polynomial.eval₂_map, hAB,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply, ← Polynomial.aeval_def]
  refine ⟨P, ?_, fun h ↦ hQd_ne ?_⟩
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [haeval P Q hmap', minpoly.aeval, mul_zero, map_zero]
  · have h' := congrArg (HahnSeries.ofPowerSeries ℤ K) h
    have hmap_deriv : P.derivative.map (algebraMap K[X] K⟮X⟯) =
        Polynomial.C (algebraMap K[X] K⟮X⟯ D) * Q.derivative := by
      rw [← Polynomial.derivative_map, hmap', Polynomial.derivative_C_mul]
    rw [haeval P.derivative Q.derivative hmap_deriv, map_zero, mul_eq_zero] at h'
    exact h'.resolve_left fun hD0 ↦ hD_ne <|
      (injective_iff_map_eq_zero _).mp (FaithfulSMul.algebraMap_injective K[X] K⸨X⸩) D hD0

end PowerSeries

section Helpers

/-- Finite set of coefficients for the tail reduction `f = b + X ^ N * (C g₀ + u)` with
`u = X * R(X, u)`, including `0` so all truncation and recurrence coefficients lie in the set. -/
private noncomputable def tailCoeffSet {K : Type*} [Semiring K] [DecidableEq K] (g₀ : K)
    (b : K[X]) (R : K[X][X]) : Finset K :=
  {0, g₀} ∪ b.coeffs ∪ (R.support.biUnion fun j ↦ (R.coeff j).coeffs)

private lemma mem_tailCoeffSet_self {K : Type*} [Semiring K] [DecidableEq K] (g₀ : K) (b : K[X])
    (R : K[X][X]) : g₀ ∈ tailCoeffSet g₀ b R := by
  simp [tailCoeffSet]

private lemma coeff_mem_tailCoeffSet {K : Type*} [Semiring K] [DecidableEq K] (g₀ : K)
    (b : K[X]) (R : K[X][X]) (k : ℕ) : b.coeff k ∈ tailCoeffSet g₀ b R := by
  by_cases hk : b.coeff k = 0
  · simp [tailCoeffSet, hk]
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Polynomial.coeff_mem_coeffs hk))

private lemma coeff_coeff_mem_tailCoeffSet {K : Type*} [Semiring K] [DecidableEq K] (g₀ : K)
    (b : K[X]) (R : K[X][X]) (j i : ℕ) : (R.coeff j).coeff i ∈ tailCoeffSet g₀ b R := by
  rcases Polynomial.coeff_eq_zero_or_mem_biUnion_coeffs R j i with h0 | hmem
  · simp [tailCoeffSet, h0]
  · exact Finset.mem_union_right _ hmem

end Helpers

namespace PowerSeries

/-- If `K / F` is an algebraic extension in characteristic zero and `f ∈ K⟦X⟧` is algebraic over
`K(X)`, then all coefficients of `f` lie in a single finite-dimensional intermediate field of
`K / F`. -/
theorem exists_finiteDimensional_intermediateField_of_isAlgebraic {F K : Type*} [Field F]
    [Field K] [CharZero K] [Algebra F K] [Algebra.IsAlgebraic F K] (f : K⟦X⟧)
    (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ E : IntermediateField F K, FiniteDimensional F E ∧ ∀ n, coeff n f ∈ E := by
  classical
  obtain ⟨P, hP, hPd⟩ := exists_aeval_eq_zero_aeval_derivative_ne_zero_of_isAlgebraic hf
  obtain ⟨N, g₀, u, R, -, hfg, hu₀, huR⟩ :=
    exists_tail_eq_X_mul_aeval_of_aeval_eq_zero hP hPd
  let b : K[X] := trunc N f
  let T : Finset K := tailCoeffSet g₀ b R
  have hTint : ∀ x ∈ (T : Set K), IsIntegral F x := fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let E : IntermediateField F K := IntermediateField.adjoin F (T : Set K)
  have hfd : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin hTint
  have hmemT {x : K} (hx : x ∈ T) : x ∈ E := IntermediateField.subset_adjoin F (T : Set K) hx
  have huE (n : ℕ) : coeff n u ∈ E :=
    coeff_mem_subring_of_eq_X_mul_aeval (R := E.toSubring) huR
      (fun j i ↦ hmemT (coeff_coeff_mem_tailCoeffSet g₀ b R j i)) n
  refine ⟨E, hfd, fun n ↦ ?_⟩
  rw [coeff_eq_of_eq_trunc_add_X_pow_mul hfg hu₀ n]
  split_ifs
  exacts [hmemT (coeff_mem_tailCoeffSet g₀ b R n),
    hmemT (mem_tailCoeffSet_self g₀ b R), huE (n - N)]

/-- If `K / ℚ` is an algebraic extension and `f ∈ K⟦X⟧` is algebraic over `K(X)`, then all
coefficients of `f` lie in a single intermediate number field of `K`. -/
theorem exists_numberField_of_isAlgebraic {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] (f : K⟦X⟧) (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ (E : IntermediateField ℚ K) (_ : NumberField E), ∀ n, coeff n f ∈ E := by
  obtain ⟨E, hfd, hmem⟩ := exists_finiteDimensional_intermediateField_of_isAlgebraic (F := ℚ) f hf
  have : FiniteDimensional ℚ E := hfd
  exact ⟨E, ⟨⟩, hmem⟩

end PowerSeries

namespace TauCeti

/-- **Eisenstein's theorem (nonconstant part).** If `K / ℚ` is an algebraic extension and
`f ∈ K⟦X⟧` is algebraic over `K(X)`, then `f - C (constantCoeff f)` lies in the integral lattice at
some positive integer scale `M`: `(M : K)ⁿ * coeff n f` is integral over `ℤ` for every `n ≥ 1`. -/
theorem exists_pos_nat_sub_C_mem_scaledIntegralSeries {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ M : ℕ, 0 < M ∧
      f - C (constantCoeff f) ∈ scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  classical
  obtain ⟨P, hP, hPd⟩ := exists_aeval_eq_zero_aeval_derivative_ne_zero_of_isAlgebraic hf
  obtain ⟨N, g₀, u, R, hN, hfg, hu₀, huR⟩ :=
    exists_tail_eq_X_mul_aeval_of_aeval_eq_zero hP hPd
  let T : Finset K := tailCoeffSet g₀ (trunc N f) R
  obtain ⟨M, hMpos, hM_int⟩ :=
    Algebra.exists_pos_nat_mul_isIntegral T (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)
  have huM_int := isIntegral_pow_mul_coeff_of_eq_X_mul_aeval huR M
    (fun j i ↦ hM_int _ (coeff_coeff_mem_tailCoeffSet g₀ (trunc N f) R j i))
  refine ⟨M, hMpos, mem_scaledIntegralSeries_integralClosure_iff.mpr fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [isIntegral_zero]
  rw [map_sub, coeff_C, ite_eq_right hn0, sub_zero, coeff_eq_of_eq_trunc_add_X_pow_mul hfg hu₀ n]
  split_ifs with hlt hEq
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hk, pow_succ, mul_assoc]
    exact ((isIntegral_natCast M).pow k).mul
      (hM_int _ (coeff_mem_tailCoeffSet g₀ (trunc N f) R k.succ))
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [hEq, hk, pow_succ, mul_assoc]
    exact ((isIntegral_natCast M).pow k).mul (hM_int _ (mem_tailCoeffSet_self g₀ (trunc N f) R))
  · have hpow : (M : K) ^ n = (M : K) ^ N * (M : K) ^ (n - N) := by
      rw [← pow_add, Nat.add_sub_of_le (le_of_not_gt hlt)]
    rw [hpow, mul_assoc]
    exact ((isIntegral_natCast M).pow N).mul (huM_int (n - N))

/-- **Eisenstein's theorem.** If `K / ℚ` is an algebraic extension and `f ∈ K⟦X⟧` is algebraic
over `K(X)`, then there exist positive rational integers `c` and `M` such that
`(c : K) • f ∈ scaledIntegralSeries (integralClosure ℤ K) M`, i.e., `(c : K) * (M : K)ⁿ * coeff n f`
is integral over `ℤ` for every `n ≥ 0`. -/
theorem exists_pos_nat_smul_mem_scaledIntegralSeries {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ c M : ℕ, 0 < c ∧ 0 < M ∧
      (c : K) • f ∈ scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨M, hM, hfsub⟩ := exists_pos_nat_sub_C_mem_scaledIntegralSeries hf
  obtain ⟨c, hcpos, hc_int⟩ := Algebra.exists_pos_nat_mul_isIntegral {constantCoeff f}
    (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)
  have hc_int' : IsIntegral ℤ ((c : K) * constantCoeff f) :=
    hc_int _ (Finset.mem_singleton_self _)
  refine ⟨c, M, hcpos, hM, ?_⟩
  have hdecomp : (c : K) • f = C (c : K) * (f - C (constantCoeff f)) +
      C ((c : K) * constantCoeff f) := by
    rw [smul_eq_C_mul, mul_sub, ← map_mul, sub_add_cancel]
  rw [hdecomp]
  refine Subring.add_mem _ (Subring.mul_mem _ ?_ hfsub) ?_
  · rw [C_mem_scaledIntegralSeries_iff]
    exact ⟨⟨c, (mem_integralClosure_iff ℤ K).mpr (isIntegral_natCast c)⟩, rfl⟩
  · rw [C_mem_scaledIntegralSeries_iff]
    exact ⟨⟨(c : K) * constantCoeff f, (mem_integralClosure_iff ℤ K).mpr hc_int'⟩, rfl⟩

/-- **Eisenstein's theorem (integral constant term).** If `K / ℚ` is an algebraic extension,
`f ∈ K⟦X⟧` is algebraic over `K(X)`, and `constantCoeff f` is integral over `ℤ`, then
`f ∈ scaledIntegralSeries (integralClosure ℤ K) M` for some positive integer `M`. -/
theorem exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩))
    (hf₀ : IsIntegral ℤ (constantCoeff f)) :
    ∃ M : ℕ, 0 < M ∧ f ∈ scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨M, hM, hfsub⟩ := exists_pos_nat_sub_C_mem_scaledIntegralSeries hf
  refine ⟨M, hM, ?_⟩
  rw [← sub_add_cancel f (C (constantCoeff f))]
  refine Subring.add_mem _ hfsub ?_
  rw [C_mem_scaledIntegralSeries_iff]
  exact ⟨⟨constantCoeff f, (mem_integralClosure_iff ℤ K).mpr hf₀⟩, rfl⟩

/-- Specialization of `TauCeti.exists_pos_nat_smul_mem_scaledIntegralSeries` to rational power
series: if `f ∈ ℚ⟦X⟧` is algebraic over `ℚ(X)`, then `(c : ℚ) • f ∈ scaledIntegralSeries ℤ M`
for some positive integers `c, M`. -/
theorem exists_pos_nat_smul_mem_scaledIntegralSeries_rat {f : ℚ⟦X⟧}
    (hf : IsAlgebraic ℚ⟮X⟯ (f : ℚ⸨X⸩)) :
    ∃ c M : ℕ, 0 < c ∧ 0 < M ∧ (c : ℚ) • f ∈ scaledIntegralSeries ℤ (M : ℚ) := by
  obtain ⟨c, M, hc, hM, hmem⟩ := exists_pos_nat_smul_mem_scaledIntegralSeries hf
  rw [scaledIntegralSeries_integralClosure] at hmem
  exact ⟨c, M, hc, hM, hmem⟩

/-- Specialization of `TauCeti.exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral` to rational
power series: if `f ∈ ℚ⟦X⟧` is algebraic over `ℚ(X)` and its constant coefficient is an integer,
then `f ∈ scaledIntegralSeries ℤ M` for some positive integer `M`. -/
theorem exists_pos_nat_mem_scaledIntegralSeries_rat {f : ℚ⟦X⟧}
    (hf : IsAlgebraic ℚ⟮X⟯ (f : ℚ⸨X⸩)) (hf₀ : ∃ a : ℤ, (a : ℚ) = constantCoeff f) :
    ∃ M : ℕ, 0 < M ∧ f ∈ scaledIntegralSeries ℤ (M : ℚ) := by
  obtain ⟨a, ha⟩ := hf₀
  obtain ⟨M, hM, hmem⟩ := exists_pos_nat_mem_scaledIntegralSeries_of_isIntegral hf
    (ha ▸ isIntegral_intCast a)
  rw [scaledIntegralSeries_integralClosure] at hmem
  exact ⟨M, hM, hmem⟩

/-! ### Examples -/

section Examples

/-- The constant algebraic series `1 / 2 ∈ ℚ⟦X⟧` satisfies Eisenstein's theorem with `c = 2` and
`M = 1`, while no variable scaling `M` alone makes its constant term integral. -/
example : ((2 : ℕ) : ℚ) • C (1 / 2 : ℚ) ∈ scaledIntegralSeries ℤ (1 : ℚ) ∧
    ∀ M : ℚ, C (1 / 2 : ℚ) ∉ scaledIntegralSeries ℤ M := by
  refine ⟨mem_scaledIntegralSeries_int_iff.mpr fun n ↦ ?_, fun M h ↦ ?_⟩
  · rcases n with _ | n
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  · rw [C_mem_scaledIntegralSeries_iff] at h
    obtain ⟨a, ha⟩ := h
    have ha' : (a : ℚ) = 1 / 2 := by simpa using ha
    have h2 : ((2 * a : ℤ) : ℚ) = 1 := by push_cast; linarith
    have : 2 * a = 1 := by exact_mod_cast h2
    omega

/-- The square root `√(1 - 4X) = 1 - 2X - 2X² - 4X³ - ⋯` is algebraic over `ℚ(X)` and satisfies
Eisenstein's theorem with `c = 1` and `M = 1`. -/
example : let f : ℚ⟦X⟧ := rescale (-1 : ℚ) (sqrtOneAddFour.map (Int.castRingHom ℚ))
    IsAlgebraic ℚ⟮X⟯ (f : ℚ⸨X⸩) ∧
      coeff 0 f = 1 ∧ coeff 1 f = -2 ∧ coeff 2 f = -2 ∧ coeff 3 f = -4 ∧
      f ∈ scaledIntegralSeries ℤ (1 : ℚ) := by
  intro f
  have hsq : f ^ 2 = 1 - 4 * X := by
    have h1 : (sqrtOneAddFour.map (Int.castRingHom ℚ)) ^ 2 = 1 + 4 * X := by
      rw [← map_pow, sqrtOneAddFour_sq]
      simp [map_ofNat]
    have h2 := congrArg (rescale (-1 : ℚ)) h1
    rw [map_pow, map_add, map_one, map_mul, rescale_X, map_ofNat] at h2
    simpa [f, smul_eq_C_mul, mul_assoc, sub_eq_add_neg] using h2
  have hmem : f ∈ scaledIntegralSeries ℤ (1 : ℚ) :=
    mem_scaledIntegralSeries_int_iff.mpr fun n ↦
      ⟨(-1 : ℤ) ^ n * coeff n sqrtOneAddFour, by
        simp only [f, one_pow, one_mul, coeff_rescale, coeff_map, eq_intCast]
        push_cast
        ring⟩
  refine ⟨⟨Polynomial.X ^ 2 - Polynomial.C (1 - 4 * RatFunc.X), ?_, ?_⟩, ?_, ?_, ?_, ?_, hmem⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by decide) _
  · have hcoe : ((1 - 4 * X : ℚ⟦X⟧) : ℚ⸨X⸩) = algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (1 - 4 * RatFunc.X) := by
      simp [map_sub, map_mul, RatFunc.coe_X, map_ofNat]
    rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, ← PowerSeries.coe_pow, hsq, hcoe,
      sub_self]
  · simp [f]
  · simp [f]
  · simp [f]
  · simp [f, catalan_two]; norm_num

end Examples

end TauCeti
