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
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import TauCeti.RingTheory.PowerSeries.SqrtOneAddFour

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

* `PowerSeries.exists_finiteDimensional_intermediateField_of_isAlgebraic`: all coefficients of an
  algebraic series over `K(X)` lie in a common finite-dimensional intermediate field of `K / F` when
  `K / F` is algebraic in characteristic zero.
* `PowerSeries.exists_numberField_of_isAlgebraic`: when `K / ℚ` is algebraic in characteristic zero,
  all coefficients of `f` lie in a common intermediate `NumberField`.
* `TauCeti.exists_pos_int_sub_C_mem_scaledIntegralSeries`: `f - C (constantCoeff f)` lies in
  `scaledIntegralSeries (integralClosure ℤ K) M` for some positive integer `M`.
* `TauCeti.exists_pos_int_mul_mem_scaledIntegralSeries`: `(c : K) • f` lies in
  `scaledIntegralSeries (integralClosure ℤ K) M` for some positive integers `c, M`.
* `TauCeti.exists_pos_int_mem_scaledIntegralSeries_of_isIntegral`: if `constantCoeff f` is
  integral over `ℤ`, then `f ∈ scaledIntegralSeries (integralClosure ℤ K) M` for some `M > 0`.
* `TauCeti.exists_pos_int_mul_mem_scaledIntegralSeries_rat` and
  `TauCeti.exists_pos_int_mem_scaledIntegralSeries_rat`: the specializations to `ℚ⟦X⟧` and
  `scaledIntegralSeries ℤ M`.

## References

* Yu. Bilu and M. Borichev, *Remarks on Eisenstein*, J. Aust. Math. Soc. **94** (2013), 158–180
  (`arXiv:1112.2290v2`), §1 (p. 1) and Theorem 6.1 (pp. 10–11).
-/

public section

open PowerSeries
open scoped LaurentSeries Polynomial RatFunc

section Helpers

/-- Rewriting `algebraMap K[X] K⟦X⟧` as the canonical polynomial-to-power-series coercion. -/
private theorem algebraMap_polynomial_powerSeries {K : Type*} [CommRing K] (p : K[X]) :
    algebraMap K[X] K⟦X⟧ p = (p : K⟦X⟧) := by
  simp [PowerSeries.algebraMap_apply']

/-- Lifting bivariate evaluation `K[X][Y] → K⟦X⟧` into `K⸨X⸩`. -/
private theorem coe_aeval_polynomial_powerSeries {K : Type*} [Field K] (f : K⟦X⟧)
    (R : K[X][X]) :
    ((Polynomial.aeval f R : K⟦X⟧) : K⸨X⸩) = Polynomial.aeval (f : K⸨X⸩) R := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range,
    Polynomial.eval₂_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, algebraMap_polynomial_powerSeries, RatFunc.coe_coe,
    RatFunc.coePolynomial_eq_algebraMap, ← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ K⸨X⸩]

/-- Clearing the rational-function denominators of the minimal polynomial of an algebraic series
`f ∈ K⟦X⟧` over `K(X)` produces a bivariate polynomial `P ∈ K[X][Y]` annihilating `f` whose
`Y`-derivative is nonzero at `f`. -/
private theorem clearDenom_minpoly {K : Type*} [Field K] [CharZero K] {f : K⟦X⟧}
    (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
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
  refine ⟨P, HahnSeries.ofPowerSeries_injective (by
    rw [coe_aeval_polynomial_powerSeries, map_zero, Polynomial.aeval_def,
      IsScalarTower.algebraMap_eq K[X] K⟮X⟯ K⸨X⸩, ← Polynomial.eval₂_map, hmap',
      Polynomial.eval₂_mul, Polynomial.eval₂_C, ← Polynomial.aeval_def, minpoly.aeval,
      mul_zero]), fun h ↦ hQd_ne ?_⟩
  have h' := congrArg (HahnSeries.ofPowerSeries ℤ K) h
  rw [coe_aeval_polynomial_powerSeries, map_zero, Polynomial.aeval_def,
    IsScalarTower.algebraMap_eq K[X] K⟮X⟯ K⸨X⸩, ← Polynomial.eval₂_map,
    ← Polynomial.derivative_map, hmap', Polynomial.derivative_C_mul, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, ← Polynomial.aeval_def, mul_eq_zero] at h'
  refine h'.resolve_left fun hD0 ↦ hD_ne ?_
  exact (injective_iff_map_eq_zero _).mp (FaithfulSMul.algebraMap_injective K[X] K⸨X⸩) D
    (by simpa [IsScalarTower.algebraMap_apply K[X] K⟮X⟯ K⸨X⸩] using hD0)

/-- Divisibility of a polynomial `p ∈ K[X]` by `X ^ m` from the vanishing of its low
coefficients. -/
private theorem polynomial_X_pow_dvd_iff {K : Type*} [CommRing K] {m : ℕ} {p : K[X]} :
    Polynomial.X ^ m ∣ p ↔ ∀ i < m, p.coeff i = 0 := by
  refine ⟨fun ⟨q, hq⟩ i hi ↦ ?_, fun h ↦ Polynomial.X_pow_dvd_iff.mpr h⟩
  rw [hq, mul_comm, Polynomial.coeff_mul_X_pow', ite_eq_right (not_le.mpr hi)]

/-- Factoring a common divisor `d : K[X]` out of every coefficient of `T : K[X][Y]`. -/
private theorem exists_eq_C_mul_of_dvd {K : Type*} [Field K] {d : K[X]} (hd_ne : d ≠ 0)
    (T : K[X][X]) (hd : ∀ k, d ∣ T.coeff k) :
    ∃ Q : K[X][X], T = Polynomial.C d * Q ∧ ∀ k, d * Q.coeff k = T.coeff k := by
  classical
  let Q : K[X][X] := ∑ k ∈ T.support, Polynomial.monomial k (T.coeff k / d)
  have hcoeff (k : ℕ) : d * Q.coeff k = T.coeff k := by
    dsimp [Q]
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial, Finsupp.single_apply]
    by_cases hk : k ∈ T.support
    · rw [Finset.sum_eq_single k (fun j _ hjk ↦ ite_eq_right hjk) (fun h ↦ absurd hk h),
        ite_eq_left rfl]
      exact EuclideanDomain.mul_div_cancel' hd_ne (hd k)
    · rw [Finset.sum_eq_zero fun j hj ↦ ite_eq_right fun h ↦ hk (by simpa [h] using hj),
        mul_zero, Polynomial.notMem_support_iff.mp hk]
  refine ⟨Q, ?_, hcoeff⟩
  ext k
  rw [Polynomial.coeff_C_mul, hcoeff k]

/-- Splitting a power series at index `N` into its `N`-truncation plus `X ^ N` times the tail. -/
private theorem eq_trunc_add_X_pow_mul {K : Type*} [CommRing K] (f : K⟦X⟧) (N : ℕ) :
    f = (trunc N f : K⟦X⟧) + X ^ N * mk fun n ↦ coeff (n + N) f := by
  ext n
  rw [map_add, Polynomial.coeff_coe, coeff_trunc, coeff_X_pow_mul']
  by_cases h : n < N
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h, coeff_mk]

/-- Evaluating `P(b + X ^ N * g)` at `g` via the shifted Taylor polynomial
`T = (P.taylor b)(X ^ N * Y)`. -/
private theorem aeval_taylor_comp_X_pow_mul {K : Type*} [CommRing K] (P : K[X][X]) (b : K[X])
    (N : ℕ) (g : K⟦X⟧) :
    Polynomial.aeval g ((P.taylor b).comp (Polynomial.C (Polynomial.X ^ N) * Polynomial.X)) =
      Polynomial.aeval ((b : K⟦X⟧) + X ^ N * g) P := by
  have hcomp :
      Polynomial.aeval g ((P.taylor b).comp (Polynomial.C (Polynomial.X ^ N) * Polynomial.X)) =
      Polynomial.aeval (Polynomial.aeval g (Polynomial.C (Polynomial.X ^ N) * Polynomial.X))
        (P.taylor b) :=
    Polynomial.aeval_comp g
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_polynomial_powerSeries,
    Polynomial.coe_pow, Polynomial.coe_X] at hcomp
  rw [hcomp, Polynomial.taylor_apply, Polynomial.aeval_comp, map_add, Polynomial.aeval_X,
    Polynomial.aeval_C, algebraMap_polynomial_powerSeries, add_comm]

/-- Low coefficients of `P'(b)` agree with those of `P'(f)` when `b = trunc N f`. -/
private theorem deriv_eval_trunc_coeff {K : Type*} [CommRing K] (P : K[X][X]) (f : K⟦X⟧)
    {N s i : ℕ} (hi : i ≤ s) (hs : s < N) :
    (P.derivative.eval (trunc N f)).coeff i = coeff i (Polynomial.aeval f P.derivative) := by
  let b : K[X] := trunc N f
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  have hfb : X ^ N ∣ f - (b : K⟦X⟧) := ⟨g, by rw [eq_trunc_add_X_pow_mul f N]; ring⟩
  obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub f (b : K⟦X⟧)
    (P.derivative.map (algebraMap K[X] K⟦X⟧))
  obtain ⟨v, hv⟩ := hfb.trans ⟨w, by
    simpa only [Polynomial.aeval_def, Polynomial.eval_map] using hw⟩
  have hPb_eval : Polynomial.aeval (b : K⟦X⟧) P.derivative =
      ((P.derivative.eval b : K[X]) : K⟦X⟧) := by
    rw [Polynomial.aeval_def]
    symm
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, ← Polynomial.eval₂_id,
      Polynomial.hom_eval₂, RingHom.comp_id, Polynomial.coeToPowerSeries.ringHom_apply]
    congr 1
  have hci := congrArg (coeff i) hv
  rw [map_sub, coeff_X_pow_mul', ite_eq_right (by omega), sub_eq_zero,
    ← Polynomial.aeval_def, ← Polynomial.aeval_def, hPb_eval, Polynomial.coeff_coe] at hci
  exact hci.symm

/-- From `aeval g T = 0` and divisibility of `T.coeff k` for `k ≥ 1` by `X ^ m`, deduce that
`X ^ m` divides `T.coeff 0`. -/
private theorem X_pow_dvd_coeff_zero_of_aeval_eq_zero {K : Type*} [Field K] {T : K[X][X]}
    {g : K⟦X⟧} {m : ℕ} (hT : Polynomial.aeval g T = 0)
    (hdvd : ∀ k, 1 ≤ k → Polynomial.X ^ m ∣ T.coeff k) :
    Polynomial.X ^ m ∣ T.coeff 0 := by
  rw [polynomial_X_pow_dvd_iff]
  intro i hi
  have hev := congrArg (coeff i) hT
  rw [Polynomial.aeval_eq_sum_range, map_sum, map_zero] at hev
  have hrest : ∀ k ∈ Finset.range (T.natDegree + 1), k ≠ 0 →
      coeff i (algebraMap K[X] K⟦X⟧ (T.coeff k) * g ^ k) = 0 := by
    intro k _ hk0
    obtain ⟨q, hq⟩ := hdvd k (Nat.pos_of_ne_zero hk0)
    rw [algebraMap_polynomial_powerSeries, hq, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, mul_assoc, coeff_X_pow_mul', ite_eq_right (not_le.mpr hi)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.succ_pos T.natDegree)),
    Finset.sum_eq_zero (fun k hk ↦ by
      simp only [Algebra.smul_def]
      exact hrest k (Finset.mem_erase.mp hk).2 (Finset.mem_erase.mp hk).1),
    add_zero, Algebra.smul_def, pow_zero, mul_one, algebraMap_polynomial_powerSeries,
    Polynomial.coeff_coe] at hev
  exact hev

/-- Coefficient divisibility for the shifted Taylor polynomial `T = (P.taylor b)(X ^ N * Y)`:
setting `N = s + 1` where `s = order (P'(f))` makes `X ^ (N + s)` divide `T.coeff 1` and
`X ^ (N + s + 1)` divide `T.coeff k` for `k ≥ 2`. -/
private theorem taylor_comp_X_pow_dvd {K : Type*} [Field K] {f : K⟦X⟧} {P : K[X][X]}
    (hf : Polynomial.aeval f P = 0) (hfd : Polynomial.aeval f P.derivative ≠ 0) :
    let s : ℕ := (Polynomial.aeval f P.derivative).order.toNat
    let N : ℕ := s + 1
    let T : K[X][X] := (P.taylor (trunc N f)).comp (Polynomial.C (Polynomial.X ^ N) * Polynomial.X)
    (Polynomial.X ^ (N + s) ∣ T.coeff 1) ∧
      (∀ {k : ℕ}, 2 ≤ k → Polynomial.X ^ (N + s + 1) ∣ T.coeff k) ∧
      (∀ k, Polynomial.X ^ (N + s) ∣ T.coeff k) := by
  intro s N T
  let b : K[X] := trunc N f
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  have hT_eval : Polynomial.aeval g T = 0 := by
    dsimp [T, b, g]
    rw [aeval_taylor_comp_X_pow_mul, ← eq_trunc_add_X_pow_mul f N, hf]
  have hT_coeff (k : ℕ) : T.coeff k = (P.taylor b).coeff k * Polynomial.X ^ (N * k) := by
    dsimp [T, b]; rw [Polynomial.comp_C_mul_X_coeff, pow_mul]
  have hT1_dvd : Polynomial.X ^ (N + s) ∣ T.coeff 1 := by
    rw [hT_coeff 1, mul_one, Polynomial.taylor_coeff_one, pow_add, mul_comm (Polynomial.X ^ N)]
    refine mul_dvd_mul_right (polynomial_X_pow_dvd_iff.mpr fun i hi ↦ ?_) _
    rw [deriv_eval_trunc_coeff P f hi.le (Nat.lt_succ_self s)]
    exact coeff_of_lt_order i (by
      rw [← ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hfd)]
      exact Nat.cast_lt.mpr hi)
  have hT_ge_dvd {k : ℕ} (hk : 2 ≤ k) : Polynomial.X ^ (N + s + 1) ∣ T.coeff k := by
    rw [hT_coeff k]
    have hNs : N + s + 1 ≤ N * k := by dsimp [N]; nlinarith
    exact dvd_mul_of_dvd_right (pow_dvd_pow Polynomial.X hNs) _
  refine ⟨hT1_dvd, fun hk ↦ hT_ge_dvd hk, fun k ↦ ?_⟩
  rcases lt_trichotomy k 1 with hk0 | rfl | hk2
  · rw [Nat.lt_one_iff.mp hk0]
    exact X_pow_dvd_coeff_zero_of_aeval_eq_zero hT_eval fun j hj ↦ by
      rcases eq_or_lt_of_le hj with rfl | hj2
      exacts [hT1_dvd, (pow_dvd_pow Polynomial.X (Nat.le_succ _)).trans (hT_ge_dvd hj2)]
  · exact hT1_dvd
  · exact (pow_dvd_pow Polynomial.X (Nat.le_succ _)).trans (hT_ge_dvd hk2)

/-- First stage of the Bilu–Borichev reduction: dividing out `X ^ (N + s)` from the shifted
Taylor polynomial yields `Q ∈ K[X][Y]` annihilating `g` with `(Q.coeff 1)(0) ≠ 0` and
`(Q.coeff k)(0) = 0` for `k ≥ 2`. -/
private theorem exists_div_X_pow_eq_zero_of_aeval_eq_zero {K : Type*} [Field K] {f : K⟦X⟧}
    {P : K[X][X]} (hf : Polynomial.aeval f P = 0) (hfd : Polynomial.aeval f P.derivative ≠ 0) :
    ∃ (N : ℕ) (Q : K[X][X]),
      1 ≤ N ∧ f = (trunc N f : K⟦X⟧) + X ^ N * mk (fun n ↦ coeff (n + N) f) ∧
        Polynomial.aeval (mk fun n ↦ coeff (n + N) f) Q = 0 ∧
        (Q.coeff 1).coeff 0 ≠ 0 ∧ ∀ k, 2 ≤ k → (Q.coeff k).coeff 0 = 0 := by
  let s : ℕ := (Polynomial.aeval f P.derivative).order.toNat
  let N : ℕ := s + 1
  let b : K[X] := trunc N f
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  have hfg : f = (b : K⟦X⟧) + X ^ N * g := eq_trunc_add_X_pow_mul f N
  let T : K[X][X] := (P.taylor b).comp (Polynomial.C (Polynomial.X ^ N) * Polynomial.X)
  have hT_eval : Polynomial.aeval g T = 0 := by
    dsimp [T]; rw [aeval_taylor_comp_X_pow_mul, ← hfg, hf]
  obtain ⟨-, hT_ge_dvd, hTdvd⟩ := taylor_comp_X_pow_dvd hf hfd
  obtain ⟨Q, hTQ, hQcoeff⟩ :=
    exists_eq_C_mul_of_dvd (pow_ne_zero _ Polynomial.X_ne_zero) T hTdvd
  have hQ_eval : Polynomial.aeval g Q = 0 := by
    have hmul : X ^ (N + s) * Polynomial.aeval g Q = 0 := by
      have := hT_eval
      rwa [hTQ, map_mul, Polynomial.aeval_C, algebraMap_polynomial_powerSeries, Polynomial.coe_pow,
        Polynomial.coe_X] at this
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  refine ⟨N, Q, by omega, hfg, hQ_eval, ?_, ?_⟩
  · have h1 := congrArg (fun p : K[X] ↦ p.coeff (N + s)) (hQcoeff 1)
    rw [Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self] at h1
    dsimp [T] at h1
    rw [Polynomial.comp_C_mul_X_coeff, pow_one, Polynomial.taylor_coeff_one, mul_comm,
      Polynomial.coeff_X_pow_mul', ite_eq_left (Nat.le_add_right N s), add_comm N s,
      Nat.add_sub_cancel, deriv_eval_trunc_coeff P f le_rfl (Nat.lt_succ_self s)] at h1
    exact h1 ▸ coeff_order hfd
  · intro k hk
    obtain ⟨q, hq⟩ := hT_ge_dvd hk
    have hq_eq : Q.coeff k = Polynomial.X * q := by
      apply mul_left_cancel₀ (pow_ne_zero (N + s) Polynomial.X_ne_zero)
      rw [hQcoeff k, hq, ← mul_assoc, ← pow_succ]
    rw [hq_eq, Polynomial.coeff_X_mul_zero]

/-- Evaluating the Taylor shift and scalar normalization of `Q` at `X = 0` yields `Y`. -/
private theorem map_eval_zero_normalize_taylor {K : Type*} [Field K] {g : K⟦X⟧}
    {Q : K[X][X]} (hQ_eval : Polynomial.aeval g Q = 0) (hQ1 : (Q.coeff 1).coeff 0 ≠ 0)
    (hQ_ge : ∀ k, 2 ≤ k → (Q.coeff k).coeff 0 = 0) :
    (Polynomial.C (Polynomial.C ((Q.coeff 1).coeff 0)⁻¹) *
        Q.taylor (Polynomial.C (constantCoeff g))).map (Polynomial.evalRingHom 0) =
      Polynomial.X := by
  let g₀ : K := constantCoeff g
  let ev0 : K[X] →+* K := Polynomial.evalRingHom 0
  have hQ0_map : Q.map ev0 = Polynomial.C ((Q.coeff 0).coeff 0) +
      Polynomial.C ((Q.coeff 1).coeff 0) * Polynomial.X := by
    ext k
    rcases k with _ | _ | k
    · simp [ev0, Polynomial.coeff_zero_eq_eval_zero]
    · simp [ev0, Polynomial.coeff_zero_eq_eval_zero]
    · simp [ev0, ← Polynomial.coeff_zero_eq_eval_zero, hQ_ge (k + 2) (by omega)]
  have hQ_const : (Q.coeff 0).coeff 0 + (Q.coeff 1).coeff 0 * g₀ = 0 := by
    have hc := congrArg constantCoeff hQ_eval
    rw [map_zero, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, map_sum] at hc
    have hsum : ∑ i ∈ Finset.range (Q.natDegree + 1), ev0 (Q.coeff i) * g₀ ^ i = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) hc
      rw [map_mul, map_pow, algebraMap_polynomial_powerSeries, Polynomial.constantCoeff_coe,
        Polynomial.coeff_zero_eq_eval_zero]
      rfl
    rw [← Polynomial.eval₂_eq_sum_range, ← Polynomial.eval_map, hQ0_map] at hsum
    simpa using hsum
  have hQ1_map :
      (Q.taylor (Polynomial.C g₀)).map ev0 = Polynomial.C ((Q.coeff 1).coeff 0) * Polynomial.X := by
    rw [Polynomial.map_taylor, hQ0_map, Polynomial.taylor_apply, Polynomial.add_comp,
      Polynomial.C_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    simp only [ev0, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    rw [mul_add, ← Polynomial.C_mul, add_comm (Polynomial.C _ * Polynomial.X), ← add_assoc,
      ← Polynomial.C_add, hQ_const, map_zero, zero_add]
  rw [Polynomial.map_mul, Polynomial.map_C, hQ1_map, ← mul_assoc, ← Polynomial.C_mul]
  simp [inv_mul_cancel₀ hQ1]

/-- Second stage of the Bilu–Borichev reduction: shifting `g` by its constant term `g₀` and
normalizing by `(Q.coeff 1)(0)⁻¹` rewrites `u = g - C g₀` as `u = X * R(X, u)`. -/
private theorem exists_eq_X_mul_aeval_of_linear_const {K : Type*} [Field K] {g : K⟦X⟧}
    {Q : K[X][X]} (hQ_eval : Polynomial.aeval g Q = 0) (hQ1 : (Q.coeff 1).coeff 0 ≠ 0)
    (hQ_ge : ∀ k, 2 ≤ k → (Q.coeff k).coeff 0 = 0) :
    ∃ R : K[X][X], g - C (constantCoeff g) = X * Polynomial.aeval (g - C (constantCoeff g)) R := by
  let g₀ : K := constantCoeff g
  let u : K⟦X⟧ := g - C g₀
  let Q₁ : K[X][X] := Q.taylor (Polynomial.C g₀)
  have hQ1_eval : Polynomial.aeval u Q₁ = 0 := by
    have heq : u + algebraMap K[X] K⟦X⟧ (Polynomial.C g₀) = g := by
      simp [u, algebraMap_polynomial_powerSeries]
    simpa only [Q₁, Polynomial.taylor_apply, Polynomial.aeval_comp, map_add, Polynomial.aeval_X,
      Polynomial.aeval_C, heq] using hQ_eval
  let Q₂ : K[X][X] := Polynomial.C (Polynomial.C ((Q.coeff 1).coeff 0)⁻¹) * Q₁
  have hQ2_eval : Polynomial.aeval u Q₂ = 0 := by simp [Q₂, hQ1_eval]
  have hQ2_map : Q₂.map (Polynomial.evalRingHom 0) = Polynomial.X :=
    map_eval_zero_normalize_taylor hQ_eval hQ1 hQ_ge
  have hQ2_sub_dvd (k : ℕ) : Polynomial.X ∣ (Polynomial.X - Q₂).coeff k := by
    rw [← pow_one Polynomial.X, polynomial_X_pow_dvd_iff]
    intro i hi
    rw [Nat.lt_one_iff.mp hi]
    have h := congrArg (fun p : K[X] ↦ p.coeff k) hQ2_map
    rw [Polynomial.coeff_map] at h
    rcases eq_or_ne k 1 with rfl | hk
    · have h1 : Polynomial.evalRingHom 0 (Q₂.coeff 1) = 1 := by simpa using h
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_sub,
        AddMonoidAlgebra.coeff_one_zero, Polynomial.coeff_zero_eq_eval_zero]
      exact sub_eq_zero.mpr h1.symm
    · have hk0 : Polynomial.evalRingHom 0 (Q₂.coeff k) = 0 := by
        simpa [Polynomial.coeff_X_of_ne_one hk] using h
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_of_ne_one hk, zero_sub, Polynomial.coeff_neg,
        Polynomial.coeff_zero_eq_eval_zero, neg_eq_zero]
      exact hk0
  obtain ⟨R, hQ2_eq, -⟩ :=
    exists_eq_C_mul_of_dvd Polynomial.X_ne_zero (Polynomial.X - Q₂) hQ2_sub_dvd
  refine ⟨R, ?_⟩
  have h0 :
      Polynomial.aeval u (Polynomial.X - Q₂) = Polynomial.aeval u (Polynomial.C Polynomial.X * R) :=
    congrArg (Polynomial.aeval u) hQ2_eq
  rw [map_sub, Polynomial.aeval_X, hQ2_eval, sub_zero, map_mul, Polynomial.aeval_C,
    algebraMap_polynomial_powerSeries, Polynomial.coe_X] at h0
  exact h0

/-- Bilu–Borichev tail-series reduction: if `P ∈ K[X][Y]` annihilates `f ∈ K⟦X⟧` and `P_Y(f) ≠ 0`,
then splitting `f = b + X ^ N * (C g₀ + u)` at `N = order (P_Y(f)) + 1` satisfies
`u = X * R(X, u)` for a bivariate polynomial `R ∈ K[X][Y]`. -/
private theorem exists_tail_eq_X_mul_aeval_of_aeval_eq_zero {K : Type*} [Field K] {f : K⟦X⟧}
    {P : K[X][X]} (hf : Polynomial.aeval f P = 0) (hfd : Polynomial.aeval f P.derivative ≠ 0) :
    ∃ (N : ℕ) (g₀ : K) (u : K⟦X⟧) (R : K[X][X]),
      1 ≤ N ∧ f = (trunc N f : K⟦X⟧) + X ^ N * (C g₀ + u) ∧ constantCoeff u = 0 ∧
        u = X * Polynomial.aeval u R := by
  obtain ⟨N, Q, hN, hfg, hQ_eval, hQ1, hQ_ge⟩ :=
    exists_div_X_pow_eq_zero_of_aeval_eq_zero hf hfd
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  obtain ⟨R, huR⟩ := exists_eq_X_mul_aeval_of_linear_const hQ_eval hQ1 hQ_ge
  refine ⟨N, constantCoeff g, g - C (constantCoeff g), R, hN, ?_, by simp, huR⟩
  simpa [sub_add_cancel] using hfg

/-- If `u ∈ K⟦X⟧` satisfies `u = X * R(X, u)` for a bivariate polynomial `R ∈ K[X][Y]` whose
coefficients all lie in a subring `S ⊆ K`, then every coefficient of `u` lies in `S`. -/
private theorem coeff_mem_subring_of_eq_X_mul_aeval {K : Type*} [CommRing K] {S : Subring K}
    {u : K⟦X⟧} {R : K[X][X]} (hu : u = X * Polynomial.aeval u R)
    (hR : ∀ j i, (R.coeff j).coeff i ∈ S) (n : ℕ) : coeff n u ∈ S := by
  have hpow : ∀ m, (∀ k ≤ m, coeff k u ∈ S) → ∀ j k, k ≤ m → coeff k (u ^ j) ∈ S := by
    intro m hm j
    induction j with
    | zero =>
      intro k _
      rw [pow_zero, coeff_one]
      split_ifs
      exacts [S.one_mem, S.zero_mem]
    | succ j ih =>
      intro k hk
      rw [pow_succ, coeff_mul]
      refine S.sum_mem fun p hp ↦ ?_
      exact S.mul_mem (ih p.1 ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hk))
        (hm p.2 ((Finset.HasAntidiagonal.antidiagonal.snd_le hp).trans hk))
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [hu, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
      exact S.zero_mem
    · have hcoeff := congrArg (coeff (m + 1)) hu
      rw [coeff_succ_X_mul, Polynomial.aeval_eq_sum_range, map_sum] at hcoeff
      rw [hcoeff]
      refine S.sum_mem fun j _ ↦ ?_
      rw [Algebra.smul_def, algebraMap_polynomial_powerSeries, coeff_mul]
      refine S.sum_mem fun p hp ↦ ?_
      rw [Polynomial.coeff_coe]
      exact S.mul_mem (hR j p.1)
        (hpow m (fun k hk ↦ ih k (by omega)) j p.2 (Finset.HasAntidiagonal.antidiagonal.snd_le hp))

/-- Choosing a positive integer multiplier `M : ℕ` making every element of a finite subset
`T ⊆ K` integral over `ℤ`. -/
private theorem exists_pos_nat_mul_isIntegral {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] (T : Finset K) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ T, IsIntegral ℤ ((M : K) * x) := by
  have hAlgZK : Algebra.IsAlgebraic ℤ K :=
    have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨m, hm0, hm_int⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ T
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, fun x hx ↦ ?_⟩
  have h1 : IsIntegral ℤ ((m : K) * x) := by simpa [Algebra.smul_def] using hm_int x hx
  rcases Int.natAbs_eq m with hm | hm
  · have hMm : (m.natAbs : K) = (m : K) := by
      rw [← Int.cast_natCast (R := K)]
      exact congrArg (Int.cast (R := K)) hm.symm
    rwa [hMm]
  · have hMm : (m.natAbs : K) = -(m : K) := by
      rw [← Int.cast_natCast (R := K), ← Int.cast_neg]
      exact congrArg (Int.cast (R := K)) (by omega)
    rw [hMm, neg_mul]
    exact h1.neg

/-- Rescaling the Bilu–Borichev recurrence `u = X * R(X, u)` by a positive integer `M` clearing the
coefficients of `R` makes `Mⁿ * coeff n u` integral over `ℤ` for all `n`. -/
private theorem isIntegral_pow_mul_coeff_of_eq_X_mul_aeval {K : Type*} [CommRing K] {u : K⟦X⟧}
    {R : K[X][X]} (hu : u = X * Polynomial.aeval u R) (M : ℕ)
    (hRM : ∀ j i, IsIntegral ℤ ((M : K) * (R.coeff j).coeff i)) (n : ℕ) :
    IsIntegral ℤ ((M : K) ^ n * coeff n u) := by
  let R' : K[X][X] := Polynomial.C (Polynomial.C (M : K)) *
    R.map (Polynomial.compRingHom (Polynomial.C (M : K) * Polynomial.X))
  have hrescale_coe (p : K[X]) :
      rescale (M : K) (p : K⟦X⟧) =
        ((p.comp (Polynomial.C (M : K) * Polynomial.X) : K[X]) : K⟦X⟧) := by
    ext k
    rw [coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.comp_C_mul_X_coeff, mul_comm]
  have huM : rescale (M : K) u = X * Polynomial.aeval (rescale (M : K) u) R' := by
    have h := congrArg (rescale (M : K)) hu
    rw [map_mul, rescale_X, mul_assoc, mul_left_comm (C (M : K)) X] at h
    have heq : (rescale (M : K)).comp (algebraMap K[X] K⟦X⟧) =
        (algebraMap K[X] K⟦X⟧).comp
          (Polynomial.compRingHom (Polynomial.C (M : K) * Polynomial.X)) :=
      RingHom.ext fun p ↦ by simpa [algebraMap_polynomial_powerSeries] using hrescale_coe p
    conv_lhs => rw [h]
    rw [map_mul, Polynomial.aeval_C, algebraMap_polynomial_powerSeries, Polynomial.coe_C,
      Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, ← heq,
      ← Polynomial.hom_eval₂]
  have hR' : ∀ j i, (R'.coeff j).coeff i ∈ (integralClosure ℤ K).toSubring := by
    intro j i
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff, Polynomial.coeff_C_mul,
      Polynomial.coeff_map, Polynomial.coe_compRingHom_apply, Polynomial.coeff_C_mul,
      Polynomial.comp_C_mul_X_coeff, mul_comm ((R.coeff j).coeff i), mul_left_comm]
    exact ((isIntegral_natCast M).pow i).mul (hRM j i)
  have hmem := coeff_mem_subring_of_eq_X_mul_aeval (S := (integralClosure ℤ K).toSubring) huM hR' n
  rwa [Subalgebra.mem_toSubring, mem_integralClosure_iff, coeff_rescale] at hmem

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
  obtain ⟨P, hP, hPd⟩ := clearDenom_minpoly hf
  obtain ⟨N, g₀, u, R, -, hfg, -, huR⟩ :=
    exists_tail_eq_X_mul_aeval_of_aeval_eq_zero hP hPd
  let b : K[X] := trunc N f
  let T : Finset K :=
    {g₀} ∪ (b.support.image b.coeff) ∪
      (R.support.biUnion fun j ↦ (R.coeff j).support.image (R.coeff j).coeff)
  have hTint : ∀ x ∈ (T : Set K), IsIntegral F x := fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let E : IntermediateField F K := IntermediateField.adjoin F (T : Set K)
  have hfd : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin hTint
  have hmemT {x : K} (hx : x ∈ T) : x ∈ E := IntermediateField.subset_adjoin F (T : Set K) hx
  have hg₀E : g₀ ∈ E := hmemT (by simp [T])
  have hbE (k : ℕ) : b.coeff k ∈ E := by
    by_cases hk : k ∈ b.support
    · exact hmemT
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)))
    · rw [Polynomial.notMem_support_iff.mp hk]; exact E.zero_mem
  have hRE (j i : ℕ) : (R.coeff j).coeff i ∈ E := by
    by_cases hj : j ∈ R.support
    · by_cases hi : i ∈ (R.coeff j).support
      · exact hmemT (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image_of_mem _ hi⟩))
      · rw [Polynomial.notMem_support_iff.mp hi]; exact E.zero_mem
    · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.coeff_zero]; exact E.zero_mem
  have huE (n : ℕ) : coeff n u ∈ E :=
    coeff_mem_subring_of_eq_X_mul_aeval (S := E.toSubring) huR hRE n
  refine ⟨E, hfd, fun n ↦ ?_⟩
  rw [hfg, map_add, Polynomial.coeff_coe, coeff_X_pow_mul']
  split_ifs with hle
  · refine E.add_mem (hbE n) ?_
    rw [map_add]
    rcases eq_or_ne (n - N) 0 with h0 | hne
    · rw [h0, coeff_C, ite_eq_left rfl]
      exact E.add_mem hg₀E (huE 0)
    · rw [coeff_C, ite_eq_right hne, zero_add]
      exact huE (n - N)
  · simpa using hbE n

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
theorem exists_pos_int_sub_C_mem_scaledIntegralSeries {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ M : ℕ, 0 < M ∧
      f - C (constantCoeff f) ∈ scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  classical
  obtain ⟨P, hP, hPd⟩ := clearDenom_minpoly hf
  obtain ⟨N, g₀, u, R, hN, hfg, -, huR⟩ :=
    exists_tail_eq_X_mul_aeval_of_aeval_eq_zero hP hPd
  let T : Finset K :=
    {g₀} ∪ ((Finset.Ico 1 N).image (trunc N f).coeff) ∪
      (R.support.biUnion fun j ↦ (R.coeff j).support.image (R.coeff j).coeff)
  obtain ⟨M, hMpos, hM_int⟩ := exists_pos_nat_mul_isIntegral T
  have hRM (j i : ℕ) : IsIntegral ℤ ((M : K) * (R.coeff j).coeff i) := by
    by_cases hj : j ∈ R.support <;> by_cases hi : i ∈ (R.coeff j).support
    · exact hM_int _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image_of_mem _ hi⟩))
    all_goals simp [Polynomial.notMem_support_iff.mp ‹_›, isIntegral_zero]
  have huM_int := isIntegral_pow_mul_coeff_of_eq_X_mul_aeval huR M hRM
  have hfg₀ : coeff 0 u = 0 := by
    rw [huR, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
  refine ⟨M, hMpos, mem_scaledIntegralSeries_integralClosure_iff.mpr fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [isIntegral_zero]
  rw [map_sub, coeff_C, ite_eq_right hn0, sub_zero, hfg, map_add, Polynomial.coeff_coe,
    coeff_X_pow_mul']
  split_ifs with hle
  · rw [coeff_trunc, ite_eq_right (not_lt.mpr hle), zero_add, map_add, coeff_C]
    rcases eq_or_ne (n - N) 0 with hsub | hsub
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
      have hnN : n = N := by omega
      rw [hsub, ite_eq_left rfl, hfg₀, add_zero, hnN, hk, pow_succ, mul_assoc]
      exact ((isIntegral_natCast M).pow k).mul
        (hM_int g₀ (by simp [T]))
    · have hpow : (M : K) ^ n = (M : K) ^ N * (M : K) ^ (n - N) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      rw [ite_eq_right hsub, zero_add, hpow, mul_assoc]
      exact ((isIntegral_natCast M).pow N).mul (huM_int (n - N))
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hlt : k.succ < N := hk ▸ not_le.mp hle
    rw [add_zero, hk, pow_succ, mul_assoc]
    exact ((isIntegral_natCast M).pow k).mul
      (hM_int _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_Ico.mpr ⟨by omega, hlt⟩)))))

/-- **Eisenstein's theorem.** If `K / ℚ` is an algebraic extension and `f ∈ K⟦X⟧` is algebraic
over `K(X)`, then there exist positive rational integers `c` and `M` such that
`(c : K) • f ∈ scaledIntegralSeries (integralClosure ℤ K) M`, i.e., `(c : K) * (M : K)ⁿ * coeff n f`
is integral over `ℤ` for every `n ≥ 0`. -/
theorem exists_pos_int_mul_mem_scaledIntegralSeries {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩)) :
    ∃ c M : ℕ, 0 < c ∧ 0 < M ∧
      (c : K) • f ∈ scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨M, hM, hfsub⟩ := exists_pos_int_sub_C_mem_scaledIntegralSeries hf
  obtain ⟨c, hcpos, hc_int⟩ := exists_pos_nat_mul_isIntegral {constantCoeff f}
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
theorem exists_pos_int_mem_scaledIntegralSeries_of_isIntegral {K : Type*} [Field K] [CharZero K]
    [Algebra.IsAlgebraic ℚ K] {f : K⟦X⟧} (hf : IsAlgebraic K⟮X⟯ (f : K⸨X⸩))
    (hf₀ : IsIntegral ℤ (constantCoeff f)) :
    ∃ M : ℕ, 0 < M ∧ f ∈ scaledIntegralSeries (integralClosure ℤ K) (M : K) := by
  obtain ⟨M, hM, hfsub⟩ := exists_pos_int_sub_C_mem_scaledIntegralSeries hf
  refine ⟨M, hM, ?_⟩
  rw [← sub_add_cancel f (C (constantCoeff f))]
  refine Subring.add_mem _ hfsub ?_
  rw [C_mem_scaledIntegralSeries_iff]
  exact ⟨⟨constantCoeff f, (mem_integralClosure_iff ℤ K).mpr hf₀⟩, rfl⟩

/-- Specialization of `TauCeti.exists_pos_int_mul_mem_scaledIntegralSeries` to rational power
series: if `f ∈ ℚ⟦X⟧` is algebraic over `ℚ(X)`, then `(c : ℚ) • f ∈ scaledIntegralSeries ℤ M`
for some positive integers `c, M`. -/
theorem exists_pos_int_mul_mem_scaledIntegralSeries_rat {f : ℚ⟦X⟧}
    (hf : IsAlgebraic ℚ⟮X⟯ (f : ℚ⸨X⸩)) :
    ∃ c M : ℕ, 0 < c ∧ 0 < M ∧ (c : ℚ) • f ∈ scaledIntegralSeries ℤ (M : ℚ) := by
  obtain ⟨c, M, hc, hM, hmem⟩ := exists_pos_int_mul_mem_scaledIntegralSeries hf
  refine ⟨c, M, hc, hM, mem_scaledIntegralSeries_int_iff.mpr fun n ↦ ?_⟩
  have hint := mem_scaledIntegralSeries_integralClosure_iff.mp hmem n
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hint
  exact ⟨a, by simpa using ha⟩

/-- Specialization of `TauCeti.exists_pos_int_mem_scaledIntegralSeries_of_isIntegral` to rational
power series: if `f ∈ ℚ⟦X⟧` is algebraic over `ℚ(X)` and its constant coefficient is an integer,
then `f ∈ scaledIntegralSeries ℤ M` for some positive integer `M`. -/
theorem exists_pos_int_mem_scaledIntegralSeries_rat {f : ℚ⟦X⟧}
    (hf : IsAlgebraic ℚ⟮X⟯ (f : ℚ⸨X⸩)) (hf₀ : ∃ a : ℤ, (a : ℚ) = constantCoeff f) :
    ∃ M : ℕ, 0 < M ∧ f ∈ scaledIntegralSeries ℤ (M : ℚ) := by
  obtain ⟨a, ha⟩ := hf₀
  obtain ⟨M, hM, hmem⟩ := exists_pos_int_mem_scaledIntegralSeries_of_isIntegral hf
    (ha ▸ isIntegral_intCast a)
  refine ⟨M, hM, mem_scaledIntegralSeries_int_iff.mpr fun n ↦ ?_⟩
  have hint := mem_scaledIntegralSeries_integralClosure_iff.mp hmem n
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hint
  exact ⟨b, by simpa using hb⟩

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
