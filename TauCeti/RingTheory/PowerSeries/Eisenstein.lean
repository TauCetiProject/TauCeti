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
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.RingTheory.Algebraic.Denominator
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.PowerSeries.Basic
import TauCeti.RingTheory.PowerSeries.Evaluation
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

/-- Coefficient divisibility and evaluation properties for the shifted Taylor polynomial
`T = (P.taylor (trunc N f))(X ^ N * Y)` where `N = s + 1` and `s = order (P'(f))`. -/
private theorem taylor_comp_X_pow_dvd {K : Type*} [Field K] {f : K⟦X⟧} {P : K[X][X]}
    (hf : Polynomial.aeval f P = 0) (hfd : Polynomial.aeval f P.derivative ≠ 0) :
    ∃ (s : ℕ) (T : K[X][X]),
      let N : ℕ := s + 1
      s = (Polynomial.aeval f P.derivative).order.toNat ∧
      Polynomial.aeval (mk fun n ↦ coeff (n + N) f) T = 0 ∧
      (T.coeff 1).coeff (N + s) = coeff s (Polynomial.aeval f P.derivative) ∧
      (∀ {k : ℕ}, 2 ≤ k → Polynomial.X ^ (N + s + 1) ∣ T.coeff k) ∧
      (∀ k, Polynomial.X ^ (N + s) ∣ T.coeff k) := by
  let s : ℕ := (Polynomial.aeval f P.derivative).order.toNat
  let N : ℕ := s + 1
  let b : K[X] := trunc N f
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  let T : K[X][X] := (P.taylor b).comp (Polynomial.C (Polynomial.X ^ N) * Polynomial.X)
  have hT_eval : Polynomial.aeval g T = 0 := by
    dsimp [T, b, g]
    rw [aeval_taylor_comp_X_pow_mul, add_comm, ← PowerSeries.eq_X_pow_mul_shift_add_trunc N f, hf]
  have hT_coeff (k : ℕ) : T.coeff k = (P.taylor b).coeff k * Polynomial.X ^ (N * k) := by
    dsimp [T, b]; rw [Polynomial.comp_C_mul_X_coeff, pow_mul]
  have hT1_eq : T.coeff 1 = Polynomial.eval b P.derivative * Polynomial.X ^ N := by
    rw [hT_coeff 1, mul_one, Polynomial.taylor_coeff_one]
  have hT1_dvd : Polynomial.X ^ (N + s) ∣ T.coeff 1 := by
    rw [hT1_eq, pow_add, mul_comm (Polynomial.X ^ N)]
    refine mul_dvd_mul_right (Polynomial.X_pow_dvd_iff.mpr fun i hi ↦ ?_) _
    rw [coeff_eval_trunc P.derivative f (hi.trans (Nat.lt_succ_self s))]
    exact coeff_of_lt_order i (by
      rw [← ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hfd)]
      exact Nat.cast_lt.mpr hi)
  have hT1_coeff : (T.coeff 1).coeff (N + s) = coeff s (Polynomial.aeval f P.derivative) := by
    rw [hT1_eq, mul_comm, Polynomial.coeff_X_pow_mul', ite_eq_left (Nat.le_add_right N s),
      add_comm N s, Nat.add_sub_cancel, coeff_eval_trunc P.derivative f (Nat.lt_succ_self s)]
  have hT_ge_dvd {k : ℕ} (hk : 2 ≤ k) : Polynomial.X ^ (N + s + 1) ∣ T.coeff k := by
    rw [hT_coeff k]
    have hNs : N + s + 1 ≤ N * k := by dsimp [N]; nlinarith
    exact dvd_mul_of_dvd_right (pow_dvd_pow Polynomial.X hNs) _
  refine ⟨s, T, rfl, hT_eval, hT1_coeff, fun hk ↦ hT_ge_dvd hk, fun k ↦ ?_⟩
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
  obtain ⟨s, T, hs, hT_eval, hT1_coeff, hT_ge_dvd, hTdvd⟩ := taylor_comp_X_pow_dvd hf hfd
  let N : ℕ := s + 1
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  have hfg : f = (trunc N f : K⟦X⟧) + X ^ N * g := by
    simpa only [add_comm] using PowerSeries.eq_X_pow_mul_shift_add_trunc N f
  obtain ⟨Q, hTQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff (Polynomial.X ^ (N + s)) T).mpr hTdvd
  have hQcoeff (k : ℕ) : Polynomial.X ^ (N + s) * Q.coeff k = T.coeff k := by
    rw [← Polynomial.coeff_C_mul, ← hTQ]
  have hQ_eval : Polynomial.aeval g Q = 0 := by
    have hmul : X ^ (N + s) * Polynomial.aeval g Q = 0 := by
      have := hT_eval
      rwa [hTQ, map_mul, Polynomial.aeval_C, algebraMap_polynomial_powerSeries, Polynomial.coe_pow,
        Polynomial.coe_X] at this
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  refine ⟨N, Q, by omega, hfg, hQ_eval, ?_, ?_⟩
  · have h1 := congrArg (fun p : K[X] ↦ p.coeff (N + s)) (hQcoeff 1)
    rw [Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, hT1_coeff, hs] at h1
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
    have hcomp : (constantCoeff : K⟦X⟧ →+* K).comp (algebraMap K[X] K⟦X⟧) = ev0 :=
      RingHom.ext fun p ↦ by
        simp [algebraMap_polynomial_powerSeries, ev0, Polynomial.coeff_zero_eq_eval_zero]
    have hc := congrArg constantCoeff hQ_eval
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval_map,
      hQ0_map] at hc
    simpa [g₀] using hc
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
    rw [← pow_one Polynomial.X, Polynomial.X_pow_dvd_iff]
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
  obtain ⟨R, hQ2_eq⟩ :=
    (Polynomial.C_dvd_iff_dvd_coeff Polynomial.X (Polynomial.X - Q₂)).mpr hQ2_sub_dvd
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
      1 ≤ N ∧ f = (trunc N f : K⟦X⟧) + X ^ N * (C g₀ + u) ∧ coeff 0 u = 0 ∧
        u = X * Polynomial.aeval u R := by
  obtain ⟨N, Q, hN, hfg, hQ_eval, hQ1, hQ_ge⟩ :=
    exists_div_X_pow_eq_zero_of_aeval_eq_zero hf hfd
  let g : K⟦X⟧ := mk fun n ↦ coeff (n + N) f
  obtain ⟨R, huR⟩ := exists_eq_X_mul_aeval_of_linear_const hQ_eval hQ1 hQ_ge
  refine ⟨N, constantCoeff g, g - C (constantCoeff g), R, hN, ?_, by simp, huR⟩
  simpa [sub_add_cancel] using hfg

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
