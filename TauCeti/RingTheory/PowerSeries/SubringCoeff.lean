/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.PowerSeries.Basic
import TauCeti.RingTheory.PowerSeries.Evaluation
import TauCeti.RingTheory.PowerSeries.Rescale
import TauCeti.RingTheory.PowerSeries.Trunc

/-!
# Power series with coefficients in a subring: division and expansion

Let `R` be a subring of a ring `S`, and let `D` be a power series over `S` with coefficients in
`R` whose first nonzero coefficient, in degree `m`, is `1`; that is, `D = Xᵐ u` with `u(0) = 1`.
If `F * D` has coefficients in `R`, then so does `F` (`PowerSeries.coeff_mem_of_coeff_mul_mem`):
the coefficients of `F` are solved for recursively from those of `F * D`.

This is how integrality of `q`-expansions passes through division by a modular form such as the
discriminant `Δ = q + ⋯`, whose `q`-expansion has integer coefficients.

A power series lies in the image of `PowerSeries.map f` exactly when each of its coefficients
lies in the range of `f` (`PowerSeries.mem_map_range`), so the same division statement applies
to images of power series over another ring.

Substituting `Xᵖ` for `X` (`PowerSeries.expand`) only spreads the coefficients out and inserts
zeros, so it neither creates nor destroys coefficients in `R`
(`PowerSeries.forall_coeff_expand_mem_iff`). This is how integrality of a `q`-expansion is
unchanged when it is read in a power of `q`, for instance at a multiple of the cusp width.

Similarly, an algebraic power series `f ∈ K⟦X⟧` annihilated by `P ∈ K[X][Y]` with `P_Y(f) ≠ 0`
admits a tail decomposition `f = trunc N f + X ^ N * (C g₀ + u)` satisfying a recurrence
`u = X * R(X, u)` (`PowerSeries.exists_tail_eq_X_mul_aeval_of_aeval_eq_zero`), from which
subring membership (`PowerSeries.coeff_mem_subring_of_eq_X_mul_aeval`) and scaled integrality
(`PowerSeries.isIntegral_pow_mul_coeff_of_eq_X_mul_aeval`) follow inductively.

## Main results

* `PowerSeries.mem_map_range`: the range of `PowerSeries.map f` consists of the power series whose
  coefficients all lie in the range of `f`.
* `PowerSeries.coeff_mem_of_coeff_mul_mem`: if `F * D` and `D = Xᵐ u`, `u(0) = 1`, have
  coefficients in `R`, then so does `F`.
* `PowerSeries.forall_coeff_expand_mem_iff`: `expand p φ` has coefficients in `R` if and only if
  `φ` does.
* `PowerSeries.coeff_mem_subring_of_eq_X_mul_aeval`: if `u = X * P(X, u)` with `P` having
  coefficients in a subring `R`, then all coefficients of `u` lie in `R`.
* `PowerSeries.isIntegral_pow_mul_coeff_of_eq_X_mul_aeval`: rescaling `u = X * R(X, u)` by `M`
  clearing the coefficients of `R` makes `Mⁿ * coeff n u` integral over `ℤ`.
* `PowerSeries.exists_eq_X_mul_aeval_of_linear_const`: a series annihilated by `Q ∈ K[X][Y]`
  with linear constant term `(Q.coeff 1)(0) ≠ 0` and `(Q.coeff k)(0) = 0` for `k ≥ 2` satisfies
  `g - C (constantCoeff g) = X * R(X, g - C (constantCoeff g))`.
* `PowerSeries.exists_tail_eq_X_mul_aeval_of_aeval_eq_zero`: the Bilu–Borichev tail-series
  reduction of an equation `P(f) = 0` with `P_Y(f) ≠ 0` to `u = X * R(X, u)`.
-/

public section

namespace PowerSeries

section Ring

variable {S : Type*} [Ring S] {R : Subring S}

/-- The range of `PowerSeries.map f` consists of the power series whose coefficients all lie in
the range of `f`. -/
theorem mem_map_range {T : Type*} [Ring T] (f : T →+* S) {p : S⟦X⟧} :
    p ∈ (map f).range ↔ ∀ n, coeff n p ∈ f.range := by
  refine ⟨fun ⟨q, hq⟩ n ↦ ⟨coeff n q, by rw [← hq, coeff_map]⟩, fun h ↦ ?_⟩
  choose g hg using h
  exact ⟨mk g, by ext n; simp [hg]⟩

/-- **Division by `Xᵐ u` with `u(0) = 1` preserves coefficients in a subring.** If `D` has
coefficients in `R`, vanishes below degree `m` and has coefficient `1` in degree `m`, and `F * D`
has coefficients in `R`, then `F` has coefficients in `R`. -/
theorem coeff_mem_of_coeff_mul_mem {m : ℕ} {F D : S⟦X⟧} (hD : ∀ i < m, coeff i D = 0)
    (hDm : coeff m D = 1) (hDR : ∀ i, coeff i D ∈ R) (hFD : ∀ n, coeff n (F * D) ∈ R) (n : ℕ) :
    coeff n F ∈ R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hmem : (n, m) ∈ Finset.antidiagonal (n + m) := Finset.mem_antidiagonal.mpr rfl
  have h := hFD (n + m)
  rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem, hDm, mul_one] at h
  -- every other term involves an earlier coefficient of `F` or a vanishing coefficient of `D`
  refine (add_mem_cancel_right (R.sum_mem fun p hp ↦ ?_)).mp h
  obtain ⟨hpne, hp⟩ := Finset.mem_erase.mp hp
  have hsum : p.1 + p.2 = n + m := Finset.mem_antidiagonal.mp hp
  rcases lt_trichotomy p.1 n with hlt | heq | hgt
  · exact R.mul_mem (ih _ hlt) (hDR _)
  · exact absurd (Prod.ext heq (by omega)) hpne
  · rw [hD _ (by omega), mul_zero]
    exact R.zero_mem

end Ring

/-- **Expansion preserves and reflects coefficients in a subring.** The coefficients of
`expand p φ`, the power series `φ` with `Xᵖ` substituted for `X`, all lie in a subring `R` if and
only if those of `φ` do. -/
@[simp]
theorem forall_coeff_expand_mem_iff {S : Type*} [CommRing S] {R : Subring S} {p : ℕ}
    (hp : p ≠ 0) {φ : S⟦X⟧} : (∀ n, coeff n (expand p hp φ) ∈ R) ↔ ∀ n, coeff n φ ∈ R := by
  refine ⟨fun h n ↦ by simpa using h (p * n), fun h n ↦ ?_⟩
  rw [coeff_expand]
  split_ifs
  · exact h _
  · exact R.zero_mem

/-- If `u ∈ S⟦X⟧` satisfies `u = X * P(X, u)` for a bivariate polynomial `P ∈ S[X][Y]` whose
coefficients all lie in a subring `R ⊆ S`, then every coefficient of `u` lies in `R`. -/
theorem coeff_mem_subring_of_eq_X_mul_aeval {S : Type*} [CommRing S] {R : Subring S}
    {u : S⟦X⟧} {P : Polynomial (Polynomial S)} (hu : u = X * Polynomial.aeval u P)
    (hP : ∀ j i, (P.coeff j).coeff i ∈ R) (n : ℕ) : coeff n u ∈ R := by
  have hpow : ∀ m, (∀ k ≤ m, coeff k u ∈ R) → ∀ j k, k ≤ m → coeff k (u ^ j) ∈ R := by
    intro m hm j
    induction j with
    | zero =>
      intro k _
      rw [pow_zero, coeff_one]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    | succ j ih =>
      intro k hk
      rw [pow_succ, coeff_mul]
      refine R.sum_mem fun p hp ↦ ?_
      exact R.mul_mem (ih p.1 ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hk))
        (hm p.2 ((Finset.HasAntidiagonal.antidiagonal.snd_le hp).trans hk))
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [hu, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
      exact R.zero_mem
    · have hcoeff := congrArg (coeff (m + 1)) hu
      rw [coeff_succ_X_mul, Polynomial.aeval_eq_sum_range, map_sum] at hcoeff
      rw [hcoeff]
      refine R.sum_mem fun j _ ↦ ?_
      rw [Algebra.smul_def, algebraMap_polynomial_powerSeries, coeff_mul]
      refine R.sum_mem fun p hp ↦ ?_
      rw [Polynomial.coeff_coe]
      exact R.mul_mem (hP j p.1)
        (hpow m (fun k hk ↦ ih k (by omega)) j p.2 (Finset.HasAntidiagonal.antidiagonal.snd_le hp))

/-- Rescaling the recurrence `u = X * R(X, u)` by a natural number `M` clearing the coefficients
of `R` makes `Mⁿ * coeff n u` integral over `ℤ` for all `n`. -/
theorem isIntegral_pow_mul_coeff_of_eq_X_mul_aeval {K : Type*} [CommRing K] {u : K⟦X⟧}
    {R : Polynomial (Polynomial K)} (hu : u = X * Polynomial.aeval u R) (M : ℕ)
    (hRM : ∀ j i, IsIntegral ℤ ((M : K) * (R.coeff j).coeff i)) (n : ℕ) :
    IsIntegral ℤ ((M : K) ^ n * coeff n u) := by
  let R' : Polynomial (Polynomial K) := Polynomial.C (Polynomial.C (M : K)) *
    R.map (Polynomial.compRingHom (Polynomial.C (M : K) * Polynomial.X))
  have hrescale_coe (p : Polynomial K) :
      rescale (M : K) (p : K⟦X⟧) =
        ((p.comp (Polynomial.C (M : K) * Polynomial.X) : Polynomial K) : K⟦X⟧) := by
    ext k
    rw [coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.comp_C_mul_X_coeff, mul_comm]
  have huM : rescale (M : K) u = X * Polynomial.aeval (rescale (M : K) u) R' := by
    have h := congrArg (rescale (M : K)) hu
    rw [map_mul, rescale_X, mul_assoc, mul_left_comm (C (M : K)) X] at h
    have heq : (rescale (M : K)).comp (algebraMap (Polynomial K) K⟦X⟧) =
        (algebraMap (Polynomial K) K⟦X⟧).comp
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
  have hmem := coeff_mem_subring_of_eq_X_mul_aeval (R := (integralClosure ℤ K).toSubring) huM hR' n
  rwa [Subalgebra.mem_toSubring, mem_integralClosure_iff, coeff_rescale] at hmem

section TailRecurrence

open scoped Polynomial

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
theorem exists_eq_X_mul_aeval_of_linear_const {K : Type*} [Field K] {g : K⟦X⟧}
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
  have hQ2_sub_map : (Polynomial.X - Q₂).map (Polynomial.evalRingHom 0) = 0 := by
    simp [hQ2_map]
  have hQ2_sub_dvd (k : ℕ) : Polynomial.X ∣ (Polynomial.X - Q₂).coeff k := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom,
      ← Polynomial.coeff_map, hQ2_sub_map, Polynomial.coeff_zero]
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
theorem exists_tail_eq_X_mul_aeval_of_aeval_eq_zero {K : Type*} [Field K] {f : K⟦X⟧}
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

end TailRecurrence

end PowerSeries
