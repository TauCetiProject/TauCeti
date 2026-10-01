/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Exponential
public import TauCeti.NumberTheory.LocalField.Logarithm
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.Valuation.Polynomial
import TauCeti.Topology.Algebra.ValuativeRel.HasSum

/-!
# The exponential and the logarithm are inverse on deep units

Let `K` be a finite extension of `ℚ_[p]` with absolute ramification index `e`, and let `i` be a
depth with `e < (p - 1) * i`. The exponential series converges on `𝓂[K] ^ i`
(`TauCeti.hasSum_exp_of_mem_maximalIdeal_pow`) and the logarithm series converges on `U(K,i)`
(`TauCeti.hasSum_log_of_mem_unitFiltration_one`). This file proves that Mathlib's
`NormedSpace.exp` and `NormedSpace.log` restrict to mutually inverse bijections

`exp : 𝓂[K] ^ i → U(K,i)`, `log : U(K,i) → 𝓂[K] ^ i`.

These are the two inverse identities of the deep-unit logarithm: they make `exp` and `log`
mutually inverse bijections between `𝓂[K] ^ i` and `U(K,i)`. Identifying these as groups
additionally needs the homomorphism property of the logarithm, which this file does not prove.

## Main results

* `TauCeti.valuation_exp_sub_one`: `v(exp x - 1) = v(x)` for `x ∈ 𝓂[K] ^ i`.
* `TauCeti.exists_mem_unitFiltration_eq_exp`: `exp x` is a unit in `U(K,i)` for
  `x ∈ 𝓂[K] ^ i`.
* `TauCeti.log_exp_of_mem_maximalIdeal_pow`: `log (exp x) = x` for `x ∈ 𝓂[K] ^ i`.
* `TauCeti.exp_log_of_mem_unitFiltration`: `exp (log u) = u` for `u ∈ U(K,i)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.5).
-/

public section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField NormedSpace

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p] {i : ℕ}

section Bounds

variable (K p) in
/-- The `(p - 1)`-st power of the valuation of `K`. Its values are the `(p - 1)`-st powers of
the values of `valuation K`, so rational depths with denominator `p - 1` become integral. -/
private noncomputable def powValuation : Valuation K (ValueGroupWithZero K) :=
  (valuation K).map
    { powMonoidWithZeroHom (M₀ := ValueGroupWithZero K)
        (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt) with
      monotone' := fun _ _ h => pow_le_pow_left₀ zero_le h _ }

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FinitePadicExtension K p] in
private theorem powValuation_apply (x : K) :
    powValuation K p x = valuation K x ^ (p - 1) := rfl

/-- The weighted bound on the terms of the exponential series at a deep element: measured by
`powValuation`, the `m`-th term of `exp - 1` at `x` is at most `v(x) ^ (p - 1) * S ^ (m - 1)`. -/
private theorem powValuation_coeff_exp_sub_one_mul_pow_le [CharZero K] {π : 𝒪[K]}
    (hπ : Irreducible π)
    (hi : absoluteRamificationIndex K p < (p - 1) * i) {x : K}
    (hx : valuation K x ≤ valuation K (π : K) ^ i) (m : ℕ) :
    powValuation K p (PowerSeries.coeff m (PowerSeries.exp K - 1) * x ^ m) *
        valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) ≤
      powValuation K p x *
        (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hfac : (m.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hcoeff : PowerSeries.coeff m (PowerSeries.exp K - 1) * x ^ m * m.factorial = x ^ m := by
    simp [PowerSeries.coeff_exp, PowerSeries.coeff_one, hm]
    field_simp
  have hv : valuation K (m.factorial : K) ≠ 0 := by simpa using hfac
  simp only [powValuation_apply]
  refine le_of_mul_le_mul_right ?_ (pow_pos (zero_lt_iff.mpr hv) (p - 1))
  calc valuation K (PowerSeries.coeff m (PowerSeries.exp K - 1) * x ^ m) ^ (p - 1) *
          valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) *
          valuation K (m.factorial : K) ^ (p - 1)
      = valuation K x ^ (m * (p - 1)) *
          valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) := by
        rw [mul_right_comm, ← mul_pow, ← map_mul, hcoeff, map_pow, ← pow_mul]
    _ ≤ valuation K x ^ (p - 1) *
          (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ m *
          valuation K (π : K) ^
            ((p - 1) * (absoluteRamificationIndex K p * padicValNat p m.factorial)) :=
        pow_mul_pow_le_of_le (Valuation.integer.v_irreducible_lt_one hπ).le hx hi.le
          (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hm)
    _ = valuation K x ^ (p - 1) *
          (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ m *
          valuation K (m.factorial : K) ^ (p - 1) := by
        rw [valuation_natCast_eq_pow_mul_padicValNat p hπ m.factorial_ne_zero, ← pow_mul,
          ← pow_mul, mul_comm (absoluteRamificationIndex K p * _) (p - 1)]

/-- The weighted bound on the coefficients of the logarithm series: measured by
`powValuation`, `c_n * v(x) ^ n ≤ v(x) * S ^ (n - 1)` for `c_n = (-1) ^ (n + 1) / n`. -/
private theorem powValuation_coeff_log_mul_pow_le [CharZero K] {π : 𝒪[K]}
    (hπ : Irreducible π)
    (hi : absoluteRamificationIndex K p < (p - 1) * i) {x : K}
    (hx : valuation K x ≤ valuation K (π : K) ^ i) (n : ℕ) :
    powValuation K p (PowerSeries.coeff n (PowerSeries.log K)) * powValuation K p x ^ n *
        valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) ≤
      powValuation K p x *
        (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcoeff :
      valuation K (PowerSeries.coeff n (PowerSeries.log K)) * valuation K (n : K) = 1 := by
    rw [← map_mul]
    simp [PowerSeries.coeff_log, hn, hnK]
  have hv : valuation K (n : K) ≠ 0 := by simpa using hnK
  -- `(p - 1) * v_p(n) < n`, since `p ^ v_p(n)` divides `n`.
  have hq : (p - 1) * padicValNat p n < n := by
    have h : p * padicValNat p n ≤ n := mul_padicValNat_le
    have hp := (Fact.out : p.Prime).one_lt
    rw [Nat.sub_one_mul]
    rcases Nat.eq_zero_or_pos (padicValNat p n) with h0 | h0
    · simp [h0, Nat.pos_of_ne_zero hn]
    · omega
  simp only [powValuation_apply]
  refine le_of_mul_le_mul_right ?_ (pow_pos (zero_lt_iff.mpr hv) (p - 1))
  calc valuation K (PowerSeries.coeff n (PowerSeries.log K)) ^ (p - 1) *
          (valuation K x ^ (p - 1)) ^ n *
          valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) *
          valuation K (n : K) ^ (p - 1)
      = valuation K x ^ (n * (p - 1)) *
          valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) := by
        rw [mul_right_comm, mul_right_comm _ (_ ^ n), ← mul_pow, hcoeff, one_pow, one_mul,
          ← pow_mul, mul_comm (p - 1)]
    _ ≤ valuation K x ^ (p - 1) *
          (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ n *
          valuation K (π : K) ^ ((p - 1) * (absoluteRamificationIndex K p * padicValNat p n)) :=
        pow_mul_pow_le_of_le (Valuation.integer.v_irreducible_lt_one hπ).le hx hi.le hq
    _ = valuation K x ^ (p - 1) *
          (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ n *
          valuation K (n : K) ^ (p - 1) := by
        rw [valuation_natCast_eq_pow_mul_padicValNat p hπ hn, ← pow_mul, ← pow_mul,
          mul_comm (absoluteRamificationIndex K p * _) (p - 1)]

end Bounds

/-- On `𝓂[K] ^ i` with `(p - 1) * i > e`, the exponential series at `x` is `1` plus the series
`exp - 1` at `x`. -/
private theorem hasSum_coeff_exp_sub_one_mul_pow [CharZero K]
    (hi : absoluteRamificationIndex K p < (p - 1) * i) (x : (𝓂[K] ^ i : Ideal 𝒪[K])) :
    HasSum (fun m => PowerSeries.coeff m (PowerSeries.exp K - 1) * (x : K) ^ m)
      (exp (x : K) - 1) := by
  convert (hasSum_exp_of_mem_maximalIdeal_pow x hi).sub (hasSum_ite_eq 0 (1 : K)) using 1
  funext m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp [PowerSeries.coeff_exp, PowerSeries.coeff_one, hm, div_eq_inv_mul]

/-- The valuation of an element of `𝓂[K] ^ i`, for a uniformizer `π`, is at most `v(π) ^ i`. -/
private theorem valuation_le_pow_of_mem_maximalIdeal_pow {π : 𝒪[K]} (hπ : Irreducible π)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) : valuation K (x : K) ≤ valuation K (π : K) ^ i :=
  (Set.ext_iff.mp (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) i) x).mp x.2

/-- On `𝓂[K] ^ i` with `(p - 1) * i > e`, the exponential preserves the valuation of its
argument: `v(exp x - 1) = v(x)`. -/
theorem valuation_exp_sub_one (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) :
    valuation K (exp (x : K) - 1) = valuation K (x : K) := by
  have := FinitePadicExtension.charZero K p
  rcases eq_or_ne (x : K) 0 with hx | hx
  · simp [hx, exp_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hxv := valuation_le_pow_of_mem_maximalIdeal_pow hπ x
  have hvx : valuation K (x : K) ≠ 0 := by simpa using hx
  set f := fun m => PowerSeries.coeff m (PowerSeries.exp K - 1) * (x : K) ^ m with hf_def
  have hf := hasSum_coeff_exp_sub_one_mul_pow hi x
  have hf1 : PowerSeries.coeff 1 (PowerSeries.exp K - 1) * (x : K) ^ 1 = x := by
    simp [PowerSeries.coeff_exp, PowerSeries.coeff_one]
  have hS1 : valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) < 1 :=
    pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ) (by omega)
  have hS0 : valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) ≠ 0 :=
    pow_ne_zero _ (by simpa using hπ.ne_zero)
  -- Every term other than the linear one is strictly smaller than `x`.
  have hlt : ∀ m, valuation K (Function.update f 1 0 m) < valuation K (x : K) := by
    intro m
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa [zero_lt_iff] using hvx
    rw [Function.update_of_ne hm1]
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa [hf_def, zero_lt_iff] using hvx
    have hb := powValuation_coeff_exp_sub_one_mul_pow_le hπ hi hxv m
    have hSm : (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ m =
        (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ (m - 1) *
          valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
    rw [hSm, ← mul_assoc, mul_le_mul_iff_left₀ (zero_lt_iff.mpr hS0)] at hb
    have hpow : powValuation K p (f m) < powValuation K p (x : K) :=
      hb.trans_lt (mul_lt_of_lt_one_right (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))
        (pow_lt_one₀ zero_le hS1 (by omega)))
    rw [powValuation_apply, powValuation_apply] at hpow
    exact lt_of_pow_lt_pow_left₀ (p - 1) zero_le hpow
  have hsum := valuation_lt_of_hasSum (hf.update 1 0) (Units.mk0 _ hvx) hlt
  rw [hf1, zero_sub, neg_add_eq_sub] at hsum
  rw [← sub_add_cancel (exp (x : K) - 1) (x : K), add_comm]
  exact Valuation.map_add_eq_of_lt_left _ hsum

/-- On `𝓂[K] ^ i` with `(p - 1) * i > e`, the exponential lands in the unit filtration
`U(K,i)`. -/
theorem exists_mem_unitFiltration_eq_exp (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) :
    ∃ u ∈ unitFiltration K i, (u : K) = exp (x : K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hv := (valuation_exp_sub_one hi x).trans_le
    (valuation_le_pow_of_mem_maximalIdeal_pow hπ x)
  have hne : exp (x : K) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, map_one] at hv
    exact hv.not_gt (pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ) hi0)
  exact ⟨Units.mk0 _ hne, (mem_unitFiltration_iff_valuation_sub_one_le hi0 hπ).mpr hv, rfl⟩

/-- At a deep `x`, the composite of the truncation of the logarithm series below degree
`M` after the truncation of `exp - 1` below degree `N` is `x` up to
`v(x) ^ (p - 1) * S ^ (min M N - 1)`, measured by `powValuation`. -/
private theorem powValuation_eval_trunc_log_eval_trunc_exp_sub_one_sub_le [CharZero K]
    {π : 𝒪[K]} (hπ : Irreducible π) (hi : absoluteRamificationIndex K p < (p - 1) * i) {x : K}
    (hxv : valuation K x ≤ valuation K (π : K) ^ i) (M N : ℕ) :
    powValuation K p ((PowerSeries.trunc M (PowerSeries.log K)).eval
        ((PowerSeries.trunc N (PowerSeries.exp K - 1)).eval x) - x) *
        valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) ≤
      powValuation K p x *
        (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ min M N := by
  set S := valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)
  set F := PowerSeries.trunc M (PowerSeries.log K)
  set Q := PowerSeries.trunc N (PowerSeries.exp K - 1)
  have hS0 : S ≠ 0 := pow_ne_zero _ (by simpa using hπ.ne_zero)
  have hQ : ∀ k, powValuation K p (Q.coeff k * x ^ k) * S ≤ powValuation K p x * S ^ k := by
    intro k
    rw [PowerSeries.coeff_trunc]
    split_ifs
    · exact powValuation_coeff_exp_sub_one_mul_pow_le hπ hi hxv k
    · simp
  have hF : ∀ n, powValuation K p (F.coeff n) * powValuation K p x ^ n * S ≤
      powValuation K p x * S ^ n := by
    intro n
    rw [PowerSeries.coeff_trunc]
    split_ifs
    · exact powValuation_coeff_log_mul_pow_le hπ hi hxv n
    · simp
  have hX : ∀ k, powValuation K p ((Polynomial.X : Polynomial K).coeff k * x ^ k) * S ≤
      powValuation K p x * S ^ k := by
    intro k
    rw [Polynomial.coeff_X]
    split_ifs with h
    · subst h
      simp
    · simp
  have hG : (F.comp Q - Polynomial.X).eval x = F.eval (Q.eval x) - x := by
    simp [Polynomial.eval_comp]
  rw [← hG]
  -- `F ∘ Q - X` vanishes below degree `min M N` and has weight `1`.
  refine Valuation.map_eval_mul_le (pow_le_one₀ zero_le
    (Valuation.integer.v_irreducible_lt_one hπ).le) (fun k hk => ?_) (fun k => ?_)
  · rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc_log_comp_trunc_exp_sub_one
      (lt_min_iff.mp hk).1 (lt_min_iff.mp hk).2, sub_self]
  · have hcomp := Valuation.map_coeff_comp_mul_pow_le hF hQ k
    have hXk := hX k
    rw [Polynomial.coeff_sub, sub_mul]
    rw [← le_div_iff₀ (zero_lt_iff.mpr hS0)] at hcomp hXk ⊢
    exact Valuation.map_sub_le _ hcomp hXk

/-- Letting the truncation degree of `exp - 1` tend to infinity in
`powValuation_eval_trunc_log_eval_trunc_exp_sub_one_sub_le`: the truncation of the logarithm
series below degree `M`, evaluated at `exp x - 1`, is `x` up to `v(x) ^ (p - 1) * S ^ (M - 1)`. -/
private theorem powValuation_eval_trunc_log_exp_sub_one_sub_le [CharZero K] {π : 𝒪[K]}
    (hπ : Irreducible π) (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) (M : ℕ) :
    powValuation K p ((PowerSeries.trunc M (PowerSeries.log K)).eval (exp (x : K) - 1) - x) *
        valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p) ≤
      powValuation K p (x : K) *
        (valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)) ^ M := by
  set F := PowerSeries.trunc M (PowerSeries.log K)
  rcases eq_or_ne (F.eval (exp (x : K) - 1) - x) 0 with h0 | h0
  · simp [h0, powValuation_apply, zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)]
  -- The truncations of `exp - 1` at `x` converge to `exp x - 1`.
  have hE : Tendsto (fun N => (PowerSeries.trunc N (PowerSeries.exp K - 1)).eval (x : K)) atTop
      (𝓝 (exp (x : K) - 1)) := by
    refine (hasSum_coeff_exp_sub_one_mul_pow hi x).tendsto_sum_nat.congr fun N => ?_
    simp only [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range, RingHom.id_apply]
  have hlim : Tendsto (fun N => F.eval ((PowerSeries.trunc N (PowerSeries.exp K - 1)).eval
      (x : K)) - x) atTop (𝓝 (F.eval (exp (x : K) - 1) - x)) :=
    ((F.continuous.tendsto _).comp hE).sub_const _
  -- A valuation is locally constant away from `0`, so the bound passes to the limit.
  obtain ⟨N, hN, hMN⟩ := ((hlim.eventually ((valuation K).locally_const
    (by simpa using h0))).and (eventually_ge_atTop M)).exists
  have h := powValuation_eval_trunc_log_eval_trunc_exp_sub_one_sub_le hπ hi
    (valuation_le_pow_of_mem_maximalIdeal_pow hπ x) M N
  rwa [min_eq_left hMN, powValuation_apply, hN, ← powValuation_apply] at h

/-- **The logarithm inverts the exponential on deep elements.** On `𝓂[K] ^ i` with
`(p - 1) * i > e`, `log (exp x) = x`. -/
theorem log_exp_of_mem_maximalIdeal_pow (hi : absoluteRamificationIndex K p < (p - 1) * i)
    (x : (𝓂[K] ^ i : Ideal 𝒪[K])) : log (exp (x : K)) = x := by
  have := FinitePadicExtension.charZero K p
  rcases eq_or_ne (x : K) 0 with hx | hx
  · simp [hx, exp_zero, log_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set S := valuation K (π : K) ^ ((p - 1) * i - absoluteRamificationIndex K p)
  set A := powValuation K p (x : K)
  have hS1 : S < 1 := pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one hπ) (by omega)
  have hA0 : A ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  -- The truncations of the logarithm series at `exp x - 1` converge to `log (exp x)`.
  have hL : Tendsto (fun M => (PowerSeries.trunc M (PowerSeries.log K)).eval (exp (x : K) - 1))
      atTop (𝓝 (log (exp (x : K)))) := by
    obtain ⟨u, hu, hux⟩ := exists_mem_unitFiltration_eq_exp hi x
    have h := hasSum_log_of_mem_unitFiltration_one p
      (unitFiltration_antitone (Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hi)) hu)
    rw [hux] at h
    refine h.tendsto_sum_nat.congr fun M => ?_
    simp only [Polynomial.eval, PowerSeries.eval₂_trunc_eq_sum_range, RingHom.id_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_log, hn]
  -- A nonzero `log (exp x) - x` would violate the bound `A * S ^ M` for large `M`.
  by_contra hne
  have hy : log (exp (x : K)) - x ≠ 0 := sub_ne_zero.mpr hne
  have hyS : powValuation K p (log (exp (x : K)) - x) * S / A ≠ 0 :=
    div_ne_zero (mul_ne_zero ((Valuation.ne_zero_iff _).mpr hy)
      (pow_ne_zero _ (by simpa using hπ.ne_zero))) hA0
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ hS1 (Units.mk0 _ hyS)
  obtain ⟨M, hM, hMM₀⟩ := (((hL.sub_const (x : K)).eventually ((valuation K).locally_const
    (by simpa using hy))).and (eventually_ge_atTop M₀)).exists
  have h := powValuation_eval_trunc_log_exp_sub_one_sub_le hπ hi x M
  rw [powValuation_apply, hM, ← powValuation_apply] at h
  have hlt : A * S ^ M < powValuation K p (log (exp (x : K)) - x) * S :=
    calc A * S ^ M ≤ A * S ^ M₀ := mul_le_mul_right (pow_le_pow_right_of_le_one' hS1.le hMM₀) A
      _ < A * (powValuation K p (log (exp (x : K)) - x) * S / A) :=
        mul_lt_mul_of_pos_left hM₀ (zero_lt_iff.mpr hA0)
      _ = powValuation K p (log (exp (x : K)) - x) * S := mul_div_cancel₀ _ hA0
  exact (h.trans_lt hlt).false

/-- **The exponential inverts the logarithm on deep units.** On `U(K,i)` with `(p - 1) * i > e`,
`exp (log u) = u`. -/
theorem exp_log_of_mem_unitFiltration (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) : exp (log (u : K)) = u := by
  obtain ⟨z, hz, hzu⟩ := exists_mem_maximalIdeal_pow_eq_log hi hu
  obtain ⟨w, hw, hwz⟩ := exists_mem_unitFiltration_eq_exp hi ⟨z, hz⟩
  have hlog := log_exp_of_mem_maximalIdeal_pow hi ⟨z, hz⟩
  have hwu : (⟨w, hw⟩ : unitFiltration K i) = ⟨u, hu⟩ :=
    log_unitFiltration_injective hi (by simpa [hwz, ← hzu] using hlog)
  rw [← hzu, ← hwz]
  exact congrArg (fun t : unitFiltration K i => ((t : Kˣ) : K)) hwu

end TauCeti
