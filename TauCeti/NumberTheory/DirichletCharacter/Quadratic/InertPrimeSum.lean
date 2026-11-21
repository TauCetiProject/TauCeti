/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.Chebyshev
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.InertPrimeSum.Determinant
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.PrimitiveDiscriminant

/-!
# Inert-prime sum bound via the determinant method

For a quadratic Dirichlet character `χ` of level `q ≠ 0` (with values in any commutative ring where
`2 ≠ 0`), inert primes — those with `χ(p) = -1` — carry at most three quarters of the Mertens mass
once `x ≥ q ^ 18`: `∑_{p ≤ x, χ(p) = -1} log p / p ≤ (3 / 4) log x + K`, with an absolute constant
`K` independent of `R`, `q`, `χ`, and `x`.

The determinant and `p`-adic divisibility core lives in
`TauCeti.NumberTheory.DirichletCharacter.Quadratic.InertPrimeSum.Determinant`
(`TauCeti.sum_min_div_log_le_of_jacobiSym_eq_neg_one`). Here we optimize the grid parameters
`R = ⌊x⌋₊`, `S = ⌊R / 18⌋`, `N ≈ R ^ (2 / 3)` to prove
`TauCeti.sum_primesLE_jacobiSym_eq_neg_one_log_div_le`, and transfer to quadratic Dirichlet
characters via `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`.

## Main results

* `TauCeti.sum_primesLE_jacobiSym_eq_neg_one_log_div_le`
* `DirichletCharacter.sum_primesLE_eq_neg_one_log_div_le`
* `DirichletCharacter.sum_primesLE_pow_eq_neg_one_log_div_le`

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Theorem 1.1 and §§2–6.
-/

public section

namespace TauCeti

section Assembly

private theorem sum_min_sub_ge (S k : ℕ) :
    (S : ℝ) * k - (k : ℝ) ^ 2 ≤ ∑ s : Fin S, ((min k (S - 1 - s.val) : ℕ) : ℝ) := by
  rcases le_or_gt S k with hSk | hkS
  · have : (S : ℝ) ≤ k := by exact_mod_cast hSk
    exact (show (S : ℝ) * k - (k : ℝ) ^ 2 ≤ 0 by nlinarith).trans
      (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  · let T : Finset (Fin S) := Finset.univ.filter fun s : Fin S ↦ s.val < S - k
    have hcard : T.card = S - k := by
      rw [Fin.card_filter_val_lt, min_eq_right (Nat.sub_le S k)]
    have hsumT : (S : ℝ) * k - (k : ℝ) ^ 2 = ∑ s ∈ T, ((min k (S - 1 - s.val) : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (fun s hs ↦ by
          rw [min_eq_left (by have := (Finset.mem_filter.mp hs).2; omega)]),
        Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_sub hkS.le]; ring
    rw [hsumT]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ ↦ Nat.cast_nonneg _

private theorem two_mul_sum_min_div_ge (R S p : ℕ) (hp : 0 < p) :
    (R : ℝ) ^ 2 * S / p - (R : ℝ) * S / p - 2 * R * S - 2 * (R : ℝ) ^ 3 / (p : ℝ) ^ 2 ≤
      2 * (∑ u : Fin R × Fin S, ((min (u.1.val / p) (S - 1 - u.2.val) : ℕ) : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hrow (r : Fin R) :
      (S : ℝ) * ((r.val : ℝ) / p - 1) - ((r.val : ℝ) / p) ^ 2 ≤
        ∑ s : Fin S, ((min (r.val / p) (S - 1 - s.val) : ℕ) : ℝ) := by
    refine le_trans ?_ (sum_min_sub_ge S (r.val / p))
    have hdiv_le : ((r.val / p : ℕ) : ℝ) ≤ (r.val : ℝ) / p := Nat.cast_div_le
    have hdiv_ge : (r.val : ℝ) / p - 1 ≤ ((r.val / p : ℕ) : ℝ) := by
      have hlt : r.val < p * (r.val / p + 1) := by
        have := Nat.div_add_mod r.val p; have := Nat.mod_lt r.val hp; nlinarith
      have hltR : (r.val : ℝ) < p * (((r.val / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
      rw [sub_le_iff_le_add, div_le_iff₀ hpR]; linarith
    have hsq : (((r.val / p : ℕ) : ℝ) ^ 2) ≤ ((r.val : ℝ) / p) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv_le 2
    nlinarith [Nat.cast_nonneg (α := ℝ) S]
  have hsum_r2 : ∑ r : Fin R, (r.val : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 := by
    calc ∑ r : Fin R, (r.val : ℝ) ^ 2
        ≤ ∑ _r : Fin R, (R : ℝ) ^ 2 := Finset.sum_le_sum fun r _ ↦
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast r.isLt.le) 2
      _ = (R : ℝ) ^ 3 := by simp [pow_succ, mul_assoc]
  have htot := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) ↦ hrow r
  rw [← Fintype.sum_prod_type
    (fun u : Fin R × Fin S ↦ ((min (u.1.val / p) (S - 1 - u.2.val) : ℕ) : ℝ))] at htot
  have hsimp : ∑ r : Fin R, ((S : ℝ) * ((r.val : ℝ) / p - 1) - ((r.val : ℝ) / p) ^ 2) =
      (S : ℝ) / p * (∑ r : Fin R, (r.val : ℝ)) - R * S -
        (1 / (p : ℝ) ^ 2) * ∑ r : Fin R, (r.val : ℝ) ^ 2 := by
    simp_rw [mul_sub, mul_one, div_pow, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]; ring
  rw [hsimp, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (i : ℝ)), Finset.sum_range_natCast] at htot
  have hmul2 : (1 / (p : ℝ) ^ 2) * ∑ r : Fin R, (r.val : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 / (p : ℝ) ^ 2 := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hsum_r2 (sq_nonneg _)
  have hmain : (S : ℝ) / p * ((R : ℝ) * ((R : ℝ) - 1) / 2) =
      ((R : ℝ) ^ 2 * S / p - (R : ℝ) * S / p) / 2 := by ring
  linarith [show 2 * (R : ℝ) * S = 2 * ((R : ℝ) * S) by ring,
    show 2 * (R : ℝ) ^ 3 / (p : ℝ) ^ 2 = 2 * ((R : ℝ) ^ 3 / (p : ℝ) ^ 2) by ring]

private theorem exists_grid_params {R : ℕ} (hR : 36 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ N ≤ R ∧ R ^ 2 ≤ N ^ 3 ∧ N ^ 3 ≤ 8 * R ^ 2 ∧
      N * R + N * (R / 18) + 2 * R * (R / 18) < N ^ 3 := by
  have hex : ∃ n : ℕ, R ^ 2 ≤ n ^ 3 := ⟨R, by nlinarith⟩
  classical
  let N := Nat.find hex
  have hRN : R ^ 2 ≤ N ^ 3 := Nat.find_spec hex
  have hNR : N ≤ R := Nat.find_min' hex (by nlinarith)
  have hN2 : 2 ≤ N := by
    by_contra h; have : N ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left (by omega) 3; nlinarith
  have hprev : (N - 1) ^ 3 < R ^ 2 := Nat.lt_of_not_ge (Nat.find_min hex (by omega))
  have hN8 : N ^ 3 ≤ 8 * R ^ 2 := by
    have : N ^ 3 ≤ (2 * (N - 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : (2 * (N - 1)) ^ 3 = 8 * (N - 1) ^ 3 := by ring
    omega
  have h9R : 9 * R < 4 * N ^ 2 := by
    refine lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) ?_
    calc (9 * R) ^ 3 = 729 * R ^ 3 := by ring
      _ < 64 * R * R ^ 3 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) 3)
      _ = 64 * (R ^ 2) ^ 2 := by ring
      _ ≤ 64 * (N ^ 3) ^ 2 := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hRN 2)
      _ = (4 * N ^ 2) ^ 3 := by ring
  have hS : 18 * (R / 18) ≤ R := Nat.mul_div_le R 18
  have hparam : N * R + N * (R / 18) + 2 * R * (R / 18) < N ^ 3 := by
    have : 9 * (N * R + N * (R / 18) + 2 * R * (R / 18)) < 9 * N ^ 3 := by
      have : N * (R / 18) ≤ N * R := Nat.mul_le_mul_left N (Nat.div_le_self R 18)
      have : R * (18 * (R / 18)) ≤ R ^ 2 := by nlinarith
      have : 18 * (N * R) < 8 * N ^ 3 := by nlinarith
      nlinarith
    omega
  exact ⟨N, hN2, hNR, hRN, hN8, hparam⟩

private theorem archimedean_error_le {R N : ℕ} (hN2 : 2 ≤ N) (hNR : N ≤ R)
    (hN8 : N ^ 3 ≤ 8 * R ^ 2) :
    (3 * Real.log N + 2 * N * Real.log R) / R ≤ 2 * Real.log 8 + 9 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hNRR : (N : ℝ) ≤ R := by exact_mod_cast hNR
  have h1 : 3 * Real.log N / R ≤ 3 := by
    rw [div_le_iff₀ hRpos]
    linarith [(Real.log_le_sub_one_of_pos hNpos).trans (by linarith : (N : ℝ) - 1 ≤ R)]
  have hcube : (R : ℝ) ≤ 8 * ((R : ℝ) / N) ^ 3 := by
    have h8 : (N : ℝ) ^ 3 ≤ 8 * (R : ℝ) ^ 2 := by exact_mod_cast hN8
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hNpos 3)]; nlinarith
  have hlogR : Real.log R ≤ Real.log 8 + 3 * ((R : ℝ) / N) := by
    have hqpos : 0 < (R : ℝ) / N := div_pos hRpos hNpos
    refine (Real.log_le_log hRpos hcube).trans ?_
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hqpos.ne'), Real.log_pow]
    linarith [(Real.log_le_sub_one_of_pos hqpos).trans (by linarith : (R : ℝ) / N - 1 ≤ R / N)]
  have h2 : 2 * N * Real.log R / R ≤ 2 * Real.log 8 + 6 := by
    have hNR' : (N : ℝ) / R ≤ 1 := (div_le_one hRpos).mpr hNRR
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    calc 2 * (N : ℝ) * Real.log R / R
        = 2 * ((N : ℝ) / R) * Real.log R := by ring
      _ ≤ 2 * ((N : ℝ) / R) * (Real.log 8 + 3 * ((R : ℝ) / N)) := by gcongr
      _ = 2 * ((N : ℝ) / R) * Real.log 8 + 6 := by field_simp; ring
      _ ≤ 2 * 1 * Real.log 8 + 6 := by nlinarith
      _ = 2 * Real.log 8 + 6 := by ring
  rw [add_div]; linarith

private theorem sum_filter_primesLE_le_add_odd {N : ℕ} {P : ℕ → Prop} [DecidablePred P] :
    ∑ p ∈ (Nat.primesLE N).filter P, Real.log p / p ≤
      Real.log 2 / 2 + ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ P p ∧ Odd p), Real.log p / p := by
  rw [← Finset.sum_filter_add_sum_filter_not ((Nat.primesLE N).filter P) Odd, add_comm]
  refine add_le_add ?_ ?_
  · have hsub : ((Nat.primesLE N).filter P).filter (fun p ↦ ¬ Odd p) ⊆ {2} := fun p hp ↦
      Finset.mem_singleton.mpr (by
        have hpr := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        by_contra hne; exact (Finset.mem_filter.mp hp).2 (hpr.odd_of_ne_two hne))
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ by
      rw [Finset.mem_singleton.mp hp]; positivity).trans (by simp)
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦ div_nonneg
      (Real.log_nonneg (by exact_mod_cast
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_lt.le)) (Nat.cast_nonneg _)
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨hp.1.1, hp.1.2, hp.2⟩

private theorem inert_sum_master_bound {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) {R S N : ℕ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hN : 1 ≤ N) (hparam : N * R + N * S + 2 * R * S < N ^ 3)
    {P' : Finset ℕ} (hP' : ∀ p ∈ P', p.Prime ∧ Odd p ∧ jacobiSym d p = -1) :
    ∑ p ∈ P', Real.log p / p ≤
      (1 + (S : ℝ) / R) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) +
        (3 * Real.log N + 2 * N * Real.log R) / R +
        (∑ p ∈ P', Real.log p / p) / R + 2 * (∑ p ∈ P', Real.log p) / R +
        2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) := by
  have hdet_ub := sum_min_div_log_le_of_jacobiSym_eq_neg_one hd hd1 hR hN hparam hP'
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hlb2 : (R : ℝ) ^ 2 * S * (∑ p ∈ P', Real.log p / p) -
      (R : ℝ) * S * (∑ p ∈ P', Real.log p / p) - 2 * R * S * (∑ p ∈ P', Real.log p) -
      2 * (R : ℝ) ^ 3 * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤
      ∑ p ∈ P', (2 * (∑ u : Fin R × Fin S,
        (min (u.1.val / p) (S - 1 - u.2.val) : ℕ) : ℝ)) * Real.log p := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hP' p hp).1.one_lt.le)
    have hmul := mul_le_mul_of_nonneg_right (two_mul_sum_min_div_ge R S p (hP' p hp).1.pos) hlogp
    linarith [show ((R : ℝ) ^ 2 * S / p - (R : ℝ) * S / p - 2 * R * S -
        2 * (R : ℝ) ^ 3 / (p : ℝ) ^ 2) * Real.log p =
        (R : ℝ) ^ 2 * S * (Real.log p / p) - (R : ℝ) * S * (Real.log p / p) -
        2 * R * S * Real.log p - 2 * (R : ℝ) ^ 3 * (Real.log p / (p : ℝ) ^ 2) by ring]
  have hmul_div := (div_le_div_iff_of_pos_right (mul_pos (sq_pos_of_pos hRpos) hSpos)).mpr
    (hlb2.trans hdet_ub)
  have heqL : ((R : ℝ) ^ 2 * S * (∑ p ∈ P', Real.log p / p) -
      (R : ℝ) * S * (∑ p ∈ P', Real.log p / p) - 2 * R * S * (∑ p ∈ P', Real.log p) -
      2 * (R : ℝ) ^ 3 * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2)) / ((R : ℝ) ^ 2 * S) =
      (∑ p ∈ P', Real.log p / p) - (∑ p ∈ P', Real.log p / p) / R -
      2 * (∑ p ∈ P', Real.log p) / R -
      2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) := by field_simp
  have heqR : ((R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
      (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|)) /
      ((R : ℝ) ^ 2 * S) =
      (3 * Real.log N + 2 * N * Real.log R) / R +
      (1 + (S : ℝ) / R) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by field_simp
  rw [heqL, heqR] at hmul_div; linarith

private theorem inert_sum_main_term_le {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ} {x : ℝ} (hR : 1 ≤ R)
    (hN : 1 ≤ N) (hRx : (R : ℝ) ≤ x) (hS_le : (S : ℝ) ≤ (R : ℝ) / 18) (hN8 : N ^ 3 ≤ 8 * R ^ 2)
    (hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x) :
    (1 + (S : ℝ) / R) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ≤
      3 / 4 * Real.log x + 19 / 9 * Real.log 2 := by
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hdpos : (0 : ℝ) < |(d : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hd0)
  have hlogR_le : Real.log R ≤ Real.log x := Real.log_le_log hRpos hRx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (le_trans (by exact_mod_cast hR) hRx)
  have hlogN_le : Real.log N ≤ Real.log 2 + 2 / 3 * Real.log x := by
    have hlog := Real.log_le_log (pow_pos hNpos 3) (by exact_mod_cast hN8 : (N : ℝ) ^ 3 ≤ 8 * R ^ 2)
    rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero 2 hRpos.ne'), Real.log_pow,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hlog
    push_cast at hlog; linarith
  have hlogd_le : Real.log |(d : ℝ)| ≤ 1 / 18 * Real.log x := by
    have hlog := Real.log_le_log (pow_pos hdpos 18) hdx
    rw [Real.log_pow] at hlog; push_cast at hlog; linarith
  have hM_le : Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ≤
      2 * Real.log 2 + 25 / 36 * Real.log x := by
    rw [Real.log_mul (mul_ne_zero two_ne_zero hNpos.ne') (Real.sqrt_pos.mpr hdpos).ne',
      Real.log_mul two_ne_zero hNpos.ne', Real.log_sqrt hdpos.le]; linarith
  have hSR : 1 + (S : ℝ) / R ≤ 19 / 18 := by
    linarith [(div_le_iff₀ hRpos).mpr (by linarith : (S : ℝ) ≤ 1 / 18 * R)]
  have hlogM_nn : 0 ≤ Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := Real.log_nonneg (by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ |(d : ℝ)| by exact_mod_cast Int.one_le_abs hd0)
    nlinarith [(by exact_mod_cast hN : (1 : ℝ) ≤ N), Real.sqrt_one])
  linarith [mul_le_mul hSR hM_le hlogM_nn (by norm_num : (0 : ℝ) ≤ 19 / 18)]

private theorem inert_sum_prime_errors_le {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRS : (R : ℝ) ≤ 27 * S) {P' : Finset ℕ} (hP'sub : P' ⊆ Nat.primesLE R) :
    (∑ p ∈ P', Real.log p / p) / R + 2 * (∑ p ∈ P', Real.log p) / R +
        2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤
      1 + 56 * Real.log 4 := by
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hpr : ∀ p ∈ P', p.Prime := fun p hp ↦ Nat.prime_of_mem_primesLE (hP'sub hp)
  have hterm3 : (∑ p ∈ P', Real.log p / p) / R ≤ 1 := by
    rw [div_le_one hRpos]
    have hsub : P' ⊆ Finset.Icc 1 R := fun p hp ↦
      Finset.mem_Icc.mpr ⟨(hpr p hp).one_lt.le, Nat.le_of_mem_primesLE (hP'sub hp)⟩
    calc ∑ p ∈ P', Real.log p / p
        ≤ ∑ _p ∈ P', (1 : ℝ) := Finset.sum_le_sum fun p hp ↦ by
          have hppos : (0 : ℝ) < p := Nat.cast_pos.mpr (hpr p hp).pos
          rw [div_le_one hppos]; exact (Real.log_le_sub_one_of_pos hppos).trans (by linarith)
      _ ≤ R := by
        simpa using (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub))
  have hterm4 : 2 * (∑ p ∈ P', Real.log p) / R ≤ 2 * Real.log 4 := by
    have htheta : ∑ p ∈ P', Real.log p ≤ Chebyshev.theta R := by
      rw [Chebyshev.theta_eq_sum_Icc, ← Nat.primesLE_eq_filter_Icc_zero, Nat.floor_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg hP'sub fun p hp _ ↦
        Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)
    rw [div_le_iff₀ hRpos]; linarith [htheta.trans (Chebyshev.theta_le_log4_mul_x hRpos.le)]
  have hterm5 : 2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤ 54 * Real.log 4 := by
    have htail := TauCeti.sum_log_div_sq_le_of_prime (y := 2) zero_lt_two hpr
      (fun p hp ↦ by exact_mod_cast (hpr p hp).two_le)
    have hRS' : 2 * (R : ℝ) / S ≤ 54 := by rw [div_le_iff₀ hSpos]; linarith
    have hsum_nn : 0 ≤ ∑ p ∈ P', Real.log p / (p : ℝ) ^ 2 := Finset.sum_nonneg fun p hp ↦
      div_nonneg (Real.log_nonneg (by exact_mod_cast (hpr p hp).one_lt.le)) (sq_nonneg _)
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  linarith

private noncomputable def inertConst : ℝ :=
  Real.log 36 + 57 * Real.log 4 + 2 * Real.log 8 + 3 * Real.log 2 + 14

private theorem inertConst_nonneg : 0 ≤ inertConst := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 36 by norm_num)
  rw [inertConst]; linarith

private theorem sum_primesLE_jacobiSym_le_of_squarefree_large {d : ℤ} (hd : Squarefree d)
    (hd1 : d ≠ 1) {x : ℝ} (hx36 : 36 ≤ x) (hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1 ∧ Odd p), Real.log p / p ≤
      3 / 4 * Real.log x + (56 * Real.log 4 + 2 * Real.log 8 + 19 / 9 * Real.log 2 + 10) := by
  set R := ⌊x⌋₊
  have hR36 : 36 ≤ R := Nat.le_floor hx36
  set S := R / 18
  obtain ⟨N, hN2, hNR, _, hN8, hparam⟩ := exists_grid_params hR36
  set P' := (Nat.primesLE R).filter (fun p ↦ jacobiSym d p = -1 ∧ Odd p)
  have hmaster := inert_sum_master_bound (P' := P') hd hd1 (by omega) (by omega) (by omega) hparam
    fun p hp ↦ by obtain ⟨hm, hj, ho⟩ := Finset.mem_filter.mp hp
                  exact ⟨Nat.prime_of_mem_primesLE hm, ho, hj⟩
  have hmain := inert_sum_main_term_le hd.ne_zero (by omega) (by omega) (Nat.floor_le (by linarith))
    Nat.cast_div_le hN8 hdx
  have harch := archimedean_error_le hN2 hNR hN8
  have herr := inert_sum_prime_errors_le (S := S) (P' := P') (by omega) (by omega)
    (by exact_mod_cast (show R ≤ 27 * S by omega)) (Finset.filter_subset _ _)
  linarith

private theorem sum_primesLE_jacobiSym_le_of_squarefree {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) (hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
      3 / 4 * Real.log x + inertConst := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
  have := Real.log_nonneg (show (1 : ℝ) ≤ 36 by norm_num)
  rcases lt_or_ge x 36 with hlt | hge
  · have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ ↦
        div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))
          (Nat.cast_nonneg _)
    have hmert := hsub.trans (Chebyshev.sum_primesLE_log_div_le hx)
    have hlogx_le : Real.log x ≤ Real.log 36 := Real.log_le_log (by linarith) hlt.le
    rw [inertConst]; linarith
  · have hsplit := sum_filter_primesLE_le_add_odd (N := ⌊x⌋₊) (P := fun p ↦ jacobiSym d p = -1)
    have hlarge := sum_primesLE_jacobiSym_le_of_squarefree_large hd hd1 hge hdx
    rw [inertConst]; linarith

end Assembly

/-! ### Public inert-prime sum bounds -/

/-- **Inert-prime sum bound for Jacobi symbols.** There is an absolute constant `K` such that for
every integer `d` and every real `x ≥ 1` with `|d| ^ 18 ≤ x`,
`∑_{p ≤ x, jacobiSym d p = -1} log p / p ≤ (3 / 4) log x + K`. -/
theorem sum_primesLE_jacobiSym_eq_neg_one_log_div_le :
    ∃ K : ℝ, ∀ (d : ℤ) (x : ℝ), 1 ≤ x → (|d| : ℝ) ^ (18 : ℕ) ≤ x →
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
        3 / 4 * Real.log x + K := by
  refine ⟨inertConst, fun d x hx hdx ↦ ?_⟩
  have hK_nn : 0 ≤ inertConst := inertConst_nonneg
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases eq_or_ne d 0 with rfl | hd0
  · have : (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym 0 p = -1) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun p hp ↦ by
        rw [jacobiSym.zero_left (Nat.prime_of_mem_primesLE hp).one_lt]; norm_num
    rw [this, Finset.sum_empty]; linarith
  · obtain ⟨m, d₀, hmd, hsf_d₀⟩ := _root_.exists_sq_mul_squarefree d
    have hm0 : m ≠ 0 := fun h ↦ hd0 (by rw [← hmd, h]; simp)
    have hd₀_abs : |d₀| ≤ |d| := by
      have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [Int.one_le_abs hm0, sq_abs m]
      rw [← hmd, abs_mul, abs_of_nonneg (sq_nonneg m)]; nlinarith [abs_nonneg d₀]
    have hd₀_x : (|d₀| : ℝ) ^ (18 : ℕ) ≤ x :=
      (pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast hd₀_abs) 18).trans hdx
    have hsub : (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1) ⊆
        (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d₀ p = -1) := fun p hp ↦ by
      obtain ⟨hpm, hj⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hpm, ?_⟩
      rw [← hmd, jacobiSym.mul_left, sq, jacobiSym.mul_left] at hj
      rcases jacobiSym.trichotomy m p with h0 | h1 | hn1 <;> simp_all
    have hle_d₀ : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
        ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d₀ p = -1), Real.log p / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦
        div_nonneg (Real.log_nonneg (by exact_mod_cast
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_lt.le)) (Nat.cast_nonneg _)
    rcases eq_or_ne d₀ 1 with rfl | hd₀1
    · have : (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym 1 p = -1) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun p _ ↦ by rw [jacobiSym.one_left]; norm_num
      rw [this, Finset.sum_empty] at hle_d₀; linarith
    · exact hle_d₀.trans (sum_primesLE_jacobiSym_le_of_squarefree hsf_d₀ hd₀1 hx hd₀_x)

end TauCeti

namespace DirichletCharacter

open TauCeti.Multiquadratic

private theorem filter_primesLE_odd_subset_jacobiSym {R : Type*} [CommRing R] [NeZero (2 : R)]
    [DecidableEq R] {q : ℕ} {χ : DirichletCharacter R q} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    {N : ℕ} (hval : ∀ m : ℤ, IsCoprime m q → χ m = fundamentalDiscriminantCharCast R D hD m) :
    (Nat.primesLE N).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1 ∧ _root_.Odd p) ⊆
      (Nat.primesLE N).filter (fun p ↦ jacobiSym D p = -1) := by
  intro p hp
  have : Nontrivial R := nontrivial_of_ne 2 0 two_ne_zero
  obtain ⟨hpm, hχp, hodd⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpm, ?_⟩
  have hcop : p.Coprime q := Nat.isCoprime_iff_coprime.mp <|
    (χ.apply_ne_zero_iff p).mp (by rw [Int.cast_natCast, hχp]; exact neg_ne_zero.mpr one_ne_zero)
  have hv : (jacobiSym D p : R) = -1 :=
    (apply_natCast_eq_jacobiSym_of_forall_isCoprime hval hodd hcop).symm.trans hχp
  rcases jacobiSym.trichotomy D p with h0 | h1 | hn1
  · exact absurd (by simpa [h0] using hv.symm) fun h : (-1 : R) = 0 ↦
      NeZero.ne (2 : R) (by rw [← one_add_one_eq_two, neg_eq_zero.mp h, add_zero])
  · exact absurd (by simpa [h1] using hv.symm) fun h : (-1 : R) = 1 ↦
      NeZero.ne (2 : R) (by rw [← one_add_one_eq_two]; linear_combination -h)
  · exact hn1

/-- **Inert-prime sum bound for quadratic Dirichlet characters.** There is an absolute constant `K`
such that for every commutative ring `R` with `2 ≠ 0`, every level `q ≠ 0`, every quadratic
Dirichlet character `χ : DirichletCharacter R q`, and every real `x ≥ q ^ 18`,
`∑_{p ≤ x, χ(p) = -1} log p / p ≤ (3 / 4) log x + K`. -/
theorem sum_primesLE_eq_neg_one_log_div_le :
    ∃ K : ℝ, ∀ {R : Type*} [CommRing R] [NeZero (2 : R)] [DecidableEq R]
      {q : ℕ} [NeZero q] (χ : DirichletCharacter R q), χ.IsQuadratic →
      ∀ x : ℝ, (q : ℝ) ^ (18 : ℕ) ≤ x →
        ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1), Real.log p / p ≤
          3 / 4 * Real.log x + K := by
  obtain ⟨K, hK⟩ := TauCeti.sum_primesLE_jacobiSym_eq_neg_one_log_div_le
  refine ⟨K + Real.log 2 / 2, fun {R} _ _ _ {q} _ χ hquad x hx ↦ ?_⟩
  have hx1 : 1 ≤ x :=
    (one_le_pow₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q) : (1 : ℝ) ≤ q)).trans hx
  obtain ⟨D, ⟨_, habs, hval⟩, -⟩ := hquad.existsUnique_isFundamentalDiscr_apply_eq
  have hDq : (|D| : ℝ) ≤ q := by
    exact_mod_cast ((Int.natCast_natAbs D).symm ▸ Int.ofNat_le.mpr
      (habs ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level))
  have hodd_le := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ ↦ Real.log p / p)
    (filter_primesLE_odd_subset_jacobiSym (N := ⌊x⌋₊) hval) fun p hp _ ↦ div_nonneg
      (Real.log_nonneg (by exact_mod_cast
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_lt.le)) (Nat.cast_nonneg _)
  have hsplit := TauCeti.sum_filter_primesLE_le_add_odd (N := ⌊x⌋₊)
    (P := fun p : ℕ ↦ χ (p : ZMod q) = -1)
  linarith [hK D x hx1 ((pow_le_pow_left₀ (abs_nonneg _) hDq 18).trans hx)]

/-- **Inert-prime sum bound at power cutoffs `q ^ C`.** For every commutative ring `R` with `2 ≠ 0`,
every level `q ≠ 0`, every quadratic Dirichlet character `χ : DirichletCharacter R q`, and every
integer `C ≥ 18`, `∑_{p ≤ q ^ C, χ(p) = -1} log p / p ≤ (3 / 4) log (q ^ C) + K`. -/
theorem sum_primesLE_pow_eq_neg_one_log_div_le :
    ∃ K : ℝ, ∀ {R : Type*} [CommRing R] [NeZero (2 : R)] [DecidableEq R]
      {q : ℕ} [NeZero q] (χ : DirichletCharacter R q), χ.IsQuadratic →
      ∀ C : ℕ, 18 ≤ C →
        ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1), Real.log p / p ≤
          3 / 4 * Real.log ((q : ℝ) ^ C) + K := by
  obtain ⟨K, hK⟩ := sum_primesLE_eq_neg_one_log_div_le
  refine ⟨K, fun {R} _ _ _ {q} _ χ hquad C hC ↦ ?_⟩
  have hpow : (q : ℝ) ^ (18 : ℕ) ≤ (q : ℝ) ^ C :=
    pow_le_pow_right₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) hC
  simpa only [show ⌊(q : ℝ) ^ C⌋₊ = q ^ C by rw [← Nat.cast_pow, Nat.floor_natCast]] using
    hK χ hquad ((q : ℝ) ^ C) hpow

end DirichletCharacter
