/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.Algebra.Order.BigOperators.Sum.Min
import TauCeti.Analysis.SpecialFunctions.Log.ProdPowDvd
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.InertPrimeSum.Determinant

/-!
# The Mertens sum over inert primes of a primitive quadratic character

For a nonprincipal primitive quadratic Dirichlet character `χ` mod `q ≥ 3` and a sufficiently large
exponent `C` divisible by `3`, the logarithmic reciprocal sum over primes `p ≤ q ^ C` with
`χ p = -1` carries at most three quarters of the Mertens mass `log (q ^ C)`, up to an additive
constant depending only on `C`.

Following Green (*On Landau–Siegel zeros*, 2026), let `d ≠ 1` be the squarefree radicand with
`|d| ≤ q` and `χ p = jacobiSym d p` for odd primes `p`, and set `X = q ^ C`, `R = X`, `S = X / C`,
and `N = q ^ (2 * (C / 3)) = X ^ (2 / 3)`. Green's Gram determinant construction in
`TauCeti.NumberTheory.DirichletCharacter.Quadratic.InertPrimeSum.Determinant`
(`TauCeti.exists_pos_nat_log_le_and_pow_dvd_of_jacobiSym_eq_neg_one`) supplies a positive natural
number `D` satisfying both the Hadamard upper bound
`log D ≤ (1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * R ^ 2 * S * log X + O(R ^ 2 * S)` and the
simultaneous `p`-adic divisibilities `p ^ (2 * ∑_{r, s} min (r / p) (S - 1 - s)) ∣ D` at every odd
prime `p` with `jacobiSym d p = -1`. Comparing `∑_p 2 * (∑_{r, s} h) * log p ≤ log D` and dividing
by `R ^ 2 * S` yields the explicit bound for all `C ≥ 6` divisible by `3`, and specializes at
`C ≥ 15` (`56 / 75 < 3 / 4`) to `TauCeti.inert_prime_sum_le`.

## Main results

* `TauCeti.sum_primesLE_jacobiSym_eq_neg_one_le`: explicit upper bound on
  `∑_{2C < p ≤ q^C, (d / p) = -1} log p / p` for any squarefree `d ≠ 1` with `|d| ≤ q` (`q ≥ 3`)
  and any `C ≥ 6` divisible by `3`.
* `DirichletCharacter.IsPrimitive.sum_primesLE_filter_eq_neg_one_le`: explicit upper bound on
  `∑_{p ≤ q^C, χ p = -1} log p / p` for a primitive nonprincipal quadratic character `χ` mod `q ≥ 3`
  over any commutative ring with `2 ≠ 0`, for all `C ≥ 6` divisible by `3`.
* `TauCeti.inert_prime_sum_le`: for all sufficiently large `C` divisible by `3`, inert primes up to
  `q ^ C` carry at most `3 / 4 * log (q ^ C) + O_C(1)` of the Mertens mass.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon **2610.00311** (2026), Theorem 1.1 and §§2–6.
-/

public section

open Finset

namespace TauCeti

namespace InertPrimeSum

/-! ### Parameter arithmetic and assembling the Mertens bound -/

/-- Power identities for `X = q ^ C`, `N = q ^ (2 * (C / 3))`, and `u = q ^ (C / 3)` when
`3 ∣ C`. -/
private theorem grid_pow_identities (q : ℕ) {C : ℕ} (hC3 : 3 ∣ C) :
    q ^ C = (q ^ (C / 3)) ^ 3 ∧
      q ^ (2 * (C / 3)) = (q ^ (C / 3)) ^ 2 ∧
      (q ^ (2 * (C / 3))) ^ 3 = (q ^ C) ^ 2 := by
  have hC_div : C / 3 * 3 = C := Nat.div_mul_cancel hC3
  have hX : q ^ C = (q ^ (C / 3)) ^ 3 := by rw [← pow_mul, hC_div]
  have hN : q ^ (2 * (C / 3)) = (q ^ (C / 3)) ^ 2 := by rw [mul_comm 2 (C / 3), pow_mul]
  have hN3 : (q ^ (2 * (C / 3))) ^ 3 = (q ^ C) ^ 2 := by rw [hN, hX]; ring
  exact ⟨hX, hN, hN3⟩

/-- Parameter arithmetic for `X = q ^ C`, `S = X / C`, `N = q ^ (2 * (C / 3))` when `6 ≤ C` and
`3 ∣ C`. -/
private theorem grid_deg_lt_cube {q C : ℕ} (hq3 : 3 ≤ q) (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    let X := q ^ C
    let S := X / C
    let N := q ^ (2 * (C / 3))
    0 < X ∧ 0 < S ∧ 0 < N ∧
      N * ((X - 1) + (S - 1)) + 2 * (X - 1) * (S - 1) < N ^ 3 := by
  intro X S N
  have hm : 2 ≤ C / 3 := by omega
  set u := q ^ (C / 3)
  have hu9 : 9 ≤ u :=
    (by norm_num : 9 ≤ 3 ^ 2).trans ((Nat.pow_le_pow_right (by omega) hm).trans
      (Nat.pow_le_pow_left hq3 (C / 3)))
  obtain ⟨(hX_eq : X = u ^ 3), (hN_eq : N = u ^ 2), (hN3_eq : N ^ 3 = X ^ 2)⟩ :=
    grid_pow_identities q hC3
  have h9N : 9 * N ≤ X := by rw [hN_eq, hX_eq]; nlinarith
  have hX_gt_C : C < X :=
    (Nat.lt_two_pow_self (n := C)).trans_le (Nat.pow_le_pow_left (by omega) C)
  have hS_pos : 0 < S := Nat.div_pos hX_gt_C.le (by omega)
  have h6S : 6 * S ≤ X := by
    have hS_le : S ≤ X / 6 := Nat.div_le_div_left hC6 (by omega)
    omega
  refine ⟨by positivity, hS_pos, by positivity, ?_⟩
  have hX_pos : 1 ≤ X := by omega
  have hN_pos : 1 ≤ N := by rw [hN_eq]; nlinarith
  rw [hN3_eq]
  change N * (X - 1 + (S - 1)) + 2 * (X - 1) * (S - 1) < X ^ 2
  have hXS : (X - 1) + (S - 1) < 2 * X := by omega
  have hlt1 : N * ((X - 1) + (S - 1)) < 2 * N * X := by nlinarith
  have hle2 : 2 * (X - 1) * (S - 1) ≤ 2 * X * S :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.sub_le X 1)) (Nat.sub_le S 1)
  nlinarith

private theorem sum_exp_mul_log_le_log {d : ℤ} {C X D : ℕ} {e : ℕ → ℕ} (hC_pos : 0 < C)
    (hD_pos : 0 < D) (hD_dvd : ∀ p : ℕ, p.Prime → Odd p → jacobiSym d p = -1 → p ^ e p ∣ D) :
    let P := (Nat.primesLE X).filter fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log (D : ℝ) := by
  intro P
  have hprod_dvd : (∏ p ∈ P, (p : ℤ) ^ e p) ∣ (D : ℤ) := by
    refine Finset.prod_dvd_of_coprime (fun p hp p' hp' hne ↦ ?_) (fun p hp ↦ ?_)
    · have hp_pr := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
      have hp'_pr := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp').1).2
      simpa only [Nat.cast_pow] using ((hp_pr.coprime_iff_not_dvd.mpr fun h ↦
        hne ((Nat.prime_dvd_prime_iff_eq hp_pr hp'_pr).mp h)).pow _ _).isCoprime
    · obtain ⟨hpX, h2C, hjac⟩ := Finset.mem_filter.mp hp
      have hp_pr := (Nat.mem_primesLE.mp hpX).2
      exact Int.ofNat_dvd.mpr (hD_dvd p hp_pr (hp_pr.odd_of_ne_two (by omega)) hjac)
  have hle := Int.sum_mul_log_le_log_abs e (Int.natCast_ne_zero.mpr hD_pos.ne') hprod_dvd
  have hD_real_pos : (0 : ℝ) < D := by exact_mod_cast hD_pos
  rwa [Int.cast_natCast, abs_of_pos hD_real_pos] at hle

private theorem log_det_bound_explicit {d : ℤ} (hd0 : d ≠ 0) {q C : ℕ} (hq3 : 3 ≤ q)
    (hdq : d.natAbs ≤ q) (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    let X := q ^ C
    let S := X / C
    let N := q ^ (2 * (C / 3))
    (X : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log X) +
        (X : ℝ) * S * (X + S) * Real.log (2 * N * Real.sqrt d.natAbs) ≤
      (X : ℝ) ^ 2 * S * ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) *
        Real.log ((q : ℝ) ^ C) + 15) := by
  intro X S N
  obtain ⟨-, -, hN_pos, -⟩ := grid_deg_lt_cube hq3 hC6 hC3
  obtain ⟨hX_eq, hN_eq, hN3_eq⟩ := grid_pow_identities q hC3
  set u := q ^ (C / 3)
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast Nat.one_le_pow (C / 3) q (by omega)
  have hX_u : (X : ℝ) = (u : ℝ) ^ 3 := by exact_mod_cast hX_eq
  have hN_u : (N : ℝ) = (u : ℝ) ^ 2 := by exact_mod_cast hN_eq
  have hN3_X2 : (N : ℝ) ^ 3 = (X : ℝ) ^ 2 := by exact_mod_cast hN3_eq
  have hlogu : Real.log u ≤ u :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by norm_num)
  have herr1 : Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log X ≤ 13 * X := by
    rw [hN_u, hX_u, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    have hu2_log : (u : ℝ) ^ 2 * Real.log u ≤ (u : ℝ) ^ 3 := by
      calc (u : ℝ) ^ 2 * Real.log u
          ≤ (u : ℝ) ^ 2 * u := mul_le_mul_of_nonneg_left hlogu (by positivity)
        _ = (u : ℝ) ^ 3 := by ring
    have hu_le : (u : ℝ) ≤ (u : ℝ) ^ 3 := by nlinarith
    have _ : (1 : ℝ) ≤ (u : ℝ) ^ 3 := by nlinarith
    nlinarith
  have hlog_dq : Real.log (2 * N * Real.sqrt d.natAbs) ≤ Real.log (2 * N * Real.sqrt q) := by
    have _ : (0 : ℝ) < Real.sqrt d.natAbs :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr hd0)
    exact Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hdq)) (by positivity))
  have h2Nq_log : Real.log (2 * N * Real.sqrt q) =
      Real.log 2 + (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) := by
    have hq_pos : (0 : ℝ) < q := by positivity
    have hC_ne : (C : ℝ) ≠ 0 := by positivity
    have hlogN : Real.log (N : ℝ) = 2 / 3 * Real.log ((q : ℝ) ^ C) := by
      have hpow : Real.log ((N : ℝ) ^ 3) = Real.log ((X : ℝ) ^ 2) := congrArg Real.log hN3_X2
      rw [Real.log_pow, Real.log_pow] at hpow
      push_cast at hpow
      have hX_cast : (X : ℝ) = (q : ℝ) ^ C := by dsimp [X]; exact Nat.cast_pow q C
      rw [← hX_cast]
      linarith
    have hlogsq : Real.log (Real.sqrt q) = 1 / (2 * (C : ℝ)) * Real.log ((q : ℝ) ^ C) := by
      rw [Real.log_sqrt hq_pos.le, Real.log_pow]
      field_simp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), hlogN, hlogsq]
    ring
  have hSC : (S : ℝ) ≤ (X : ℝ) / C :=
    (le_div_iff₀ (by positivity)).mpr (by exact_mod_cast Nat.div_mul_le_self X C)
  have hXS_sum : (X : ℝ) + S ≤ (1 + 1 / (C : ℝ)) * X := by
    have hdiv : (X : ℝ) / C = 1 / (C : ℝ) * X := by ring
    linarith
  have hlog2Nq_nn : 0 ≤ Real.log (2 * N * Real.sqrt q) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ q))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
    exact Real.log_nonneg (by nlinarith)
  calc (X : ℝ) * S * (Real.log (2 * (N : ℝ) ^ 3) + 2 * N * Real.log X) +
          (X : ℝ) * S * (X + S) * Real.log (2 * N * Real.sqrt d.natAbs)
      ≤ (X : ℝ) * S * (13 * X) +
          (X : ℝ) * S * ((1 + 1 / (C : ℝ)) * X) * Real.log (2 * N * Real.sqrt q) := by
        refine add_le_add (mul_le_mul_of_nonneg_left herr1 (by positivity)) ?_
        calc (X : ℝ) * S * (X + S) * Real.log (2 * N * Real.sqrt d.natAbs)
            ≤ (X : ℝ) * S * (X + S) * Real.log (2 * N * Real.sqrt q) :=
              mul_le_mul_of_nonneg_left hlog_dq (by positivity)
          _ ≤ (X : ℝ) * S * ((1 + 1 / (C : ℝ)) * X) * Real.log (2 * N * Real.sqrt q) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hXS_sum (by positivity)) hlog2Nq_nn
    _ = (X : ℝ) ^ 2 * S * (13 + (1 + 1 / (C : ℝ)) * Real.log 2 +
          (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C)) := by
        rw [h2Nq_log]; ring
    _ ≤ (X : ℝ) ^ 2 * S * ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) *
          Real.log ((q : ℝ) ^ C) + 15) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1C : 1 / (C : ℝ) ≤ 1 :=
          div_le_one_of_le₀ (by exact_mod_cast (by omega : 1 ≤ C)) (by positivity)
        have h1C_nn : 0 ≤ 1 + 1 / (C : ℝ) := by positivity
        nlinarith

private theorem prime_error_sums_le {P : Finset ℕ} {X S C : ℕ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesLE X ∧ 2 * C < p) (hS_pos : 0 < S) (hC_pos : 0 < C)
    (hS_eq : S = X / C) :
    2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p) +
        2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p) +
        (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2) ≤
      (X : ℝ) ^ 2 * S * (4 * (C : ℝ) * Real.log 4 + 4 * Real.log 4) := by
  have htheta_P : ∑ p ∈ P, Real.log p ≤ Real.log 4 * X := by
    calc ∑ p ∈ P, Real.log p
        ≤ ∑ p ∈ Nat.primesLE X, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ (hP p hp).1) fun p hp _ ↦
            Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
      _ = Chebyshev.theta X := (Chebyshev.theta_eq_sum_primesLE_log X).symm
      _ ≤ Real.log 4 * X := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hsum_p_le : ∑ p ∈ P, Real.log p / p ≤ Real.log 4 * X := by
    refine le_trans (Finset.sum_le_sum fun p hp ↦ ?_) htheta_P
    have hp_pr := (Nat.mem_primesLE.mp (hP p hp).1).2
    exact div_le_self (Real.log_nonneg (by exact_mod_cast hp_pr.one_le))
      (by exact_mod_cast hp_pr.one_le)
  have htail_sq : ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2 ≤ Real.log 4 / C := by
    calc ∑ p ∈ P, Real.log p / (p : ℝ) ^ 2
        ≤ 2 * Real.log 4 / (2 * (C : ℝ)) :=
          sum_log_div_sq_le_of_prime (by positivity)
            (fun p hp ↦ (Nat.mem_primesLE.mp (hP p hp).1).2)
            (fun p hp ↦ by exact_mod_cast (hP p hp).2.le)
      _ = Real.log 4 / C := by field_simp
  have hX_le_2SC : (X : ℝ) ≤ 2 * S * C := by
    have hdiv : X < (S + 1) * C := by
      have hmod := Nat.div_add_mod X C
      have hlt := Nat.mod_lt X hC_pos
      nlinarith
    exact_mod_cast (by nlinarith : X ≤ 2 * S * C)
  have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he1 : 2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p) ≤
      (X : ℝ) ^ 2 * S * (4 * (C : ℝ) * Real.log 4) :=
    calc 2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p)
        ≤ 2 * (X : ℝ) ^ 2 * (Real.log 4 * X) :=
          mul_le_mul_of_nonneg_left hsum_p_le (by positivity)
      _ ≤ 2 * (X : ℝ) ^ 2 * (Real.log 4 * (2 * S * C)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX_le_2SC hlog4_nn) (by positivity)
      _ = (X : ℝ) ^ 2 * S * (4 * (C : ℝ) * Real.log 4) := by ring
  have he2 : 2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p) ≤ (X : ℝ) ^ 2 * S * (2 * Real.log 4) :=
    calc 2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p)
        ≤ 2 * (X : ℝ) * S * (Real.log 4 * X) :=
          mul_le_mul_of_nonneg_left htheta_P (by positivity)
      _ = (X : ℝ) ^ 2 * S * (2 * Real.log 4) := by ring
  have he3 : (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2) ≤
      (X : ℝ) ^ 2 * S * (2 * Real.log 4) :=
    calc (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2)
        ≤ (X : ℝ) ^ 3 * (Real.log 4 / C) := mul_le_mul_of_nonneg_left htail_sq (by positivity)
      _ = (X : ℝ) ^ 2 * X * (Real.log 4 / C) := by ring
      _ ≤ (X : ℝ) ^ 2 * (2 * S * C) * (Real.log 4 / C) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX_le_2SC (by positivity)) (by positivity)
      _ = (X : ℝ) ^ 2 * S * (2 * Real.log 4) := by
          have : (C : ℝ) ≠ 0 := by positivity
          field_simp
  linarith

private theorem sum_fin_prod_min_rev (p X S : ℕ) :
    (∑ i : Fin X × Fin S, ((min (i.1.val / p) (S - 1 - i.2.val) : ℕ) : ℝ)) =
      ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range S, ((min (r / p) s : ℕ) : ℝ) := by
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (n := X)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Equiv.sum_comp Fin.revPerm
      (fun s : Fin S ↦ ((min (r.val / p) (S - 1 - s.val) : ℕ) : ℝ)),
    ← Fin.sum_univ_eq_sum_range (n := S)]
  exact Finset.sum_congr rfl fun s _ ↦ by
    congr 2; simp only [Fin.revPerm_apply, Fin.val_rev]; omega

private theorem le_two_mul_sum_fin_prod_min_mul_log {p X S : ℕ} (hp : p.Prime) (hSX : S ≤ X) :
    (X : ℝ) ^ 2 * S * (Real.log p / p) - 2 * (X : ℝ) ^ 2 * (Real.log p / p) -
        2 * (X : ℝ) * S * Real.log p - (X : ℝ) ^ 3 * (Real.log p / (p : ℝ) ^ 2) ≤
      (2 * ∑ i : Fin X × Fin S, ((min (i.1.val / p) (S - 1 - i.2.val) : ℕ) : ℝ)) *
        Real.log p := by
  have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hSX_R : (S : ℝ) ≤ X := by exact_mod_cast hSX
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hXS_div : (X : ℝ) * S / p ≤ (X : ℝ) ^ 2 / p := by rw [sq]; gcongr
  have h2div : 2 * (X : ℝ) ^ 2 / p = (X : ℝ) ^ 2 / p + (X : ℝ) ^ 2 / p := by ring
  have hexp :
      (X : ℝ) ^ 2 * S / p - 2 * (X : ℝ) ^ 2 / p - 2 * X * S - (X : ℝ) ^ 3 / p ^ 2 ≤
        2 * ∑ i : Fin X × Fin S, ((min (i.1.val / p) (S - 1 - i.2.val) : ℕ) : ℝ) := by
    rw [sum_fin_prod_min_rev]
    linarith [Finset.le_two_mul_sum_range_min_div (K := ℝ) p X S, hXS_div, h2div]
  calc (X : ℝ) ^ 2 * S * (Real.log p / p) - 2 * (X : ℝ) ^ 2 * (Real.log p / p) -
        2 * (X : ℝ) * S * Real.log p - (X : ℝ) ^ 3 * (Real.log p / (p : ℝ) ^ 2)
      = ((X : ℝ) ^ 2 * S / p - 2 * (X : ℝ) ^ 2 / p - 2 * X * S - (X : ℝ) ^ 3 / p ^ 2) *
          Real.log p := by ring
    _ ≤ (2 * ∑ i : Fin X × Fin S, ((min (i.1.val / p) (S - 1 - i.2.val) : ℕ) : ℝ)) *
          Real.log p := mul_le_mul_of_nonneg_right hexp hlog_nn

end InertPrimeSum

/-- **Explicit Mertens bound for primes inert in `ℚ(√d)`.** For any squarefree integer `d ≠ 1`,
any integer `q ≥ 3` with `|d| ≤ q`, and any exponent `C ≥ 6` divisible by `3`, the sum of
`log p / p` over primes `2 * C < p ≤ q ^ C` with `jacobiSym d p = -1` is bounded by
`(1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * log (q ^ C) + (4 * C * log 4 + 4 * log 4 + 15)`. -/
theorem sum_primesLE_jacobiSym_eq_neg_one_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {q C : ℕ} (hq3 : 3 ≤ q) (hdq : d.natAbs ≤ q) (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1),
        Real.log p / (p : ℝ) ≤
      (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) +
        (4 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15) := by
  open InertPrimeSum in
  set X := q ^ C
  set S := X / C
  obtain ⟨_, hS_pos, -, hdeg⟩ := grid_deg_lt_cube hq3 hC6 hC3
  obtain ⟨D, hD_pos, hD_log, hD_dvd⟩ :=
    exists_pos_nat_log_le_and_pow_dvd_of_jacobiSym_eq_neg_one hd hd1 hdeg
  set P := (Nat.primesLE X).filter fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1
  have hsum_log_le :
      ∑ p ∈ P, (2 * ∑ i : Fin X × Fin S, ((min (i.1.val / p) (S - 1 - i.2.val) : ℕ) : ℝ)) *
          Real.log p ≤
        Real.log (D : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_sum] using
      sum_exp_mul_log_le_log (C := C) (X := X) (by omega) hD_pos hD_dvd
  have hSX : S ≤ X := Nat.div_le_self X C
  have hlhs_ge :
      (X : ℝ) ^ 2 * S * (∑ p ∈ P, Real.log p / p) -
          2 * (X : ℝ) ^ 2 * (∑ p ∈ P, Real.log p / p) -
          2 * (X : ℝ) * S * (∑ p ∈ P, Real.log p) -
          (X : ℝ) ^ 3 * (∑ p ∈ P, Real.log p / (p : ℝ) ^ 2) ≤
        ∑ p ∈ P, (2 * ∑ i : Fin X × Fin S, ((min (i.1.val / p) (S - 1 - i.2.val) : ℕ) : ℝ)) *
          Real.log p := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun p hp ↦
      le_two_mul_sum_fin_prod_min_mul_log (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2 hSX
  have hrhs_le : Real.log (D : ℝ) ≤
      (X : ℝ) ^ 2 * S * ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) *
        Real.log ((q : ℝ) ^ C) + 15) :=
    hD_log.trans (log_det_bound_explicit hd.ne_zero hq3 hdq hC6 hC3)
  have herr_sum := prime_error_sums_le
    (P := P) (fun _ hp ↦ ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩)
    hS_pos (by omega : 0 < C) rfl
  have hcomb : (X : ℝ) ^ 2 * S * (∑ p ∈ P, Real.log p / p) ≤
      (X : ℝ) ^ 2 * S *
        ((1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) +
          (4 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15)) := by
    linarith [hlhs_ge.trans (hsum_log_le.trans hrhs_le), herr_sum]
  exact le_of_mul_le_mul_left hcomb (by positivity : (0 : ℝ) < (X : ℝ) ^ 2 * S)

end TauCeti

/-- **Explicit Mertens bound for inert primes of a primitive quadratic character.** Over any
commutative ring `R` with `2 ≠ 0`, for any primitive nonprincipal quadratic Dirichlet character
`χ` mod `q ≥ 3` and any exponent `C ≥ 6` divisible by `3`, the sum of `log p / p` over primes
`p ≤ q ^ C` with `χ p = -1` is bounded by
`(1 + 1 / C) * (2 / 3 + 1 / (2 * C)) * log (q ^ C) + (6 * C * log 4 + 4 * log 4 + 15)`. -/
theorem DirichletCharacter.IsPrimitive.sum_primesLE_filter_eq_neg_one_le {R : Type*}
    [CommRing R] [DecidableEq R] [NeZero (2 : R)] {q : ℕ} {χ : DirichletCharacter R q}
    (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (h1 : χ ≠ 1) (hq3 : 3 ≤ q)
    {C : ℕ} (hC6 : 6 ≤ C) (hC3 : 3 ∣ C) :
    ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1),
        Real.log p / (p : ℝ) ≤
      (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) * Real.log ((q : ℝ) ^ C) +
        (6 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15) := by
  have : NeZero q := ⟨by omega⟩
  have : Nontrivial R := ⟨⟨2, 0, NeZero.ne (2 : R)⟩⟩
  obtain ⟨d, hd, hd1, hdq_abs, hval⟩ := hprim.exists_squarefree_apply_eq_jacobiSym hquad h1
  have hdq : d.natAbs ≤ q := Int.ofNat_le.mp (Int.abs_eq_natAbs d ▸ hdq_abs)
  set S_all := (Nat.primesLE (q ^ C)).filter fun p : ℕ ↦ χ (p : ZMod q) = -1
  have hsplit := (Finset.sum_filter_add_sum_filter_not S_all (fun p : ℕ ↦ p ≤ 2 * C)
    (fun p : ℕ ↦ Real.log p / (p : ℝ))).symm
  have hsmall : ∑ p ∈ S_all.filter (· ≤ 2 * C), Real.log p / (p : ℝ) ≤ 2 * (C : ℝ) * Real.log 4 :=
    calc ∑ p ∈ S_all.filter (· ≤ 2 * C), Real.log p / (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE (2 * C), Real.log p := by
          refine (Finset.sum_le_sum fun p hp ↦ ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦
              Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
          · have hp_pr :=
              (Nat.mem_primesLE.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
            exact div_le_self (Real.log_nonneg (by exact_mod_cast hp_pr.one_le))
              (by exact_mod_cast hp_pr.one_le)
          · obtain ⟨hpS, hp2C⟩ := Finset.mem_filter.mp hp
            exact Nat.mem_primesLE.mpr ⟨hp2C, (Nat.mem_primesLE.mp (Finset.mem_filter.mp hpS).1).2⟩
      _ = Chebyshev.theta (2 * C : ℕ) := (Chebyshev.theta_eq_sum_primesLE_log (2 * C)).symm
      _ ≤ Real.log 4 * (2 * C : ℕ) := Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = 2 * (C : ℝ) * Real.log 4 := by push_cast; ring
  have hlarge_sub : S_all.filter (¬ · ≤ 2 * C) ⊆
      (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ 2 * C < p ∧ jacobiSym d p = -1) := by
    intro p hp
    obtain ⟨hpS, hp2C⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX, hχp⟩ := Finset.mem_filter.mp hpS
    have hp_pr := (Nat.mem_primesLE.mp hpX).2
    have hgt : 2 * C < p := Nat.lt_of_not_ge hp2C
    have hjac_cast : (jacobiSym d p : R) = -1 :=
      (hval p (hp_pr.odd_of_ne_two (by omega))).symm.trans hχp
    rcases jacobiSym.trichotomy d p with h0 | h1' | hm1
    · rw [h0, Int.cast_zero, eq_comm, neg_eq_zero] at hjac_cast
      exact absurd hjac_cast one_ne_zero
    · rw [h1', Int.cast_one] at hjac_cast
      exact absurd (calc (2 : R) = 1 - (-1) := by ring
        _ = 0 := by rw [← hjac_cast, sub_self]) (NeZero.ne (2 : R))
    · exact Finset.mem_filter.mpr ⟨hpX, hgt, hm1⟩
  have hlarge := (Finset.sum_le_sum_of_subset_of_nonneg hlarge_sub fun _ _ _ ↦ by positivity).trans
    (TauCeti.sum_primesLE_jacobiSym_eq_neg_one_le hd hd1 hq3 hdq hC6 hC3)
  linarith

namespace TauCeti

open scoped Classical in
/-- **Inert primes carry at most three quarters of the Mertens mass** (Green, Theorem 1.1).
For every sufficiently large exponent `C` divisible by `3`, there is a constant `K` such that for
every modulus `q ≥ 3` and every primitive nonprincipal quadratic Dirichlet character `χ` mod `q`,
`∑_{p ≤ q ^ C, χ p = -1} log p / p ≤ 3 / 4 * log (q ^ C) + K`. -/
theorem inert_prime_sum_le :
    ∃ C₀ : ℕ, ∀ C : ℕ, C₀ ≤ C → 3 ∣ C → ∃ K : ℝ,
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        3 ≤ q → χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
        ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1),
            Real.log p / (p : ℝ) ≤
          3 / 4 * Real.log ((q : ℝ) ^ C) + K := by
  refine ⟨15, fun C hC15 hC3 ↦ ⟨6 * (C : ℝ) * Real.log 4 + 4 * Real.log 4 + 15,
    fun q χ hq3 hprim hquad h1 ↦ ?_⟩⟩
  have hbound := hprim.sum_primesLE_filter_eq_neg_one_le hquad h1 hq3 (by omega) hC3
  have hinv : 1 / (C : ℝ) ≤ 1 / 15 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hC15)
  have hinv2 : 1 / (2 * (C : ℝ)) ≤ 1 / 30 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 30 ≤ 2 * C))
  have hcoeff : (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ))) ≤ 3 / 4 := by
    calc (1 + 1 / (C : ℝ)) * (2 / 3 + 1 / (2 * (C : ℝ)))
        ≤ (1 + (1 : ℝ) / 15) * (2 / 3 + 1 / 30) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ ≤ 3 / 4 := by norm_num
  have hlog_nn : 0 ≤ Real.log ((q : ℝ) ^ C) :=
    Real.log_nonneg (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ q)))
  nlinarith

end TauCeti
