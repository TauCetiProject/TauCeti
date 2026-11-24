/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Algebra.Order.Antidiag.Pi
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Complex.PowerSeries.MultiIndex
import TauCeti.NumberTheory.ThueSiegel

/-!
# The auxiliary function of transcendence proofs on a polydisc

Let `φ_λ`, for `λ` in a finite type `Λ` of cardinality `L`, have power series on the open polydisc
of radius `R` in `ι → ℂ`, where `ι` is nonempty with `n = card ι`, and suppose `‖φ_λ‖ ≤ M_λ` there
with `∑ M_λ ≤ exp U`. Put `W = N + U + V`. If `12 ≤ W`, `e ≤ R / r ≤ exp (W / 6)` and
`(2 W) ^ (n + 1) ≤ L N (log (R / r)) ^ n`, then there are integers `p_λ`, not all zero, with
`|p_λ| ≤ exp N` and `‖∑ p_λ φ_λ‖ ≤ exp (-V)` on the closed polydisc of radius `r`
(`TauCeti.exists_ne_zero_int_norm_sum_le`). This is Waldschmidt's Proposition 4.10: the
construction of the auxiliary function, an integer linear combination of given analytic functions
that is very small on a polydisc, with which the Schneider–Lang criterion starts.

The integers come from Thue–Siegel's lemma
(`TauCeti.ThueSiegel.exists_ne_zero_int_vec_norm_le_of_exp_le`) applied to the multi-index
coefficients of degree `< T`, scaled to the radius `r`; Cauchy's inequality
(`HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le`) bounds these linear forms. The truncated Taylor
bound (`HasFPowerSeriesOnBall.norm_le_add_sum_mvCoeff`) then controls `∑ p_λ φ_λ` on the polydisc
of radius `r` by the coefficients of degree `< T` and a remainder `(1 + T) e ^ (N + U) (r / R) ^ T`.
The order is `T = ⌈(W + log (4 W + 4)) / log (R / r)⌉`, which makes the remainder at most
`exp (-V) / 2`. Waldschmidt assumes `12 n² ≤ W`; the argument here needs only `12 ≤ W`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, §4.5, Proposition 4.10 (pp. 131–132) and
  Lemmas 4.12 and 4.13 (pp. 133–135).
-/

public section

open Finset Metric
open scoped NNReal

namespace TauCeti

/-- The numerical fact behind the choice of the order `T`: `4 W + 4 ≤ exp (W / 3)` for `12 ≤ W`. -/
private theorem four_mul_add_four_le_exp_div_three {W : ℝ} (hW : 12 ≤ W) :
    4 * W + 4 ≤ Real.exp (W / 3) := by
  have h4 : (52 : ℝ) ≤ Real.exp 4 := by
    have h := Real.exp_one_gt_d9
    calc (52 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h.le 4
      _ = Real.exp 4 := by rw [Real.exp_one_pow]; norm_num
  have hsplit : Real.exp (W / 3) = Real.exp 4 * Real.exp ((W - 12) / 3) := by
    rw [← Real.exp_add]; ring_nf
  have hlin : (W - 12) / 3 + 1 ≤ Real.exp ((W - 12) / 3) := Real.add_one_le_exp _
  have hpos : 0 ≤ (W - 12) / 3 + 1 := by linarith
  rw [hsplit]
  nlinarith [mul_le_mul h4 hlin hpos (Real.exp_pos 4).le]

/-- The choice of the order `T` in Proposition 4.10: for `12 ≤ W` and `1 ≤ ℓ ≤ W / 6`, the
natural number `T = ⌈(W + log (4 W + 4)) / ℓ⌉` is positive, satisfies
`W + log (4 W + 4) ≤ T ℓ`, `T ≤ 4 W / 3 + 1` and `T ℓ ≤ 3 W / 2`. -/
private theorem exists_order {W ℓ : ℝ} (hW : 12 ≤ W) (hℓ : 1 ≤ ℓ) (hℓW : ℓ ≤ W / 6) :
    ∃ T : ℕ, 0 < T ∧ W + Real.log (4 * W + 4) ≤ T * ℓ ∧ (T : ℝ) ≤ 4 * W / 3 + 1 ∧
      T * ℓ ≤ 3 * W / 2 := by
  set a := Real.log (4 * W + 4)
  have ha : a ≤ W / 3 :=
    (Real.log_le_iff_le_exp (by linarith)).2 (four_mul_add_four_le_exp_div_three hW)
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  have hℓ0 : 0 < ℓ := by linarith
  have hWa : 0 ≤ (W + a) / ℓ := div_nonneg (by linarith) hℓ0.le
  have hceil_le : (W + a) / ℓ ≤ ⌈(W + a) / ℓ⌉₊ := Nat.le_ceil _
  have hceil_lt : (⌈(W + a) / ℓ⌉₊ : ℝ) < (W + a) / ℓ + 1 := Nat.ceil_lt_add_one hWa
  have hdiv_le : (W + a) / ℓ ≤ W + a := div_le_self (by linarith) hℓ
  refine ⟨⌈(W + a) / ℓ⌉₊, Nat.ceil_pos.2 (div_pos (by linarith) hℓ0), ?_, by linarith, ?_⟩
  · exact (div_le_iff₀ hℓ0).1 hceil_le
  · have h : (⌈(W + a) / ℓ⌉₊ : ℝ) * ℓ < ((W + a) / ℓ + 1) * ℓ :=
      mul_lt_mul_of_pos_right hceil_lt hℓ0
    rw [add_mul, div_mul_cancel₀ _ hℓ0.ne'] at h
    linarith

/-- The counting inequality of Proposition 4.10: if `T ℓ ≤ 3 W / 2` and `log 3 + log T ≤ W / 3`,
then `2 T ^ n (W + log 3 + n log T) ℓ ^ n ≤ (2 W) ^ (n + 1)` for `n ≥ 1`. It compares the number
`T ^ n` of linear forms, weighted by their logarithmic size, with the count of the hypothesis. -/
private theorem two_mul_pow_mul_le {W ℓ : ℝ} {T n : ℕ} (hn : 1 ≤ n) (hW : 0 ≤ W)
    (hℓ : 0 ≤ ℓ) (hTℓ : T * ℓ ≤ 3 * W / 2) (hlog : Real.log 3 + Real.log T ≤ W / 3) :
    2 * T ^ n * (W + Real.log 3 + n * Real.log T) * ℓ ^ n ≤ (2 * W) ^ (n + 1) := by
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : W + Real.log 3 + n * Real.log T ≤ W * (1 + n * (1 / 3)) := by
    nlinarith [mul_le_mul_of_nonneg_right hn' hlog3]
  have hbern : 1 + n * (1 / 3 : ℝ) ≤ (1 + 1 / 3) ^ n :=
    one_add_le_pow_of_two_add_nonneg (by norm_num) n
  calc 2 * T ^ n * (W + Real.log 3 + n * Real.log T) * ℓ ^ n
      = 2 * (T * ℓ) ^ n * (W + Real.log 3 + n * Real.log T) := by ring
    _ ≤ 2 * (3 * W / 2) ^ n * (W * (1 + 1 / 3) ^ n) := by
        have h1 : (T * ℓ) ^ n ≤ (3 * W / 2) ^ n := pow_le_pow_left₀ (by positivity) hTℓ n
        have h2 : W + Real.log 3 + n * Real.log T ≤ W * (1 + 1 / 3) ^ n :=
          hsum.trans (mul_le_mul_of_nonneg_left hbern hW)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 two_pos.le) h2 (by positivity)
          (by positivity)
    _ = (2 * W) ^ (n + 1) := by
        rw [pow_succ, show (2 * W) ^ n = (3 * W / 2) ^ n * (1 + 1 / 3) ^ n by
          rw [← mul_pow]; ring_nf]
        ring

/-- A ratio `R / r ≥ e` of a nonnegative `R` to a real `r` forces `0 < r < R`. -/
private theorem pos_and_lt_of_exp_one_le_div {r R : ℝ} (hR : 0 ≤ R) (h : Real.exp 1 ≤ R / r) :
    0 < r ∧ r < R := by
  have hr : 0 < r := by
    by_contra! hr
    linarith [Real.exp_pos 1, div_nonpos_of_nonneg_of_nonpos hR hr]
  exact ⟨hr, (one_lt_div hr).1 (by linarith [Real.add_one_le_exp 1])⟩

/-- The counting condition of Thue–Siegel's lemma in Proposition 4.10: with
`exp (-V') = exp (-V) / (2 T ^ n)`, the quantity `√2 exp (N + U + V') + 1` is at most
`3 T ^ n exp W`, so `c ≤ T ^ n` linear forms satisfy the count of
`TauCeti.ThueSiegel.exists_ne_zero_int_vec_norm_le_of_exp_le` once
`2 T ^ n (W + log 3 + n log T) ≤ N L`. -/
private theorem sqrt_two_mul_exp_add_one_pow_le {W N : ℝ} {T n c L : ℕ} (hW : 12 ≤ W)
    (hT : 0 < T) (hc : c ≤ T ^ n)
    (hcount : 2 * T ^ n * (W + Real.log 3 + n * Real.log T) ≤ N * L) :
    (Real.sqrt 2 * Real.exp (W + Real.log (2 * T ^ n)) + 1) ^ (2 * c) ≤ Real.exp (N * L) := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hTn : (1 : ℝ) ≤ (T : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast hT)
  have hy0 : 0 ≤ W + Real.log 3 + n * Real.log T := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T by exact_mod_cast hT)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    positivity
  have hbase : Real.sqrt 2 * Real.exp (W + Real.log (2 * T ^ n)) + 1 ≤
      Real.exp (W + Real.log 3 + n * Real.log T) := by
    rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num), Real.exp_natCast_mul, Real.exp_log hTR]
    have hx : 13 ≤ Real.exp W * T ^ n := by nlinarith [Real.add_one_le_exp W]
    have hsqrt : Real.sqrt 2 ≤ 1.45 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    nlinarith [mul_le_mul_of_nonneg_right hsqrt (by positivity : 0 ≤ Real.exp W * T ^ n)]
  calc (Real.sqrt 2 * Real.exp (W + Real.log (2 * T ^ n)) + 1) ^ (2 * c)
      ≤ Real.exp (W + Real.log 3 + n * Real.log T) ^ (2 * c) :=
        pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ Real.exp (W + Real.log 3 + n * Real.log T) ^ (2 * T ^ n) :=
        pow_le_pow_right₀ (Real.one_le_exp hy0) (by omega)
    _ = Real.exp (2 * T ^ n * (W + Real.log 3 + n * Real.log T)) := by
        rw [← Real.exp_natCast_mul]
        push_cast
        ring_nf
    _ ≤ Real.exp (N * L) := Real.exp_le_exp.2 hcount

/-- The remainder of the truncated Taylor bound in Proposition 4.10: if `W = N + U + V` satisfies
`W + log (4 W + 4) ≤ T ℓ` and `T ≤ 4 W / 3 + 1`, then
`(1 + T) exp (N + U) exp (-ℓ) ^ T ≤ exp (-V) / 2`. -/
private theorem one_add_mul_exp_mul_exp_pow_le {N U V ℓ : ℝ} {T : ℕ} (hW : 12 ≤ N + U + V)
    (hWT : N + U + V + Real.log (4 * (N + U + V) + 4) ≤ T * ℓ)
    (hT : (T : ℝ) ≤ 4 * (N + U + V) / 3 + 1) :
    (1 + T) * Real.exp (N + U) * Real.exp (-ℓ) ^ T ≤ Real.exp (-V) / 2 := by
  set W := N + U + V
  have ha : 0 < 4 * W + 4 := by linarith
  have hpow : Real.exp (N + U) * Real.exp (-ℓ) ^ T ≤ Real.exp (-V) / (4 * W + 4) := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add, ← Real.exp_log ha, ← Real.exp_sub,
      Real.exp_le_exp]
    linarith
  calc (1 + T) * Real.exp (N + U) * Real.exp (-ℓ) ^ T
      ≤ (1 + T) * (Real.exp (-V) / (4 * W + 4)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ Real.exp (-V) / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ ha two_pos]
        nlinarith [Real.exp_pos (-V)]

/-- The Thue–Siegel step of Proposition 4.10: integers `ξ_λ`, not all zero, with
`|ξ_λ| ≤ exp N`, for which every multi-index coefficient of degree `< T` of `∑ ξ_λ P_λ`, scaled to
the radius `r`, is at most `exp (-V)`; so their sum is at most `exp (-V)` times their number. -/
private theorem exists_int_sum_norm_mvCoeff_mul_pow_le {ι Λ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Λ] [Nonempty Λ] {φ : Λ → (ι → ℂ) → ℂ}
    {P : Λ → FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {R : ℝ≥0}
    (hφ : ∀ l, HasFPowerSeriesOnBall (φ l) (P l) 0 R)
    {M : Λ → ℝ} (hM : ∀ l, ∀ y ∈ ball (0 : ι → ℂ) R, ‖φ l y‖ ≤ M l)
    {N U V r : ℝ} (hMU : ∑ l, M l ≤ Real.exp U) (hN : 0 ≤ N) (hr : 0 ≤ r) (hrR : r < R)
    {T : ℕ} (hcard : (Real.sqrt 2 * Real.exp (N + U + V) + 1) ^
      (2 * #((range T).biUnion (piAntidiag (univ : Finset ι)))) ≤
        Real.exp (N * Fintype.card Λ)) :
    ∃ ξ : Λ → ℤ, ξ ≠ 0 ∧ (∀ l, |(ξ l : ℝ)| ≤ Real.exp N) ∧
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖(∑ l, (ξ l : ℂ) • P l).mvCoeff α‖ * r ^ k ≤
        #((range T).biUnion (piAntidiag (univ : Finset ι))) * Real.exp (-V) := by
  set B := (range T).biUnion (piAntidiag (univ : Finset ι))
  set u : Λ → B → ℂ := fun l α ↦ (P l).mvCoeff α.val * (r : ℂ) ^ (∑ i, α.val i)
  have hu (α : B) : ∑ l, ‖u l α‖ ≤ Real.exp U := by
    refine (sum_le_sum fun l _ ↦ ?_).trans hMU
    simpa only [u, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr] using
      (hφ l).norm_mvCoeff_mul_pow_le (hM l) α.val hr hrR
  obtain ⟨ξ, hξ0, hξN, hξu⟩ :=
    ThueSiegel.exists_ne_zero_int_vec_norm_le_of_exp_le u hN hu (by simpa using hcard)
  refine ⟨ξ, hξ0, hξN, ?_⟩
  have hterm (α : ι → ℕ) (hα : α ∈ B) :
      ‖(∑ l, (ξ l : ℂ) • P l).mvCoeff α‖ * r ^ (∑ i, α i) ≤ Real.exp (-V) := by
    refine le_of_eq_of_le ?_ (hξu ⟨α, hα⟩)
    have h : ∑ l, u l ⟨α, hα⟩ * (ξ l : ℂ) =
        (∑ l, (ξ l : ℂ) • P l).mvCoeff α * (r : ℂ) ^ (∑ i, α i) := by
      rw [FormalMultilinearSeries.mvCoeff_sum, sum_mul]
      refine sum_congr rfl fun l _ ↦ ?_
      rw [FormalMultilinearSeries.mvCoeff_smul, smul_eq_mul]
      simp only [u]
      ring
    rw [h, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr]
  calc ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖(∑ l, (ξ l : ℂ) • P l).mvCoeff α‖ * r ^ k
      = ∑ α ∈ B, ‖(∑ l, (ξ l : ℂ) • P l).mvCoeff α‖ * r ^ (∑ i, α i) := by
        rw [sum_biUnion_piAntidiag]
        exact sum_congr rfl fun k _ ↦ sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
    _ ≤ #B * Real.exp (-V) := (sum_le_sum hterm).trans_eq (by rw [sum_const, nsmul_eq_mul])

/-- The truncated Taylor bound for an integer combination `∑ ξ_λ φ_λ` with `|ξ_λ| ≤ exp N`: on the
closed polydisc of radius `r < R` it is at most `(1 + T) exp (N + U) (r / R) ^ T` plus the
multi-index coefficients of degree `< T` of `∑ ξ_λ P_λ`, scaled to the radius `r`. -/
private theorem norm_sum_intCast_mul_le {ι Λ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Λ]
    {φ : Λ → (ι → ℂ) → ℂ} {P : Λ → FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {R : ℝ≥0}
    (hφ : ∀ l, HasFPowerSeriesOnBall (φ l) (P l) 0 R)
    {M : Λ → ℝ} (hM : ∀ l, ∀ y ∈ ball (0 : ι → ℂ) R, ‖φ l y‖ ≤ M l)
    {N U r : ℝ} (hMU : ∑ l, M l ≤ Real.exp U) {ξ : Λ → ℤ}
    (hξ : ∀ l, |(ξ l : ℝ)| ≤ Real.exp N) (T : ℕ) {z : ι → ℂ} (hz : ‖z‖ ≤ r) (hrR : r < R) :
    ‖∑ l, (ξ l : ℂ) * φ l z‖ ≤ (1 + T) * Real.exp (N + U) * (r / R) ^ T +
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖(∑ l, (ξ l : ℂ) • P l).mvCoeff α‖ * r ^ k := by
  have hR : 0 < (R : ℝ) := (norm_nonneg z).trans_lt (hz.trans_lt hrR)
  have hF : HasFPowerSeriesOnBall (fun z ↦ ∑ l, (ξ l : ℂ) * φ l z)
      (∑ l, (ξ l : ℂ) • P l) 0 R := by
    convert univ.hasFPowerSeriesOnBall_sum (f := fun l ↦ (ξ l : ℂ) • φ l)
      (by simpa using hR) fun l _ ↦ (hφ l).const_smul using 1
    ext z
    simp
  refine hF.norm_le_add_sum_mvCoeff (fun y hy ↦ ?_) T hz hrR
  calc ‖∑ l, (ξ l : ℂ) * φ l y‖ ≤ ∑ l, ‖(ξ l : ℂ) * φ l y‖ := norm_sum_le _ _
    _ ≤ ∑ l, Real.exp N * M l := by
        refine sum_le_sum fun l _ ↦ ?_
        rw [norm_mul, Complex.norm_intCast]
        exact mul_le_mul (hξ l) (hM l y hy) (norm_nonneg _) (Real.exp_pos N).le
    _ ≤ Real.exp (N + U) := by
        rw [← mul_sum, Real.exp_add]
        exact mul_le_mul_of_nonneg_left hMU (Real.exp_pos N).le

/-- **The auxiliary function** (Waldschmidt, Proposition 4.10). Let `φ_λ` (`λ : Λ`, a finite type
of cardinality `L`) have power series on the open polydisc of radius `R` about `0` in `ι → ℂ`,
with `ι` nonempty and `n = card ι`, and suppose `‖φ_λ‖ ≤ M_λ` there with `∑ M_λ ≤ exp U`. Put
`W = N + U + V`. If `12 ≤ W`, `e ≤ R / r ≤ exp (W / 6)` and
`(2 W) ^ (n + 1) ≤ L N (log (R / r)) ^ n`, then there are integers `p_λ`, not all zero, with
`|p_λ| ≤ exp N` and `‖∑ p_λ φ_λ z‖ ≤ exp (-V)` on the closed polydisc of radius `r`.

Waldschmidt assumes `12 n² ≤ W`, which implies `12 ≤ W`. The hypotheses force `0 < r` and
`0 < N`. -/
theorem exists_ne_zero_int_norm_sum_le {ι Λ : Type*} [Fintype ι] [Nonempty ι] [Fintype Λ]
    {φ : Λ → (ι → ℂ) → ℂ} {P : Λ → FormalMultilinearSeries ℂ (ι → ℂ) ℂ} {R : ℝ≥0}
    (hφ : ∀ l, HasFPowerSeriesOnBall (φ l) (P l) 0 R)
    {M : Λ → ℝ} (hM : ∀ l, ∀ y ∈ ball (0 : ι → ℂ) R, ‖φ l y‖ ≤ M l)
    {N U V r : ℝ} (hMU : ∑ l, M l ≤ Real.exp U) (hW : 12 ≤ N + U + V)
    (hRr : Real.exp 1 ≤ R / r) (hRr' : R / r ≤ Real.exp ((N + U + V) / 6))
    (hL : (2 * (N + U + V)) ^ (Fintype.card ι + 1) ≤
      Fintype.card Λ * N * Real.log (R / r) ^ Fintype.card ι) :
    ∃ p : Λ → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp N) ∧
      ∀ z ∈ closedBall (0 : ι → ℂ) r, ‖∑ l, (p l : ℂ) * φ l z‖ ≤ Real.exp (-V) := by
  classical
  set W := N + U + V with hW_def
  set n := Fintype.card ι
  set ℓ := Real.log (R / r)
  have hn : 1 ≤ n := Fintype.card_pos
  -- The radii: `0 < r < R` and `1 ≤ ℓ`.
  obtain ⟨hr0, hrR⟩ := pos_and_lt_of_exp_one_le_div R.coe_nonneg hRr
  have hRr0 : 0 < (R : ℝ) / r := (Real.exp_pos 1).trans_le hRr
  have hℓ1 : 1 ≤ ℓ := (Real.le_log_iff_exp_le hRr0).2 hRr
  have hℓ0 : 0 < ℓ := one_pos.trans_le hℓ1
  -- `N` and `L` are positive, so `Λ` is nonempty.
  have hNL : 0 < (Fintype.card Λ : ℝ) * N :=
    pos_of_mul_pos_left ((pow_pos (by linarith) _).trans_le hL) (pow_nonneg hℓ0.le n)
  have hN : 0 < N := pos_of_mul_pos_right hNL (Nat.cast_nonneg _)
  have : Nonempty Λ := Fintype.card_pos_iff.1 (by exact_mod_cast pos_of_mul_pos_left hNL hN.le)
  -- The order `T`, and Thue–Siegel's lemma with `exp (-V') = exp (-V) / (2 T ^ n)`.
  obtain ⟨T, hT0, hWT, hT43, hTℓ⟩ := exists_order hW hℓ1 ((Real.log_le_iff_le_exp hRr0).2 hRr')
  have hlog : Real.log 3 + Real.log T ≤ W / 3 := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact (Real.log_le_iff_le_exp (by positivity)).2
      (by linarith [four_mul_add_four_le_exp_div_three hW])
  have hcount : 2 * T ^ n * (W + Real.log 3 + n * Real.log T) ≤ N * Fintype.card Λ :=
    le_of_mul_le_mul_right ((two_mul_pow_mul_le hn (by linarith) hℓ0.le hTℓ hlog).trans
      (by rw [mul_comm N]; exact hL)) (pow_pos hℓ0 n)
  set V' := V + Real.log (2 * T ^ n)
  have hV' : Real.exp (-V') = Real.exp (-V) / (2 * T ^ n) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity),
      div_eq_mul_inv]
  have hNUV' : N + U + V' = W + Real.log (2 * T ^ n) := by simp only [V', hW_def]; ring
  obtain ⟨ξ, hξ0, hξN, hξ⟩ := exists_int_sum_norm_mvCoeff_mul_pow_le (T := T) hφ hM hMU hN.le
    hr0.le hrR (hNUV' ▸ sqrt_two_mul_exp_add_one_pow_le hW hT0
      (card_biUnion_range_piAntidiag_le T) hcount)
  refine ⟨ξ, hξ0, hξN, fun z hz ↦ (norm_sum_intCast_mul_le hφ hM hMU hξN T
    (mem_closedBall_zero_iff.1 hz) hrR).trans ?_⟩
  -- The remainder and the coefficients each contribute at most `exp (-V) / 2`.
  have hrem : (1 + T) * Real.exp (N + U) * (r / R) ^ T ≤ Real.exp (-V) / 2 := by
    rw [show r / R = Real.exp (-ℓ) by rw [Real.exp_neg, Real.exp_log hRr0, inv_div]]
    exact one_add_mul_exp_mul_exp_pow_le hW hWT hT43
  have hcoef : ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k,
      ‖(∑ l, (ξ l : ℂ) • P l).mvCoeff α‖ * r ^ k ≤ Real.exp (-V) / 2 := by
    refine hξ.trans ?_
    calc #((range T).biUnion (piAntidiag (univ : Finset ι))) * Real.exp (-V')
        ≤ T ^ n * (Real.exp (-V) / (2 * T ^ n)) := by
          rw [hV']
          gcongr
          exact_mod_cast card_biUnion_range_piAntidiag_le T
      _ = Real.exp (-V) / 2 := by field_simp
  linarith

end TauCeti
