/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import TauCeti.Algebra.ContinuedFractions.Approximations
public import TauCeti.NumberTheory.DiophantineApproximation.Exponent
import Mathlib.Tactic.LinearCombination

/-!
# Convergents and the irrationality exponent

Let `ξ` be irrational and let `pₖ / qₖ = ξ.convergent k` be its convergents, written in lowest
terms. This file identifies `qₖ` with the denominator continuant `Bₖ` of the continued fraction
`GenContFract.of ξ` and transfers the continued-fraction error bounds to the reduced fractions:

`1 / (qₖ (qₖ + qₖ₊₁)) < |ξ - pₖ / qₖ| ≤ 1 / (qₖ qₖ₊₁)`.

With Legendre's theorem, which says that every sufficiently good approximation is a convergent,
these bounds compute the irrationality exponent from the growth of the denominators:

`μ(ξ) = 1 + limsup (log qₖ₊₁ / log qₖ)`.

An exponent `1 + s` with `log qₖ₊₁ > s log qₖ` infinitely often is realised by the convergents,
through the upper bound. Conversely, approximations `|ξ - r| < r.den ^ (-p)` with `p > 2` and
large denominator are convergents `pₖ / qₖ`, and the lower bound then forces
`qₖ ^ (p - 1) < 2 qₖ₊₁`.

## Main results

* `Real.den_convergent`, `Real.num_convergent`: for irrational `ξ`, the reduced denominator and
  numerator of `ξ.convergent n` are the continuants `Bₙ` and `Aₙ`.
* `Real.fib_succ_le_den_convergent`, `Real.monotone_den_convergent`,
  `Real.tendsto_den_convergent`: growth of the denominators `qₙ`.
* `Real.abs_sub_convergent_le`, `Real.one_div_lt_abs_sub_convergent`: the two error bounds.
* `TauCeti.irrationalityExponent_eq_one_add_limsup`: the formula for `μ(ξ)`.

## References

* J. Sondow, *Irrationality measures, irrationality bases, and a theorem of Jarnik*, §3,
  Theorem 1.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 1, Exercise 1.7.
-/

public section

open Filter GenContFract
open GenContFract (of)

namespace Real

variable {ξ : ℝ}

/-- The continued fraction of an irrational number does not terminate. -/
theorem _root_.Irrational.not_of_terminatedAt (hξ : Irrational ξ) (n : ℕ) :
    ¬(of ξ).TerminatedAt n := fun h ↦ by
  obtain ⟨q, rfl⟩ := (terminates_iff_rat ξ).mp ⟨n, h⟩
  exact hξ.ne_rat q rfl

/-- The `n`-th continuants of an irrational number are coprime integers `a` and `b > 0`, and the
`n`-th convergent is `a / b`. -/
private theorem exists_int_nums_dens (hξ : Irrational ξ) (n : ℕ) :
    ∃ a b : ℤ, (of ξ).nums n = a ∧ (of ξ).dens n = b ∧ 0 < b ∧
      Nat.Coprime a.natAbs b.natAbs ∧ ξ.convergent n = a / b := by
  obtain ⟨a, b, h⟩ := exists_int_contsAux_eq ξ (n + 1)
  obtain ⟨a', b', h'⟩ := exists_int_contsAux_eq ξ (n + 2)
  have hA : (of ξ).nums n = a := by rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux, h]
  have hB : (of ξ).dens n = b := by rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, h]
  have hA' : (of ξ).nums (n + 1) = a' := by
    rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux, h']
  have hB' : (of ξ).dens (n + 1) = b' := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, h']
  -- `SimpContFract.of ξ` is `of ξ` bundled with its simplicity proof, so its determinant formula
  -- applies to `of ξ`.
  have hdet : (of ξ).nums n * (of ξ).dens (n + 1) - (of ξ).dens n * (of ξ).nums (n + 1) =
      (-1) ^ (n + 1) := (SimpContFract.of ξ).determinant (hξ.not_of_terminatedAt n)
  rw [hA, hB, hA', hB'] at hdet
  have hdetZ : a * b' - b * a' = (-1) ^ (n + 1) := by exact_mod_cast hdet
  have hfib : ((Nat.fib (n + 1) : ℕ) : ℝ) ≤ b :=
    hB ▸ succ_nth_fib_le_of_nth_den (Or.inr (hξ.not_of_terminatedAt (n - 1)))
  have hb : 0 < b := by
    have : (0 : ℝ) < Nat.fib (n + 1) := by exact_mod_cast Nat.fib_pos.mpr n.succ_pos
    exact_mod_cast this.trans_le hfib
  set u : ℤ := (-1) ^ (n + 1)
  have hu : u * u = 1 := by rw [← mul_pow]; simp
  have hcop : IsCoprime a b := ⟨b' * u, -a' * u, by linear_combination u * hdetZ + hu⟩
  refine ⟨a, b, hA, hB, hb, Int.isCoprime_iff_gcd_eq_one.mp hcop, ?_⟩
  rw [← (Rat.cast_injective (α := ℝ)).eq_iff, ← convs_eq_convergent, conv_eq_num_div_den, hA, hB]
  simp

/-- For irrational `ξ`, the reduced denominator of `ξ.convergent n` is the `n`-th denominator
continuant `Bₙ` of the continued fraction of `ξ`. -/
theorem den_convergent (hξ : Irrational ξ) (n : ℕ) :
    ((ξ.convergent n).den : ℝ) = (of ξ).dens n := by
  obtain ⟨a, b, -, hB, hb, hcop, hconv⟩ := exists_int_nums_dens hξ n
  rw [hconv, hB]
  exact_mod_cast Rat.den_div_eq_of_coprime hb hcop

/-- For irrational `ξ`, the reduced numerator of `ξ.convergent n` is the `n`-th numerator
continuant `Aₙ` of the continued fraction of `ξ`. -/
theorem num_convergent (hξ : Irrational ξ) (n : ℕ) :
    ((ξ.convergent n).num : ℝ) = (of ξ).nums n := by
  obtain ⟨a, b, hA, -, hb, hcop, hconv⟩ := exists_int_nums_dens hξ n
  rw [hconv, Rat.num_div_eq_of_coprime hb hcop, hA]

/-- The denominators of the convergents of an irrational number grow at least like the
Fibonacci numbers. -/
theorem fib_succ_le_den_convergent (hξ : Irrational ξ) (n : ℕ) :
    Nat.fib (n + 1) ≤ (ξ.convergent n).den := by
  have := succ_nth_fib_le_of_nth_den (v := ξ) (Or.inr (hξ.not_of_terminatedAt (n - 1)))
  rw [← den_convergent hξ] at this
  exact_mod_cast this

/-- The denominators of the convergents of an irrational number are monotone. -/
theorem monotone_den_convergent (hξ : Irrational ξ) :
    Monotone fun n ↦ (ξ.convergent n).den :=
  monotone_nat_of_le_succ fun n ↦ by
    have := of_den_mono (v := ξ) (n := n)
    rw [← den_convergent hξ, ← den_convergent hξ] at this
    exact_mod_cast this

/-- The denominators of the convergents of an irrational number tend to infinity. -/
theorem tendsto_den_convergent (hξ : Irrational ξ) :
    Tendsto (fun n ↦ (ξ.convergent n).den) atTop atTop :=
  tendsto_atTop_mono' atTop ((eventually_ge_atTop 4).mono fun n hn ↦
    (Nat.le_succ n).trans ((Nat.le_fib_self (by omega)).trans (fib_succ_le_den_convergent hξ n)))
    tendsto_id

/-- The error of the `n`-th convergent of an irrational number is at most `1 / (qₙ qₙ₊₁)`. -/
theorem abs_sub_convergent_le (hξ : Irrational ξ) (n : ℕ) :
    |ξ - ξ.convergent n| ≤
      1 / ((ξ.convergent n).den * (ξ.convergent (n + 1)).den) := by
  rw [den_convergent hξ, den_convergent hξ, ← convs_eq_convergent]
  exact abs_sub_convs_le (hξ.not_of_terminatedAt n)

/-- The error of the `n`-th convergent of an irrational number exceeds `1 / (qₙ (qₙ + qₙ₊₁))`. -/
theorem one_div_lt_abs_sub_convergent (hξ : Irrational ξ) (n : ℕ) :
    1 / ((ξ.convergent n).den * ((ξ.convergent n).den + (ξ.convergent (n + 1)).den)) <
      |ξ - ξ.convergent n| := by
  rw [den_convergent hξ, den_convergent hξ, ← convs_eq_convergent]
  exact one_div_lt_abs_sub_convs (hξ.not_of_terminatedAt n)

end Real

namespace TauCeti

open Real

variable {ξ : ℝ}

/-- If infinitely often `log qₖ₊₁ / log qₖ` exceeds `s ≥ 0`, then the convergents witness
`LiouvilleWith (1 + s) ξ`. -/
private theorem liouvilleWith_one_add_of_frequently (hξ : Irrational ξ) {s : ℝ} (hs : 0 ≤ s)
    (h : ∃ᶠ k in atTop,
      s < Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den) :
    LiouvilleWith (1 + s) ξ := by
  refine Set.Infinite.liouvilleWith_of_abs_sub_lt_rpow_neg fun hfin ↦ ?_
  obtain ⟨N, hN⟩ := (hfin.image Rat.den).bddAbove
  obtain ⟨k, hk, hkN⟩ :=
    (h.and_eventually ((tendsto_den_convergent hξ).eventually_gt_atTop N)).exists
  refine hkN.not_ge (hN ⟨ξ.convergent k, ?_, rfl⟩)
  have hq1 : (1 : ℝ) ≤ (ξ.convergent k).den := by exact_mod_cast (ξ.convergent k).pos
  have hq'0 : (0 : ℝ) < (ξ.convergent (k + 1)).den := by exact_mod_cast (ξ.convergent (k + 1)).pos
  set q := ((ξ.convergent k).den : ℝ)
  set q' := ((ξ.convergent (k + 1)).den : ℝ)
  have hlog : 0 < Real.log q := by
    refine (Real.log_nonneg hq1).lt_of_ne' fun h0 ↦ ?_
    simp only [q, h0, div_zero] at hk
    exact hs.not_gt hk
  -- `log q' > s log q`, that is `q' > q ^ s`.
  have hqs : q ^ s < q' := by
    rw [lt_div_iff₀ hlog] at hk
    rw [← Real.exp_log hq'0, Real.rpow_def_of_pos (by positivity), mul_comm]
    exact Real.exp_lt_exp.mpr hk
  calc |ξ - ξ.convergent k| ≤ 1 / (q * q') := abs_sub_convergent_le hξ k
    _ < 1 / (q * q ^ s) := one_div_lt_one_div_of_lt (by positivity) (by gcongr)
    _ = q ^ (-(1 + s)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_one, one_div]

/-- Below the threshold `2 ≤ d ^ (p - 2)` of Legendre's theorem, `d ^ (-p) ≤ 1 / (2 d ^ 2)`. -/
private theorem rpow_neg_le_one_div_two_mul_sq {d p : ℝ} (hd : 0 < d) (h2 : 2 ≤ d ^ (p - 2)) :
    d ^ (-p) ≤ 1 / (2 * d ^ 2) := by
  have hsplit : d ^ (-p) = (d ^ (p - 2))⁻¹ * (d ^ 2)⁻¹ := by
    rw [← Real.rpow_neg hd.le, ← Real.rpow_natCast, ← Real.rpow_neg hd.le, ← Real.rpow_add hd]
    congr 1
    push_cast
    ring
  rw [hsplit, one_div, mul_inv]
  gcongr

/-- The logarithmic form of `q ^ p < q (q + q')`: if moreover `q ≤ q'` and
`log 2 < (p - 1 - t) log q`, then `t < log q' / log q`. -/
private theorem lt_log_div_log_of_rpow_lt {q q' p t : ℝ} (hq : 2 ≤ q) (hqq' : q ≤ q')
    (hpow : q ^ p < q * (q + q')) (hlog2 : Real.log 2 < (p - 1 - t) * Real.log q) :
    t < Real.log q' / Real.log q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < Real.log q := Real.log_pos (by linarith)
  have hpow' : q ^ (p - 1) < 2 * q' := by
    rw [Real.rpow_sub_one hq0.ne', div_lt_iff₀ hq0]
    nlinarith
  have hlogs : (p - 1) * Real.log q < Real.log 2 + Real.log q' := by
    rw [← Real.log_rpow hq0, ← Real.log_mul two_ne_zero (by linarith)]
    exact Real.log_lt_log (Real.rpow_pos_of_pos hq0 _) hpow'
  rw [lt_div_iff₀ hlog]
  nlinarith

/-- An infinite set of rationals `r` with `|ξ - r| < r.den ^ (-p)`, `p ≥ 0`, contains members of
arbitrarily large denominator. -/
private theorem exists_le_den_of_infinite {p : ℝ} (hp : 0 ≤ p)
    (hS : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-p)}.Infinite) (N : ℕ) :
    ∃ r : ℚ, |ξ - r| < (r.den : ℝ) ^ (-p) ∧ N ≤ r.den := by
  obtain ⟨r, hr, hrN⟩ :=
    (hS.sdiff ((Metric.isBounded_ball (x := ξ) (r := 1)).finite_setOf_rat_den_le N)).nonempty
  refine ⟨r, hr, not_lt.mp fun h ↦ hrN ⟨h.le, ?_⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  exact hr.trans_le (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast r.pos) (by linarith))

/-- If infinitely many rationals `r` satisfy `|ξ - r| < r.den ^ (-p)` with `p > 2`, then
infinitely often `log qₖ₊₁ / log qₖ` exceeds any `t < p - 1`: by Legendre's theorem these
rationals are convergents, and the lower error bound forces `qₖ ^ (p - 1) < 2 qₖ₊₁`. -/
private theorem frequently_lt_log_div_log (hξ : Irrational ξ) {p : ℝ} (hp : 2 < p)
    (hS : {r : ℚ | |ξ - r| < (r.den : ℝ) ^ (-p)}.Infinite) {t : ℝ} (ht : t < p - 1) :
    ∃ᶠ k in atTop,
      t < Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den := by
  refine frequently_atTop.mpr fun K ↦ ?_
  -- Large denominators `d` satisfy `2 ≤ d ^ (p - 2)`, `log 2 < (p - 1 - t) log d` and `q_K < d`.
  have hev : ∀ᶠ d : ℕ in atTop, 2 ≤ (d : ℝ) ^ (p - 2) ∧
      Real.log 2 < (p - 1 - t) * Real.log d ∧ (ξ.convergent K).den < d := by
    have hd := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (((tendsto_rpow_atTop (by linarith)).comp hd).eventually_ge_atTop 2).and
      ((((Real.tendsto_log_atTop.comp hd).const_mul_atTop (by linarith)).eventually_gt_atTop
        _).and (eventually_gt_atTop _))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨r, hr, hNr⟩ := exists_le_den_of_infinite (by linarith) hS N
  obtain ⟨h2, hlog2, hK⟩ := hN r.den hNr
  -- Legendre's theorem identifies `r` with a convergent `pₖ / qₖ`, with `k ≥ K`.
  obtain ⟨k, rfl⟩ := exists_rat_eq_convergent
    (hr.trans_le (rpow_neg_le_one_div_two_mul_sq (by positivity) h2))
  refine ⟨k, not_lt.mp fun hk ↦ (monotone_den_convergent hξ hk.le).not_gt hK, ?_⟩
  -- The two error bounds give `qₖ ^ p < qₖ (qₖ + qₖ₊₁)`.
  have hpow := (one_div_lt_abs_sub_convergent hξ k).trans hr
  rw [Real.rpow_neg (by positivity), one_div,
    inv_lt_inv₀ (by positivity) (by positivity)] at hpow
  refine lt_log_div_log_of_rpow_lt ?_ (by exact_mod_cast monotone_den_convergent hξ k.le_succ)
    hpow hlog2
  exact_mod_cast (Nat.succ_le_of_lt (ξ.convergent K).pos).trans_lt hK

/-- Eventually `log qₖ₊₁ / log qₖ ≥ 1`, so the limit superior is at least one. -/
private theorem one_le_limsup_log_div_log (hξ : Irrational ξ) :
    1 ≤ limsup (fun k : ℕ ↦ ENNReal.ofReal
      (Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den)) atTop := by
  refine le_limsup_of_frequently_le (Eventually.frequently ?_)
  filter_upwards [(tendsto_den_convergent hξ).eventually_ge_atTop 2] with k hk
  have hq2 : (2 : ℝ) ≤ (ξ.convergent k).den := by exact_mod_cast hk
  have hqq' : ((ξ.convergent k).den : ℝ) ≤ (ξ.convergent (k + 1)).den := by
    exact_mod_cast monotone_den_convergent hξ k.le_succ
  have hlog : 0 < Real.log (ξ.convergent k).den := Real.log_pos (by linarith)
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ((one_le_div₀ hlog).mpr ?_)
  exact Real.log_le_log (by linarith) hqq'

/-- **The irrationality exponent through continued fractions** (Sondow, Theorem 1): for an
irrational `ξ` with convergent denominators `qₖ`,
`μ(ξ) = 1 + limsup (log qₖ₊₁ / log qₖ)`. The limit superior is taken in `ℝ≥0∞`; the finitely
many terms with `qₖ = 1` have value `0` and do not affect it. -/
theorem irrationalityExponent_eq_one_add_limsup (hξ : Irrational ξ) :
    irrationalityExponent ξ = 1 + limsup (fun k : ℕ ↦ ENNReal.ofReal
      (Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den)) atTop := by
  set L := limsup (fun k : ℕ ↦ ENNReal.ofReal
    (Real.log (ξ.convergent (k + 1)).den / Real.log (ξ.convergent k).den)) atTop
  refine le_antisymm ?_ (le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_)
  · -- Each exponent `p > 2` of infinitely many approximations is at most `1 + L`.
    rw [irrationalityExponent_eq_iSup_infinite]
    refine iSup₂_le fun p hp ↦ ?_
    rcases le_or_gt p 2 with hp2 | hp2
    · calc ENNReal.ofReal p ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hp2
        _ = 1 + 1 := by norm_num [one_add_one_eq_two]
        _ ≤ 1 + L := by gcongr; exact one_le_limsup_log_div_log hξ
    rw [show p = 1 + (p - 1) by ring, ENNReal.ofReal_add zero_le_one (by linarith),
      ENNReal.ofReal_one]
    gcongr
    refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
    have hct : c.toReal < p - 1 := (ENNReal.lt_ofReal_iff_toReal_lt hc.ne_top).mp hc
    rw [← ENNReal.ofReal_toReal hc.ne_top]
    exact le_limsup_of_frequently_le ((frequently_lt_log_div_log hξ hp2 hp hct).mono
      fun k hk ↦ ENNReal.ofReal_le_ofReal hk.le)
  · -- Each `c < 1 + L` is realised by a Liouville exponent of the convergents.
    rcases le_or_gt c 1 with hc1 | hc1
    · exact hc1.trans (one_le_irrationalityExponent ξ)
    have hctop : c ≠ ⊤ := hc.ne_top
    set s := c.toReal - 1
    have hs : 0 < s := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hctop).mpr hc1
      simp only [ENNReal.toReal_one] at this
      simp only [s]
      linarith
    have hcs : c = 1 + ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hs.le]
      simp [s, ENNReal.ofReal_toReal hctop]
    rw [hcs] at hc ⊢
    have hsL : ENNReal.ofReal s < L := (ENNReal.add_lt_add_iff_left ENNReal.one_ne_top).mp hc
    have hfreq := (frequently_lt_of_lt_limsup (by isBoundedDefault) hsL).mono fun k hk ↦
      ((ENNReal.ofReal_lt_ofReal_iff'.mp hk).1)
    simpa [ENNReal.ofReal_add, hs.le] using
      le_irrationalityExponent_of_liouvilleWith (liouvilleWith_one_add_of_frequently hξ hs.le hfreq)

end TauCeti
