/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Group
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Summable real and complex powers

A nonnegative family `f` with a summable positive power `f ^ p` tends to `0` along the cofinite
filter, since its terms are the `p`-th roots of a summable family.

Dually, a family `a` with a summable negative power `a ^ r` tends to infinity along the cofinite
filter once it is positive outside a finite set. So `c + a i ~ a i` for every constant `c`, and
`(c + a i) ^ r` is summable as well (`Summable.const_add_rpow`).

For `1 < s.re` and any complex shift `c : ℂ`, the shifted principal-power series
`∑' n : ℕ, ((n : ℂ) + c) ^ (-s)` converges absolutely. At a nonpositive integer shift `c = -n`
(`n : ℕ`), the base `(n : ℂ) + c` vanishes and the principal-power summand `0 ^ (-s)` is `0` for
`1 < s.re` by Lean's totalized `Complex.cpow`; genuine non-totalized shifts require `c ∉ -ℕ`.

For `e < -1`, every constant multiple of the shifted `p`-series `(n + 1) ^ e` over `ℕ` has a
finite sum of nonnegative parts in `ℝ≥0∞`. This is the form of a summable majorant for tail
probabilities decaying polynomially in a sequence index. A union bound over `N ^ (q + 1)` choices
of `q` events, each with the Markov tail `C / (N ^ a) ^ m`, takes this form through the identity
`N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ (q + 1 - a m q)` for `N > 0`.

## Main results

* `TauCeti.tendsto_cofinite_zero_of_summable_rpow` — a nonnegative family with a summable positive
  power tends to `0`.
* `Summable.const_add_rpow` — if `∑ a i ^ r` converges for `r ≤ 0` and `a` is positive
  outside a finite set, so does `∑ (c + a i) ^ r` for every real `c`.
* `Complex.eventually_re_natCast_add_pos` — `(n : ℂ) + c` has positive real part for all
  sufficiently large `n`.
* `TauCeti.summable_norm_natCast_add_cpow_neg` and `TauCeti.summable_natCast_add_cpow_neg` —
  absolute convergence of `∑' n : ℕ, ((n : ℂ) + c) ^ (-s)` for `1 < s.re` and any `c : ℂ`.
* `TauCeti.tsum_ofReal_mul_natCast_add_one_rpow_lt_top` —
  `∑' n : ℕ, ENNReal.ofReal (C * (n + 1) ^ e) < ∞` for `e < -1`.
* `TauCeti.pow_add_one_mul_div_rpow_pow_pow` —
  `N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ (q + 1 - a m q)` for `N > 0`.
-/

public section

open Complex

namespace TauCeti

/-- A nonnegative family `f` with `f ^ p` summable for some `0 < p` tends to `0` along the
cofinite filter. -/
theorem tendsto_cofinite_zero_of_summable_rpow {ι : Type*} {f : ι → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (h : Summable fun i ↦ f i ^ p) :
    Filter.Tendsto f Filter.cofinite (nhds 0) := by
  have h' := h.tendsto_cofinite_zero.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.2 hp.le))
  rw [Real.zero_rpow (inv_ne_zero hp.ne')] at h'
  exact h'.congr fun i ↦ Real.rpow_rpow_inv (hf i) hp.ne'

/-- **Shifted bases keep nonpositive powers summable.** If `a i ^ r` is summable for some `r ≤ 0`
and `a` is positive outside a finite set (eventually positive along the cofinite filter), then
`(c + a i) ^ r` is summable for every real `c`.

Mathlib's `Real.summable_one_div_nat_add_rpow` is the analogous shift for `|n + a| ^ (-s)` over
`n : ℕ`, where the base `n` visibly tends to infinity. Here the index type is arbitrary, and the
growth `a i → ∞` that makes `c + a i ~ a i` is derived from the summability of `a i ^ r`. -/
theorem _root_.Summable.const_add_rpow {ι : Type*} {a : ι → ℝ} {r : ℝ}
    (h : Summable fun i ↦ a i ^ r) (hr : r ≤ 0) (ha : ∀ᶠ i in Filter.cofinite, 0 < a i)
    (c : ℝ) : Summable fun i ↦ (c + a i) ^ r := by
  rcases hr.eq_or_lt with rfl | hr
  · simpa only [Real.rpow_zero] using h
  -- Summability forces `a i ^ r → 0⁺`, so `a i = (a i ^ r) ^ r⁻¹ → ∞` as `r⁻¹ < 0`.
  have htop : Filter.Tendsto a Filter.cofinite Filter.atTop := by
    have h0 : Filter.Tendsto (fun i ↦ a i ^ r) Filter.cofinite (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.2 ⟨h.tendsto_cofinite_zero,
        ha.mono fun i hi ↦ Real.rpow_pos_of_pos hi r⟩
    refine ((tendsto_rpow_neg_nhdsGT_zero (inv_lt_zero.2 hr)).comp h0).congr' ?_
    filter_upwards [ha] with i hi
    exact Real.rpow_rpow_inv hi.le hr.ne
  -- So `c + a i ~ a i`, hence `(c + a i) ^ r =Θ a i ^ r`.
  have hequiv : Asymptotics.IsEquivalent Filter.cofinite (fun i ↦ c + a i) a :=
    Asymptotics.IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp htop)
  refine summable_of_isBigO h (hequiv.isTheta.rpow ?_ (ha.mono fun i hi ↦ hi.le)).1
  filter_upwards [htop.eventually_ge_atTop (-c)] with i hi
  exact neg_le_iff_add_nonneg'.1 hi

/-- For any `c : ℂ`, `(n : ℂ) + c` has positive real part for all sufficiently large `n : ℕ`. -/
theorem _root_.Complex.eventually_re_natCast_add_pos (c : ℂ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < ((n : ℂ) + c).re := by
  filter_upwards [(Filter.eventually_gt_atTop (-c.re)).natCast_atTop] with n hn
  simp only [add_re, natCast_re]
  linarith

/-- For `1 < s.re` and any `c : ℂ`, the principal-power series `∑' n : ℕ, ‖(n + c) ^ (-s)‖` is
summable (for `c = -n` with `n : ℕ`, the `n`-th summand uses the totalized principal power
`0 ^ (-s) = 0`). -/
theorem summable_norm_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖((n : ℂ) + c) ^ (-s)‖) := by
  obtain ⟨N, hN_pos⟩ := Filter.eventually_atTop.mp c.eventually_re_natCast_add_pos
  have hN : (N : ℂ) + c ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (hN_pos N le_rfl))
  obtain ⟨U, hU, -, C, -, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hN (-s)
  have hp : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-s.re)) :=
    ((summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow (p := -s.re)).mpr (by linarith))).congr
      fun n => by push_cast; rw [add_comm]
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hp.mul_left C)
  have h := hbound ((N : ℂ) + c) (mem_of_mem_nhds hU) (n : ℝ) (Nat.cast_nonneg n)
  simpa only [ofReal_natCast, neg_re, Nat.cast_add, add_assoc] using h

/-- For `1 < s.re` and any `c : ℂ`, `n ↦ (n + c) ^ (-s)` is summable (with totalized `0 ^ (-s) = 0`
at index `n` when `c = -n`). -/
theorem summable_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) :=
  (summable_norm_natCast_add_cpow_neg hs c).of_norm

open scoped ENNReal in
/-- For `e < -1`, a constant multiple of the shifted real `p`-series `(n + 1) ^ e` has a finite
sum of nonnegative parts in `ℝ≥0∞`. The constant may be negative. -/
theorem tsum_ofReal_mul_natCast_add_one_rpow_lt_top (C : ℝ) {e : ℝ} (he : e < -1) :
    ∑' n : ℕ, ENNReal.ofReal (C * ((n : ℝ) + 1) ^ e) < ∞ := by
  have hsum := ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 he)).mul_left C
  simpa only [Nat.cast_add, Nat.cast_one] using hsum.tsum_ofReal_lt_top

/-- For `N > 0`, `N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ (q + 1 - a m q)`. This writes a
union bound over `N ^ (q + 1)` choices of `q` events, each with the Markov tail `C / (N ^ a) ^ m`,
as a single real power of `N`. -/
theorem pow_add_one_mul_div_rpow_pow_pow {N : ℝ} (hN : 0 < N) (C a : ℝ) (m q : ℕ) :
    N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ ((q : ℝ) + 1 - a * m * q) := by
  rw [div_pow, ← pow_mul, ← Real.rpow_natCast N (q + 1), ← Real.rpow_mul_natCast hN.le,
    mul_div_left_comm, ← Real.rpow_sub hN]
  push_cast
  ring_nf

end TauCeti
