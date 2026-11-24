/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summable real powers

A nonnegative family `f` with a summable positive power `f ^ p` tends to `0` along the cofinite
filter, since its terms are the `p`-th roots of a summable family.

Dually, a family `a` with a summable negative power `a ^ r` tends to infinity along the cofinite
filter once it is positive outside a finite set. So `c + a i ~ a i` for every constant `c`, and
`(c + a i) ^ r` is summable as well (`Summable.const_add_rpow`).

For `e < -1`, every constant multiple of the shifted `p`-series `(n + 1) ^ e` over `ℕ` has a
finite sum of nonnegative parts in `ℝ≥0∞`. This is the form of a summable majorant for tail
probabilities decaying polynomially in a sequence index.

## Main results

* `TauCeti.tendsto_cofinite_zero_of_summable_rpow` — a nonnegative family with a summable positive
  power tends to `0`.
* `Summable.const_add_rpow` — if `∑ a i ^ r` converges for `r ≤ 0` and `a` is positive
  outside a finite set, so does `∑ (c + a i) ^ r` for every real `c`.
* `TauCeti.tsum_ofReal_mul_natCast_add_one_rpow_lt_top` —
  `∑' n : ℕ, ENNReal.ofReal (C * (n + 1) ^ e) < ∞` for `e < -1`.
-/

public section

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

open scoped ENNReal in
/-- For `e < -1`, a constant multiple of the shifted real `p`-series `(n + 1) ^ e` has a finite
sum of nonnegative parts in `ℝ≥0∞`. The constant may be negative. -/
theorem tsum_ofReal_mul_natCast_add_one_rpow_lt_top (C : ℝ) {e : ℝ} (he : e < -1) :
    ∑' n : ℕ, ENNReal.ofReal (C * ((n : ℝ) + 1) ^ e) < ∞ := by
  have hsum := ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 he)).mul_left C
  simpa only [Nat.cast_add, Nat.cast_one] using hsum.tsum_ofReal_lt_top

end TauCeti
