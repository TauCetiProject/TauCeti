/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Division estimates in `ℝ≥0∞`

For `a ≤ b` in `ℝ≥0∞` the difference `1 - a / b` lies in `[0, 1]`, and it is read in `ℝ` as
`1 - a.toReal / b.toReal`; when `a < b` it is positive. With `a = n` the dimension and `b = p` an
integrability exponent, this is the Hölder exponent `1 - n / p` of Morrey's embedding, which is `1`
for `p = ∞`.

The file also records exhaustion of an extended nonnegative function by its positive level sets,
and the absorption step of elliptic estimates: a finite quantity bounded by `b` plus half of itself
is at most `2 b`.

## Main declarations

* `ENNReal.toReal_one_sub_div`: `(1 - a / b).toReal = 1 - a.toReal / b.toReal` for `a ≤ b`.
* `ENNReal.one_sub_one_div_toReal_nonneg`: for `1 ≤ p`, the Hölder exponent `1 - 1 / p.toReal`
  is nonnegative.
* `ENNReal.one_div_toReal_sub_one_div_toReal_nonneg`: for `0 < p ≤ q`, the exponent
  `1 / p.toReal - 1 / q.toReal` is nonnegative.
* `ENNReal.toNNReal_one_sub_div_pos`: `0 < (1 - a / b).toNNReal` for `a < b`.
* `ENNReal.exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one`: for `r > 1` and `n > 0` with
  `n (2 - r) < 2 r`, a finite exponent `t ≥ 2` with `1/2 - 1/t < 1/n` and `1/r + 1/t ≤ 1`.
* `ENNReal.exists_inv_lt_inv_add_inv_two_and_inv_add_inv_le_iff`: for `0 < q < 2`, an exponent
  `s` with `q⁻¹ < s⁻¹ + 2⁻¹` and `p⁻¹ + s⁻¹ ≤ q⁻¹` exists exactly when `2 < p`.
* `ENNReal.le_mul_two_of_le_add_div_two`: the absorption step `a ≤ b + a / 2 → a ≤ 2 b` for
  finite `a`, as used in elliptic estimates.
* `ENNReal.ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul`: the cancellation
  `ofReal (d ^ n / n) / m * ofReal (n * a) = ofReal (a * d ^ n / m.toReal)` for `m` finite and
  nonzero.
* `ENNReal.one_lt_of_inv_add_inv_le_one`: `p⁻¹ + q⁻¹ ≤ 1` with `p ≠ ∞` implies `1 < q`.
* `ENNReal.inv_add_inv_self_lt_one`: `2 < p` implies `p⁻¹ + p⁻¹ < 1`.
* `ENNReal.exists_nnreal_two_lt_and_le_and_inv_add_inv_lt_one`: truncates `2 < p ≤ ∞` above a
  finite `r ≤ p` while preserving `p₀⁻¹ + q⁻¹ < 1`.
-/

public section

open scoped ENNReal NNReal

namespace ENNReal

/-- Restricting a nonnegative function to the levels above `1 / (n + 1)` is monotone in `n`. -/
theorem monotone_indicator_inv_natCast_add_one_le {X : Type*} (f : X → ℝ≥0∞) :
    Monotone (fun n : ℕ => {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ f x}.indicator f) := by
  intro m n hmn
  exact Set.indicator_le_indicator_of_subset
    (fun x hx => (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.add_le_add_right hmn 1)).trans hx)
    (fun _ => bot_le)

/-- The restrictions to the levels above `1 / (n + 1)` exhaust any nonnegative function. -/
theorem iSup_indicator_inv_natCast_add_one_le {X : Type*} (f : X → ℝ≥0∞) :
    (fun x => ⨆ n : ℕ, {x | (n + 1 : ℝ≥0∞)⁻¹ ≤ f x}.indicator f x) = f := by
  classical
  funext x
  apply le_antisymm
  · exact iSup_le fun n => Set.indicator_le_self _ f x
  · by_cases hx : f x = 0
    · simp [hx]
    obtain ⟨n, hn⟩ := exists_inv_nat_lt hx
    have hxn : (n + 1 : ℝ≥0∞)⁻¹ ≤ f x :=
      (ENNReal.inv_le_inv.mpr (le_add_of_nonneg_right zero_le)).trans hn.le
    exact le_iSup_of_le n (by simp [hxn])

/-- For `a ≤ b`, the difference `1 - a / b` is read in `ℝ` as `1 - a.toReal / b.toReal`. -/
@[simp]
theorem toReal_one_sub_div {a b : ℝ≥0∞} (hab : a ≤ b) :
    (1 - a / b).toReal = 1 - a.toReal / b.toReal := by
  rw [toReal_sub_of_le (div_le_of_le_mul (by simpa using hab)) one_ne_top, toReal_div, toReal_one]

/-- For `a < b`, the difference `1 - a / b` is positive, even after truncation to `ℝ≥0`. -/
theorem toNNReal_one_sub_div_pos {a b : ℝ≥0∞} (hab : a < b) : 0 < (1 - a / b).toNNReal :=
  toNNReal_pos (tsub_pos_of_lt (div_lt_of_lt_mul (by simpa using hab))).ne'
    (sub_ne_top one_ne_top)

/-- For `1 ≤ p`, the Hölder exponent `1 - 1 / p` is nonnegative (with `p = ∞` giving `1`). -/
theorem one_sub_one_div_toReal_nonneg {p : ℝ≥0∞} (hp : 1 ≤ p) : 0 ≤ 1 - 1 / p.toReal := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp
  · have h1p : (1 : ℝ) ≤ p.toReal := by
      simpa using ENNReal.toReal_mono hp_top hp
    exact sub_nonneg.2 (div_le_one_of_le₀ h1p (by positivity))

/-- For `0 < p ≤ q`, the difference `1 / p - 1 / q` of reciprocal exponents is nonnegative (with
`1 / ∞` read as `0`). It is the exponent of the measure factor in the inclusion `L^q ⊆ Lᵖ` on a
finite measure space. -/
theorem one_div_toReal_sub_one_div_toReal_nonneg {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) :
    0 ≤ 1 / p.toReal - 1 / q.toReal := by
  simpa only [one_div, toReal_inv, sub_nonneg] using
    toReal_mono (inv_ne_top.2 hp) (ENNReal.inv_le_inv.2 hpq)

/-- **Absorption**: a finite quantity bounded by `b` plus half of itself is at most `2 b`. -/
theorem le_mul_two_of_le_add_div_two {a b : ℝ≥0∞} (ha : a ≠ ∞) (h : a ≤ b + a / 2) :
    a ≤ b * 2 := by
  rw [← ENNReal.div_le_iff two_ne_zero ofNat_ne_top, ← ENNReal.sub_half ha]
  exact tsub_le_iff_right.2 h

/-- **A finite exponent `t ≥ 2` complementing `r`.** For `n > 0` and `r > 1` with
`n (2 - r) < 2 r`, there is a finite exponent `t ≥ 2` with `1/2 - 1/t < 1/n` and `1/r + 1/t ≤ 1`:
take `1/t = min (1/2) (1 - 1/r)`. -/
theorem exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one {n : ℝ} (hn : 0 < n) {r : ℝ≥0}
    (hr : 1 < r) (hrn : n * (2 - r) < 2 * r) :
    ∃ t : ℝ≥0, 0 < t ∧ (2 : ℝ≥0∞) ≤ t ∧ 2⁻¹ - (t : ℝ)⁻¹ < n⁻¹ ∧
      (r : ℝ)⁻¹ + (t : ℝ)⁻¹ ≤ 1 := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have h2r : (r : ℝ)⁻¹ < 2⁻¹ + n⁻¹ := by
    field_simp
    linarith
  set τ : ℝ := min 2⁻¹ (1 - (r : ℝ)⁻¹)
  have hτ0 : 0 < τ := lt_min (by norm_num) (sub_pos.2 (inv_lt_one_of_one_lt₀ hr1))
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ)⁻¹ = τ :=
    ⟨τ⁻¹.toNNReal, by rw [Real.coe_toNNReal _ (inv_nonneg.2 hτ0.le), inv_inv]⟩
  have ht0 : (0 : ℝ) < t := inv_pos.1 (ht ▸ hτ0)
  refine ⟨t, mod_cast ht0, ?_, ht ▸ sub_lt_comm.1 (lt_min ?_ ?_),
    ht ▸ le_sub_iff_add_le'.1 (min_le_right _ _)⟩
  · have : (2 : ℝ) ≤ t := by rw [← inv_le_inv₀ ht0 two_pos, ht]; exact min_le_left _ _
    exact_mod_cast this
  · linarith [inv_pos.2 hn]
  · linarith

/-- For `0 < q < 2`, an exponent `s` with `q⁻¹ < s⁻¹ + 2⁻¹` and `p⁻¹ + s⁻¹ ≤ q⁻¹` exists exactly
when `2 < p`: at `p = 2` the two conditions would force `q⁻¹ < q⁻¹`.

This is the exponent bookkeeping for the compactness of multiplication by `α ∈ L^p` from
`W^{1,q}` to `L^q` in dimension two, for `1 < q < 2` on a compact surface or a bounded domain
with Lipschitz boundary (the local form of McDuff–Salamon, *J-holomorphic Curves and Symplectic
Topology*, Lemma C.2.2). There `W^{1,q}` embeds compactly in `L^s` for every `s` below the
Sobolev exponent `2q/(2-q)`, that is for `q⁻¹ < s⁻¹ + 2⁻¹`, and Hölder's inequality on the finite
measure space maps `L^p × L^s` to `L^q` when `p⁻¹ + s⁻¹ ≤ q⁻¹`. The arithmetic itself needs
neither a domain nor `1 < q`. -/
theorem exists_inv_lt_inv_add_inv_two_and_inv_add_inv_le_iff {p q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq2 : q < 2) :
    (∃ s : ℝ≥0∞, q⁻¹ < s⁻¹ + 2⁻¹ ∧ p⁻¹ + s⁻¹ ≤ q⁻¹) ↔ 2 < p := by
  have hqtop : q⁻¹ ≠ ∞ := inv_ne_top.2 hq0
  have h2q : (2 : ℝ≥0∞)⁻¹ < q⁻¹ := ENNReal.inv_lt_inv.2 hq2
  constructor
  · rintro ⟨s, hlt, hle⟩
    have hstop : s⁻¹ ≠ ∞ := ne_top_of_le_ne_top hqtop (le_add_self.trans hle)
    have h : s⁻¹ + p⁻¹ < s⁻¹ + 2⁻¹ := by rw [add_comm]; exact hle.trans_lt hlt
    exact ENNReal.inv_lt_inv.1 ((ENNReal.add_lt_add_iff_left hstop).1 h)
  · intro hp
    have hp2 : p⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.2 hp
    have hpq : p⁻¹ ≤ q⁻¹ := (hp2.trans h2q).le
    refine ⟨(q⁻¹ - p⁻¹)⁻¹, ?_, ?_⟩
    · rw [inv_inv]
      calc q⁻¹ = q⁻¹ - p⁻¹ + p⁻¹ := (tsub_add_cancel_of_le hpq).symm
        _ < q⁻¹ - p⁻¹ + 2⁻¹ := ENNReal.add_lt_add_left (sub_ne_top hqtop) hp2
    · rw [inv_inv, add_tsub_cancel_of_le hpq]

/-- Cancelling a finite nonzero denominator `m` against the factor `n` of a product:
`ofReal (d ^ n / n) / m * ofReal (n * a) = ofReal (a * d ^ n / m)`. -/
theorem ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul {n : ℕ} {d a : ℝ} {m : ℝ≥0∞}
    (hn : 0 < n) (hd : 0 ≤ d) (hm₀ : m ≠ 0) (hm_top : m ≠ ∞) :
    ENNReal.ofReal (d ^ n / n) / m * ENNReal.ofReal (n * a) =
      ENNReal.ofReal (a * d ^ n / m.toReal) := by
  have hmpos : 0 < m.toReal := toReal_pos hm₀ hm_top
  conv_lhs => rw [← ofReal_toReal hm_top]
  rw [← ENNReal.ofReal_div_of_pos hmpos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- If `p⁻¹ + q⁻¹ ≤ 1` with `p ≠ ∞`, then `1 < q` since `p⁻¹ > 0` forces `q⁻¹ < 1`. -/
theorem one_lt_of_inv_add_inv_le_one {p q : ℝ≥0∞} (hp : p ≠ ∞) (hpq : p⁻¹ + q⁻¹ ≤ 1) :
    1 < q := by
  have hp_pos : (0 : ℝ≥0∞) < p⁻¹ := ENNReal.inv_pos.2 hp
  have hq_ne_top : q⁻¹ ≠ ∞ := ne_top_of_le_ne_top one_ne_top (le_add_self.trans hpq)
  refine ENNReal.inv_lt_one.1 ?_
  calc q⁻¹ = 0 + q⁻¹ := (zero_add _).symm
    _ < p⁻¹ + q⁻¹ := ENNReal.add_lt_add_right hq_ne_top hp_pos
    _ ≤ 1 := hpq

/-- For `2 < p` in `ℝ≥0∞`, the self-sum of reciprocals satisfies `p⁻¹ + p⁻¹ < 1`. -/
theorem inv_add_inv_self_lt_one {p : ℝ≥0∞} (hp : 2 < p) : p⁻¹ + p⁻¹ < 1 := by
  have hp2 : p⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.2 hp
  calc p⁻¹ + p⁻¹ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add hp2 hp2
    _ = 1 := ENNReal.inv_two_add_inv_two

/-- Given `2 < p`, a finite `r ≤ p`, and `p⁻¹ + q⁻¹ < 1` in `ℝ≥0∞` (allowing `p = ∞` and `q = ∞`),
there exists a finite exponent `p₀ : ℝ≥0` with `2 < p₀`, `r ≤ p₀`, `(p₀ : ℝ≥0∞) ≤ p`, and
`(p₀ : ℝ≥0∞)⁻¹ + q⁻¹ < 1`. -/
theorem exists_nnreal_two_lt_and_le_and_inv_add_inv_lt_one {p q r : ℝ≥0∞} (hp : 2 < p)
    (hr_top : r ≠ ∞) (hrp : r ≤ p) (hpq : p⁻¹ + q⁻¹ < 1) :
    ∃ p₀ : ℝ≥0, 2 < p₀ ∧ r ≤ p₀ ∧ (p₀ : ℝ≥0∞) ≤ p ∧ (p₀ : ℝ≥0∞)⁻¹ + q⁻¹ < 1 := by
  rcases ne_or_eq p ∞ with hp_top | rfl
  · refine ⟨p.toNNReal, ?_, ?_, (coe_toNNReal hp_top).le, ?_⟩
    · exact_mod_cast hp.trans_eq (coe_toNNReal hp_top).symm
    · rwa [coe_toNNReal hp_top]
    · rwa [coe_toNNReal hp_top]
  · have hq_lt : q⁻¹ < 1 := by simpa using hpq
    obtain ⟨n, hn⟩ := exists_inv_nat_lt (tsub_pos_of_lt hq_lt).ne'
    let p₀ : ℝ≥0 := max 3 (max r.toNNReal n)
    refine ⟨p₀, (by norm_num : (2 : ℝ≥0) < 3).trans_le (le_max_left _ _), ?_, le_top, ?_⟩
    · exact (coe_toNNReal hr_top).symm.trans_le
        (ENNReal.coe_le_coe.2 ((le_max_left _ _).trans (le_max_right _ _)))
    · have hnp : (n : ℝ≥0∞) ≤ p₀ := by
        exact_mod_cast (le_max_right r.toNNReal n).trans (le_max_right 3 _)
      have hp₀_lt : (p₀ : ℝ≥0∞)⁻¹ < 1 - q⁻¹ := (ENNReal.inv_le_inv.2 hnp).trans_lt hn
      calc (p₀ : ℝ≥0∞)⁻¹ + q⁻¹ < 1 - q⁻¹ + q⁻¹ :=
            ENNReal.add_lt_add_right (lt_of_lt_of_le hq_lt le_rfl).ne_top hp₀_lt
        _ = 1 := tsub_add_cancel_of_le hq_lt.le

end ENNReal
