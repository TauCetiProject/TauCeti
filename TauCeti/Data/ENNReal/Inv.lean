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
is at most `2 b`. Finally, an upper bound `x ≤ y` may be checked against the finite values above
`y`, dually to Mathlib's `ENNReal.le_of_forall_nnreal_lt`.

## Main declarations

* `ENNReal.toReal_one_sub_div`: `(1 - a / b).toReal = 1 - a.toReal / b.toReal` for `a ≤ b`.
* `ENNReal.one_sub_one_div_toReal_nonneg`: for `1 ≤ p`, the Hölder exponent `1 - 1 / p.toReal`
  is nonnegative.
* `ENNReal.one_le_toReal_sub_one`: a finite exponent `2 ≤ r` has `1 ≤ r.toReal - 1`.
* `ENNReal.one_div_toReal_sub_one_div_toReal_nonneg`: for `0 < p ≤ q`, the exponent
  `1 / p.toReal - 1 / q.toReal` is nonnegative.
* `ENNReal.two_le_of_toReal_inv_le`: an exponent `r ≠ 0` with `1 / r ≤ 1 / 2` satisfies `2 ≤ r`;
  conversely `ENNReal.toReal_inv_le_of_two_le`: an exponent `2 ≤ r` has `1 / r ≤ 1 / 2`.
* `ENNReal.one_sub_one_div_toReal_nonneg`, `ENNReal.toReal_inv_lt_one`: for `1 ≤ p` (resp.
  `1 < p`), the Hölder exponent `1 - 1 / p.toReal` is nonnegative (resp. `p.toReal⁻¹ < 1`).
* `ENNReal.one_div_toReal_sub_one_div_toReal_nonneg`, `ENNReal.toReal_inv_sub_toReal_inv_le_one`,
  `ENNReal.toReal_inv_sub_toReal_inv_lt_one`: bounds in `[0, 1]` and `[0, 1)` on the reciprocal
  exponent gap `p.toReal⁻¹ - q.toReal⁻¹`.
* `ENNReal.inv_lt_inv_add_inv_of_le`: `b⁻¹ < c⁻¹ + a⁻¹` for `0 < a ≤ b` and finite `c`.
* `ENNReal.natCast_lt_natCast_mul_iff`: `(n : ℝ≥0∞) < k * p ↔ (n : ℝ) * p.toReal⁻¹ < k` for
  `p ≠ 0`.
* `ENNReal.toNNReal_one_sub_div_pos`: `0 < (1 - a / b).toNNReal` for `a < b`.
* `ENNReal.inv_le_inv_mul_add_and_inv_mul_le_inv`: for `n ≤ (j + 1) p`, the exponent
  `q = (j + 1) p` satisfies `1/p ≤ 1/q + j/n` and `1/q ≤ 1/p`.
* `ENNReal.exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one`: for `r > 1` and `n > 0` with
  `n (2 - r) < 2 r`, a finite exponent `t ≥ 2` with `1/2 - 1/t < 1/n` and `1/r + 1/t ≤ 1`.
* `ENNReal.exists_inv_lt_inv_add_inv_two_and_inv_add_inv_le_iff`: for `0 < q < 2`, an exponent
  `s` with `q⁻¹ < s⁻¹ + 2⁻¹` and `p⁻¹ + s⁻¹ ≤ q⁻¹` exists exactly when `2 < p`.
* `ENNReal.exists_le_lt_lt_add`: for `a ≤ 1`, `ν < 1`, `b ≠ 0` and `a < b + ν`, some `t` with
  `a ≤ t ≤ 1` and `ν < t < b + ν`.
* `ENNReal.le_mul_two_of_le_add_div_two`: the absorption step `a ≤ b + a / 2 → a ≤ 2 b` for
  finite `a`, as used in elliptic estimates.
* `ENNReal.ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul`: the cancellation
  `ofReal (d ^ n / n) / m * ofReal (n * a) = ofReal (a * d ^ n / m.toReal)` for `m` finite and
  nonzero.
* `ENNReal.inv_mul_inv_mul_cancel`: the Hölder exponent `(c * (p * c)⁻¹)⁻¹` of `c` factors in
  `L^(p * c)` is `p`, for `c` finite and nonzero.
* `ENNReal.le_of_forall_nnreal_gt`: `x ≤ y` follows from `x ≤ r` for every finite `r > y`, the
  dual of Mathlib's `ENNReal.le_of_forall_nnreal_lt`.
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

/-- A finite exponent `2 ≤ r` has `1 ≤ r - 1`, read in `ℝ`. -/
theorem one_le_toReal_sub_one {r : ℝ≥0∞} (hr : r ≠ ∞) (hr2 : 2 ≤ r) : 1 ≤ r.toReal - 1 := by
  have := toReal_mono hr hr2
  simp only [toReal_ofNat] at this
  linarith

/-- For `0 < p ≤ q`, the difference `1 / p - 1 / q` of reciprocal exponents is nonnegative (with
`1 / ∞` read as `0`). It is the exponent of the measure factor in the inclusion `L^q ⊆ Lᵖ` on a
finite measure space. -/
theorem one_div_toReal_sub_one_div_toReal_nonneg {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) :
    0 ≤ 1 / p.toReal - 1 / q.toReal := by
  simpa only [one_div, toReal_inv, sub_nonneg] using
    toReal_mono (inv_ne_top.2 hp) (ENNReal.inv_le_inv.2 hpq)

/-- An exponent `r ≠ 0` with `1 / r ≤ 1 / 2` satisfies `2 ≤ r`. Along a Strichartz admissible
pair this is the fact that the space exponent `r` lies on the `L^r` side of `L²`. -/
theorem two_le_of_toReal_inv_le {r : ℝ≥0∞} (hr : r ≠ 0) (h : (r⁻¹).toReal ≤ 2⁻¹) : 2 ≤ r := by
  rw [← ENNReal.inv_le_inv, ← ofReal_toReal (inv_ne_top.2 hr),
    ← ofReal_toReal (a := 2⁻¹) (by simp)]
  exact ofReal_le_ofReal (h.trans_eq (by simp))

/-- An exponent `2 ≤ r` satisfies `1 / r ≤ 1 / 2`, read in `ℝ` (with `1 / ∞` read as `0`). This
is the converse of `ENNReal.two_le_of_toReal_inv_le`. -/
theorem toReal_inv_le_of_two_le {r : ℝ≥0∞} (hr : 2 ≤ r) : (r⁻¹).toReal ≤ 2⁻¹ := by
  rw [← ENNReal.toReal_ofNat, ← ENNReal.toReal_inv]
  exact ENNReal.toReal_mono (by simp) (ENNReal.inv_le_inv.2 hr)

/-- For `1 < p`, the reciprocal exponent `p.toReal⁻¹` is strictly less than `1` (with `p = ∞`
giving `0`). -/
theorem toReal_inv_lt_one {p : ℝ≥0∞} (hp : 1 < p) : p.toReal⁻¹ < 1 := by
  simpa only [toReal_inv, toReal_one] using
    (toReal_lt_toReal (inv_ne_top.2 (zero_lt_one.trans hp).ne') one_ne_top).2
      (ENNReal.inv_lt_one.2 hp)

/-- For `1 ≤ p` and any `q`, the difference `p.toReal⁻¹ - q.toReal⁻¹` is at most `1`. -/
theorem toReal_inv_sub_toReal_inv_le_one {p : ℝ≥0∞} (hp : 1 ≤ p) (q : ℝ≥0∞) :
    p.toReal⁻¹ - q.toReal⁻¹ ≤ 1 := by
  have hp1 : p.toReal⁻¹ ≤ 1 := by
    simpa only [one_div, sub_nonneg] using one_sub_one_div_toReal_nonneg hp
  have hq0 : 0 ≤ q.toReal⁻¹ := inv_nonneg.2 toReal_nonneg
  linarith

/-- When `1 ≤ p`, `q ≠ 0`, and `¬ (p = 1 ∧ q = ∞)`, the reciprocal gap `p.toReal⁻¹ - q.toReal⁻¹` is
strictly below `1`. -/
theorem toReal_inv_sub_toReal_inv_lt_one {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : q ≠ 0)
    (hp1q : ¬ (p = 1 ∧ q = ∞)) : p.toReal⁻¹ - q.toReal⁻¹ < 1 := by
  have hq0 : 0 ≤ q.toReal⁻¹ := inv_nonneg.2 toReal_nonneg
  refine (toReal_inv_sub_toReal_inv_le_one hp q).lt_of_ne fun h1 => hp1q ?_
  have hp_eq : p = 1 := by
    by_contra hp_ne
    linarith [toReal_inv_lt_one (hp.lt_of_ne' hp_ne)]
  refine ⟨hp_eq, ?_⟩
  by_contra hq_ne
  have hq_pos : 0 < q.toReal⁻¹ := inv_pos.2 (toReal_pos hq hq_ne)
  subst hp_eq
  simp only [toReal_one, inv_one] at h1
  linarith

/-- For `p ≠ 0` in `ℝ≥0∞` and natural numbers `n` and `k`, `(n : ℝ≥0∞) < k * p` holds if and only
if `(n : ℝ) * p.toReal⁻¹ < k` (with `∞.toReal⁻¹ = 0`). -/
theorem natCast_lt_natCast_mul_iff {n k : ℕ} {p : ℝ≥0∞} (hp : p ≠ 0) :
    (n : ℝ≥0∞) < k * p ↔ (n : ℝ) * p.toReal⁻¹ < k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [not_lt.2 (mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.2 toReal_nonneg))]
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp [ENNReal.mul_top (Nat.cast_ne_zero.2 hk0), Nat.pos_of_ne_zero hk0]
  rw [← toReal_lt_toReal (natCast_ne_top _) (mul_ne_top (natCast_ne_top _) hp_top),
    toReal_natCast, toReal_mul, toReal_natCast, ← div_lt_iff₀ (toReal_pos hp hp_top),
    div_eq_mul_inv]

/-- **Absorption**: a finite quantity bounded by `b` plus half of itself is at most `2 b`. -/
theorem le_mul_two_of_le_add_div_two {a b : ℝ≥0∞} (ha : a ≠ ∞) (h : a ≤ b + a / 2) :
    a ≤ b * 2 := by
  rw [← ENNReal.div_le_iff two_ne_zero ofNat_ne_top, ← ENNReal.sub_half ha]
  exact tsub_le_iff_right.2 h

/-- **The equal-step exponent ladder.** For `n ≤ (j + 1) p`, the exponent `q = (j + 1) p`
satisfies `1/p ≤ 1/q + j/n` and `1/q ≤ 1/p`: the ladder from `1/p` down to `1/q` in `j` equal
steps `1/q` has every step at most `1/n`. These are the exponent hypotheses of the Sobolev
embedding `W^{j+1,p} → W^{1,q}`. -/
theorem inv_le_inv_mul_add_and_inv_mul_le_inv {n j : ℕ} {p : ℝ≥0}
    (hkp : (n : ℝ≥0) ≤ (j + 1 : ℕ) * p) :
    (p : ℝ≥0∞)⁻¹ ≤ (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ + j * (n : ℝ≥0∞)⁻¹ ∧
      (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ (p : ℝ≥0∞)⁻¹ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hkp0 : ((j + 1 : ℕ) * p : ℝ≥0) ≠ 0 := mul_ne_zero (by positivity) hp0
  have heq : (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ + j * (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ =
      (p : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.coe_inv hkp0, ← ENNReal.coe_inv hp0]
    norm_cast
    field_simp
    push_cast
    ring
  refine ⟨heq.symm.le.trans ?_, le_self_add.trans_eq heq⟩
  gcongr
  exact_mod_cast hkp

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

/-- **An exponent between two bounds.** If `a ≤ 1`, `ν < 1`, `b ≠ 0` and `a < b + ν`, some `t`
with `a ≤ t ≤ 1` lies strictly between `ν` and `b + ν`. Read through `t = p'⁻¹`, this lowers an
exponent `p` to an exponent `p'` with a finite Sobolev exponent, losing none of the margin
`p⁻¹ < q⁻¹ + ν`. -/
theorem exists_le_lt_lt_add {a b ν : ℝ≥0∞} (ha : a ≤ 1) (hν : ν < 1) (hb : b ≠ 0)
    (hab : a < b + ν) : ∃ t, a ≤ t ∧ t ≤ 1 ∧ ν < t ∧ t < b + ν := by
  rcases lt_or_ge ν a with h | h
  · exact ⟨a, le_rfl, ha, h, hab⟩
  obtain ⟨t, h₁, h₂⟩ := exists_between
    (lt_min hν (add_comm ν b ▸ ENNReal.lt_add_right hν.ne_top hb))
  exact ⟨t, h.trans h₁.le, (h₂.trans_le (min_le_left _ _)).le, h₁, h₂.trans_le (min_le_right _ _)⟩

/-- **Every finite exponent clears a supercritical one.** If `a ≤ b` and `a ≠ 0`, then
`b⁻¹ < c⁻¹ + a⁻¹` for every finite `c`. Read with `a = n` the dimension, `b = p` and `c = q`, this
is the Rellich–Kondrachov condition `1/p < 1/q + 1/n` for one derivative when `p ≥ n`. -/
theorem inv_lt_inv_add_inv_of_le {a b c : ℝ≥0∞} (hab : a ≤ b) (ha : a ≠ 0) (hc : c ≠ ∞) :
    b⁻¹ < c⁻¹ + a⁻¹ :=
  (ENNReal.inv_le_inv.2 hab).trans_lt
    (add_comm a⁻¹ c⁻¹ ▸ ENNReal.lt_add_right (ENNReal.inv_ne_top.2 ha) (ENNReal.inv_ne_zero.2 hc))

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

/-- **Equal Hölder exponents.** For `c` finite and nonzero, `c` reciprocal exponents
`(p * c)⁻¹` add up to the reciprocal exponent `p⁻¹`. -/
theorem inv_mul_inv_mul_cancel {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞) (p : ℝ≥0∞) :
    (c * (p * c)⁻¹)⁻¹ = p := by
  rw [ENNReal.mul_inv (.inr hc) (.inr hc₀), mul_left_comm, ENNReal.mul_inv_cancel hc₀ hc, mul_one,
    inv_inv]

/-- An upper bound in `ℝ≥0∞` may be checked against the finite values above it: `x ≤ y` follows
from `x ≤ r` for every `r : ℝ≥0` with `y < r`. This is the dual of
`ENNReal.le_of_forall_nnreal_lt`. -/
theorem le_of_forall_nnreal_gt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, y < r → x ≤ r) : x ≤ y :=
  le_of_forall_gt_imp_ge_of_dense fun b hb ↦ by
    obtain ⟨r, hyr, hrb⟩ := lt_iff_exists_nnreal_btwn.1 hb
    exact (h r hyr).trans hrb.le

end ENNReal
