/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# Elementary bounds on real powers

A base at least `2` raised to a negative exponent of size at least `1` is at most `1 / 2`. This
is the shape in which the local ratio of an Euler factor is bounded away from `1`, so that the
denominator `1 - y ^ (-s)` stays bounded below.

For any `θ < 1` and any exponent `β`, some base `τ ∈ (0, 1)` has `θ < τ ^ β`. This is how a
geometric ratio is chosen in iteration arguments, such as the absorption lemma.

For `1 ≤ p`, the graph of `u ↦ u ^ p` on `[0, ∞)` lies above each of its tangent lines:
`v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p`, strictly so when `1 < p` and `u ≠ v`. This is
Bernoulli's inequality made homogeneous, and it is the first-order optimality test for weighted
sums of powers.

For `t ∈ [0, 1]` and any exponent `r`, the sum `(1 - t) ^ r + t ^ r` is positive, so it can be
used as the normalizing denominator of a pair of weights.

If `1 ≤ C`, `D < n` and `C ^ (D / (n - D)) < B + 1`, then `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n`. This
is the counting step of Siegel's lemma: it compares the integer points of a box with the cells
of a partition of the image of that box under `D` linear forms.

For `t > 0` and every natural `k`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`: the Japanese bracket
decays at least as fast as `t ^ (-1)`. This converts symbol estimates of order `0` into Mihlin's
condition.

If `0 < d` and `2 ≤ d ^ (p - 2)`, then `d ^ (-p) ≤ 1 / (2 d ^ 2)`: an approximation of quality
`d ^ (-p)` meets the hypothesis of Legendre's theorem `Real.exists_rat_eq_convergent`.

For `0 ≤ p ≤ 1`, a nonnegative quantity `r ≤ 2 h` has `r ^ p ≤ 2 h ^ p`. This is how, in a
temporal Hölder estimate with exponent `p`, a time at most twice the time step `h` is bounded by
a multiple of `h ^ p`.

If `2 ≤ q ≤ q'` and `q ^ p < q (q + q')`, then `q ^ (p - 1) < 2 q'`, so
`(p - 1) log q < log 2 + log q'`. Hence `t < log q' / log q` once `log 2 < (p - 1 - t) log q`.
This reads off the growth of consecutive continued-fraction denominators from the lower error
bound `1 / (q (q + q')) < |ξ - p / q|`.

If `0 < t ≤ 1` and `ε ≤ A t` with `0 ≤ A`, then `t ^ (-ε) ≤ exp A`. This makes factors such as
`a ^ (-ε)` uniformly bounded when the exponent `ε` shrinks with the radius `a`, as in Taubes's
monotonicity inequality with `ε = C₀ r ^ (-1/2)` and `a = c₀ r ^ (-1/2)`.

For `s ≥ 0` the weight `(1 + ‖x‖) ^ s` on a seminormed group is subadditive up to the constant
`2 ^ s`. This is the weight inequality behind product estimates in weighted sequence spaces. The
weight `1 + ‖x‖` itself is submultiplicative: `1 + ‖x + y‖ ≤ (1 + ‖x‖) (1 + ‖y‖)`.

For `1 < q`, the power mean inequality `u ^ q ≤ 2 ^ (q - 1) * (s ^ q + t ^ q)` for
`0 ≤ u ≤ s + t` improves by a uniform factor `1 - κ` once `u` is also bounded away from `2 * s`,
say `u ≤ (2 - δ) * s` with `0 ≤ t ≤ s`. Strict convexity of `t ↦ t ^ q` gives the improvement
for each ratio `t / s`, and compactness of `[0, 1]` makes it uniform. This is the scalar step in
showing that `q`-th powers of norms on a uniformly convex space are uniformly convex.

## Main results

* `Real.rpow_neg_le_half`: `y ^ (-s) ≤ 1 / 2` for `2 ≤ y` and `1 ≤ s`.
* `Real.exists_pos_lt_one_lt_rpow`: for `θ < 1` and any `β`, some `τ ∈ (0, 1)` has `θ < τ ^ β`.
* `Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow` and
  `Real.rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow`: the tangent-line inequalities for `u ↦ u ^ p`.
* `Real.one_sub_rpow_add_rpow_pos`: `0 < (1 - t) ^ r + t ^ r` for `t ∈ [0, 1]`.
* `Real.floor_mul_add_one_pow_lt`: `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n` for `1 ≤ C`, `D < n` and
  `C ^ (D / (n - D)) < B + 1`.
* `Real.one_add_sq_rpow_neg_le`: `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k` for `0 < t`.
* `Real.rpow_neg_le_one_div_two_mul_sq`: `d ^ (-p) ≤ 1 / (2 d ^ 2)` for `2 ≤ d ^ (p - 2)`.
* `Real.rpow_le_two_mul_rpow_of_le_two_mul`: `r ^ p ≤ 2 h ^ p` for `0 ≤ r ≤ 2 h` and
  `0 ≤ p ≤ 1`.
* `Real.lt_log_div_log_of_rpow_lt`: `t < log q' / log q` for `2 ≤ q ≤ q'`,
  `q ^ p < q (q + q')` and `log 2 < (p - 1 - t) log q`.
* `Real.min_rpow_lt_two_rpow_sub_one_mul`: `min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q)`
  for `1 < q`, `0 < δ ≤ 1` and `0 ≤ r ≤ 1`.
* `Real.exists_rpow_le_of_le_add_of_le_two_sub_mul`: the uniform strict power mean inequality.
* `TauCeti.rpow_neg_le_exp`: `t ^ (-ε) ≤ exp A` for `0 < t ≤ 1`, `0 ≤ A` and `ε ≤ A t`.
* `TauCeti.one_add_norm_add_rpow_le`: `(1 + ‖x + y‖) ^ s ≤ 2 ^ s ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s)`
  for `0 ≤ s`.
* `TauCeti.one_add_norm_add_le`: `1 + ‖x + y‖ ≤ (1 + ‖x‖) (1 + ‖y‖)`.
-/

public section

namespace Real

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

/-- For `θ < 1` and any exponent `β`, some ratio `τ ∈ (0, 1)` has `θ < τ ^ β`. -/
theorem exists_pos_lt_one_lt_rpow {θ : ℝ} (hθ : θ < 1) (β : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ θ < τ ^ β := by
  rcases le_or_gt β 0 with hβ | hβ
  · exact ⟨1 / 2, by norm_num, by norm_num,
      hθ.trans_le (one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) hβ)⟩
  · set c := max ((1 + θ) / 2) (1 / 2)
    have hc0 : 0 < c := lt_max_of_lt_right (by norm_num)
    have hc1 : c < 1 := max_lt (by linarith) (by norm_num)
    refine ⟨c ^ β⁻¹, rpow_pos_of_pos hc0 _, rpow_lt_one hc0.le hc1 (inv_pos.2 hβ), ?_⟩
    rw [← rpow_mul hc0.le, inv_mul_cancel₀ hβ.ne', rpow_one]
    exact lt_max_of_lt_left (by linarith)

/-- **The strict tangent-line inequality for real powers.** For `1 < p` and distinct `u, v ≥ 0`,
`u ↦ u ^ p` lies strictly above its tangent line at `v`. -/
theorem rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow {p u v : ℝ} (hp : 1 < p) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u ≠ v) : v ^ p + p * v ^ (p - 1) * (u - v) < u ^ p := by
  rcases hv.eq_or_lt with rfl | hv
  · rw [zero_rpow (by linarith), zero_rpow (by linarith)]
    simpa using rpow_pos_of_pos (hu.lt_of_ne' huv) p
  · have hs : -1 ≤ (u - v) / v := by
      rw [le_div_iff₀ hv]
      linarith
    have h := one_add_mul_self_lt_rpow_one_add hs (div_ne_zero (sub_ne_zero.2 huv) hv.ne') hp
    have hu_div : 1 + (u - v) / v = u / v := by
      field_simp
      ring
    rw [hu_div, div_rpow hu hv.le, lt_div_iff₀ (rpow_pos_of_pos hv p)] at h
    rw [rpow_sub_one hv.ne']
    calc v ^ p + p * (v ^ p / v) * (u - v) = (1 + p * ((u - v) / v)) * v ^ p := by
          field_simp
      _ < u ^ p := h

/-- **The tangent-line inequality for real powers.** For `1 ≤ p` and `u, v ≥ 0`, `u ↦ u ^ p` lies
above its tangent line at `v`. This is Bernoulli's inequality
`one_add_mul_self_le_rpow_one_add` made homogeneous. -/
theorem rpow_add_mul_rpow_sub_one_mul_sub_le_rpow {p u v : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u)
    (hv : 0 ≤ v) : v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  rcases eq_or_ne u v with rfl | huv
  · simp
  exact (rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow hp hu hv huv).le

/-- For `t ∈ [0, 1]` and any exponent `r`, `(1 - t) ^ r + t ^ r` is positive: at least one of the
two bases is positive. -/
theorem one_sub_rpow_add_rpow_pos (r : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 - t) ^ r + t ^ r := by
  rcases ht.1.eq_or_lt with rfl | ht₀
  · simpa using add_pos_of_pos_of_nonneg zero_lt_one (rpow_nonneg le_rfl r)
  · exact add_pos_of_nonneg_of_pos (rpow_nonneg (sub_nonneg.2 ht.2) r) (rpow_pos_of_pos ht₀ r)

/-- **The counting estimate of Siegel's lemma.** If `1 ≤ C`, `D < n` and
`C ^ (D / (n - D)) < B + 1`, then `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n`: the `(B + 1) ^ n` integer
points of the box `[0, B]^n` outnumber the cells of a partition of `[0, C B]^D` into
`⌊C B⌋₊ + 1` intervals per coordinate. -/
theorem floor_mul_add_one_pow_lt {C : ℝ} (hC : 1 ≤ C) {D n B : ℕ} (hDn : D < n)
    (hB : C ^ ((D : ℝ) / (n - D)) < B + 1) :
    (⌊C * B⌋₊ + 1) ^ D < (B + 1) ^ n := by
  have hnD : (D : ℝ) < n := by exact_mod_cast hDn
  rw [← Nat.cast_lt (α := ℝ)]
  push_cast
  calc ((⌊C * B⌋₊ : ℝ) + 1) ^ D ≤ (C * (B + 1)) ^ D := by
        gcongr
        linarith [Nat.floor_le (by positivity : 0 ≤ C * B)]
    _ = (C ^ ((D : ℝ) / (n - D))) ^ ((n : ℝ) - D) * (B + 1) ^ D := by
        rw [mul_pow, ← rpow_mul (by positivity), div_mul_cancel₀ _ (by linarith), rpow_natCast]
    _ < (B + 1) ^ ((n : ℝ) - D) * (B + 1) ^ D := by gcongr
    _ = (B + 1) ^ n := by
        rw [← rpow_natCast _ D, ← rpow_add (by positivity), sub_add_cancel, rpow_natCast]

/-- For `t > 0`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`. -/
theorem one_add_sq_rpow_neg_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (1 + t ^ 2) ^ (-(k : ℝ) / 2) ≤ 1 / t ^ k := by
  have hpow : t ^ k ≤ (1 + t ^ 2) ^ ((k : ℝ) / 2) := by
    calc t ^ k = (t ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul ht.le]
          ring_nf
      _ ≤ _ := rpow_le_rpow (by positivity) (by linarith) (by positivity)
  rw [neg_div, rpow_neg (by positivity), ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- If `0 < d` and `2 ≤ d ^ (p - 2)`, then `d ^ (-p) ≤ 1 / (2 d ^ 2)`. -/
theorem rpow_neg_le_one_div_two_mul_sq {d p : ℝ} (hd : 0 < d) (h2 : 2 ≤ d ^ (p - 2)) :
    d ^ (-p) ≤ 1 / (2 * d ^ 2) := by
  have hsplit : d ^ (-p) = (d ^ (p - 2))⁻¹ * (d ^ 2)⁻¹ := by
    rw [← rpow_neg hd.le, ← rpow_natCast, ← rpow_neg hd.le, ← rpow_add hd]
    congr 1
    push_cast
    ring
  rw [hsplit, one_div, mul_inv]
  gcongr

/-- For `0 ≤ p ≤ 1`, a quantity at most `2 h` has `p`-th power at most `2 h^p`. -/
theorem rpow_le_two_mul_rpow_of_le_two_mul {r h p : ℝ} (hr : 0 ≤ r) (hrh : r ≤ 2 * h)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : r ^ p ≤ 2 * h ^ p := by
  have hh : 0 ≤ h := by linarith
  calc r ^ p ≤ (2 * h) ^ p := by gcongr
    _ = 2 ^ p * h ^ p := mul_rpow (by norm_num) hh
    _ ≤ 2 * h ^ p := by
        gcongr
        exact (rpow_le_rpow_of_exponent_le (by norm_num) hp₁).trans (rpow_one 2).le

/-- The logarithmic form of `q ^ p < q (q + q')`: if moreover `2 ≤ q ≤ q'` and
`log 2 < (p - 1 - t) log q`, then `t < log q' / log q`. -/
theorem lt_log_div_log_of_rpow_lt {q q' p t : ℝ} (hq : 2 ≤ q) (hqq' : q ≤ q')
    (hpow : q ^ p < q * (q + q')) (hlog2 : log 2 < (p - 1 - t) * log q) :
    t < log q' / log q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < log q := log_pos (by linarith)
  have hpow' : q ^ (p - 1) < 2 * q' := by
    rw [rpow_sub_one hq0.ne', div_lt_iff₀ hq0]
    nlinarith
  have hlogs : (p - 1) * log q < log 2 + log q' := by
    rw [← log_rpow hq0, ← log_mul two_ne_zero (by linarith)]
    exact log_lt_log (rpow_pos_of_pos hq0 _) hpow'
  rw [lt_div_iff₀ hlog]
  nlinarith

/-- For `1 < q`, `0 < δ ≤ 1` and `0 ≤ r ≤ 1`,
`min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q)`: for `r < 1` by strict convexity of
`t ↦ t ^ q`, and for `r = 1` because `0 ≤ 2 - δ < 2`. -/
theorem min_rpow_lt_two_rpow_sub_one_mul {q δ r : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q) := by
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := rpow_sub_one two_ne_zero q
  have hmin0 : 0 ≤ min (1 + r) (2 - δ) := le_min (by linarith) (by linarith)
  rcases hr1.lt_or_eq with hr1 | rfl
  · have hstrict := (strictConvexOn_rpow hq).2 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 hr0)
      hr1.ne' (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul, one_rpow] at hstrict
    have hle : min (1 + r) (2 - δ) ^ q ≤ (1 + r) ^ q :=
      rpow_le_rpow hmin0 (min_le_left _ _) hq0.le
    have hhalf : (1 + r) ^ q = 2 ^ q * (1 / 2 * 1 + 1 / 2 * r) ^ q := by
      rw [← mul_rpow zero_le_two (by positivity)]
      ring_nf
    have := mul_lt_mul_of_pos_left hstrict (by positivity : (0 : ℝ) < 2 ^ q)
    rw [h2sub]
    nlinarith
  · have hlt : min (1 + 1) (2 - δ) ^ q < 2 ^ q :=
      rpow_lt_rpow hmin0 ((min_le_right _ _).trans_lt (by linarith)) hq0
    have h2 : (2 : ℝ) ^ q / 2 * (1 + 1) = 2 ^ q := by ring
    rwa [one_rpow, h2sub, h2]

/-- **A uniform strict power mean inequality.** For `1 < q` and `0 < δ ≤ 1` there is `κ > 0`
such that `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever
`0 ≤ t ≤ s` and `0 ≤ u ≤ min (s + t) ((2 - δ) * s)`. After rescaling to `s = 1`, the gap
between the two sides is a continuous positive function of `t ∈ [0, 1]`, so it has a positive
minimum. This is the scalar part of `TauCeti.exists_forall_norm_add_rpow_le`. -/
theorem exists_rpow_le_of_le_add_of_le_two_sub_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ κ, 0 < κ ∧ ∀ s t u : ℝ, 0 ≤ t → t ≤ s → 0 ≤ u → u ≤ s + t → u ≤ (2 - δ) * s →
      u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := rpow_sub_one two_ne_zero q
  -- The gap between the two sides after rescaling to `s = 1`.
  set φ : ℝ → ℝ := fun r ↦ 2 ^ (q - 1) * (1 + r ^ q) - min (1 + r) (2 - δ) ^ q with hφ
  have hφc : Continuous φ := by
    have := continuous_rpow_const hq0.le
    fun_prop
  obtain ⟨r₀, hr₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hφc.continuousOn
  have hm : 0 < φ r₀ := sub_pos.2 (min_rpow_lt_two_rpow_sub_one_mul hq hδ hδ1 hr₀.1 hr₀.2)
  refine ⟨φ r₀ / 2 ^ q, by positivity, fun s t u ht hts hu hus hu2 ↦ ?_⟩
  rcases (ht.trans hts).eq_or_lt with rfl | hs
  · obtain rfl : t = 0 := le_antisymm hts ht
    obtain rfl : u = 0 := le_antisymm (by simpa using hus) hu
    simp [zero_rpow hq0.ne']
  set r := t / s with hr_def
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht hs.le, div_le_one_of_le₀ hts hs.le⟩
  have hv : u / s ≤ min (1 + r) (2 - δ) := by
    refine le_min ?_ ?_ <;> rw [div_le_iff₀ hs]
    · rw [hr_def, add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
      exact hus
    · linarith
  have hrq : r ^ q ≤ 1 := rpow_le_one hr.1 hr.2 hq0.le
  have hgap : φ r₀ ≤ φ r := hmin hr
  have hvq : (u / s) ^ q ≤ min (1 + r) (2 - δ) ^ q :=
    rpow_le_rpow (div_nonneg hu hs.le) hv hq0.le
  have key : (u / s) ^ q ≤ (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) := by
    simp only [hφ] at hgap
    have hrq0 : 0 ≤ r ^ q := rpow_nonneg hr.1 q
    have : (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) =
        2 ^ (q - 1) * (1 + r ^ q) - φ r₀ * ((1 + r ^ q) / 2) := by
      rw [h2sub]
      field_simp
    rw [this]
    nlinarith
  have hsq : 0 < s ^ q := rpow_pos_of_pos hs q
  calc u ^ q = s ^ q * (u / s) ^ q := by
        rw [div_rpow hu hs.le, mul_div_cancel₀ _ hsq.ne']
    _ ≤ s ^ q * ((1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q)) := by gcongr
    _ = (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hr_def, div_rpow ht hs.le]
        field_simp

end Real

namespace TauCeti

/-- A power of a radius in `(0, 1]` with exponent controlled by the radius itself is uniformly
bounded: if `0 < t ≤ 1` and `ε ≤ A t` with `A ≥ 0`, then `t ^ (-ε) ≤ exp A`. -/
theorem rpow_neg_le_exp {t ε A : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hA : 0 ≤ A) (hε : ε ≤ A * t) :
    t ^ (-ε) ≤ Real.exp A := by
  rw [Real.rpow_def_of_pos ht, Real.exp_le_exp]
  have hlog : 0 ≤ -Real.log t := neg_nonneg.2 (Real.log_nonpos ht.le ht1)
  have htlog : t * -Real.log t ≤ 1 := by
    rw [mul_neg, mul_comm]
    exact (neg_le_abs _).trans (Real.abs_log_mul_self_lt t ht ht1).le
  calc Real.log t * -ε = -Real.log t * ε := by ring
    _ ≤ -Real.log t * (A * t) := mul_le_mul_of_nonneg_left hε hlog
    _ = A * (t * -Real.log t) := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left htlog hA
    _ = A := mul_one A

/-- The weight `(1 + ‖x‖) ^ s` is subadditive up to a constant: for `s ≥ 0`,
`(1 + ‖x + y‖) ^ s ≤ 2 ^ s ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s)`. -/
theorem one_add_norm_add_rpow_le {E : Type*} [SeminormedAddGroup E] {s : ℝ} (hs : 0 ≤ s)
    (x y : E) :
    (1 + ‖x + y‖) ^ s ≤ 2 ^ s * ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s) := by
  have hx : 0 ≤ 1 + ‖x‖ := by positivity
  have hy : 0 ≤ 1 + ‖y‖ := by positivity
  calc (1 + ‖x + y‖) ^ s ≤ (2 * max (1 + ‖x‖) (1 + ‖y‖)) ^ s := by
        gcongr
        linarith [norm_add_le x y, le_max_left (1 + ‖x‖) (1 + ‖y‖),
          le_max_right (1 + ‖x‖) (1 + ‖y‖)]
    _ = 2 ^ s * max (1 + ‖x‖) (1 + ‖y‖) ^ s :=
        Real.mul_rpow zero_le_two (hx.trans (le_max_left _ _))
    _ ≤ 2 ^ s * ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s) := by
        gcongr
        rcases le_total (1 + ‖x‖) (1 + ‖y‖) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (Real.rpow_nonneg hx s)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (Real.rpow_nonneg hy s)

/-- The weight `1 + ‖x‖` is submultiplicative: `1 + ‖x + y‖ ≤ (1 + ‖x‖) (1 + ‖y‖)`. -/
theorem one_add_norm_add_le {E : Type*} [SeminormedAddGroup E] (x y : E) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  nlinarith [norm_add_le x y, norm_nonneg x, norm_nonneg y,
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

end TauCeti
