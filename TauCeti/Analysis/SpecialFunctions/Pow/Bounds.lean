/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Elementary bounds on real powers

For `0 < x` and `|log x · y| ≤ 1`, `|x ^ y - 1| ≤ 2 |log x · y|`: a power with a small
logarithm is close to `1`. Likewise, for `0 < u` and any
exponent `p ∈ [p₁, p₂]`, `u ^ p ≤ u ^ p₁ + u ^ p₂`, which dominates `u ^ (Re s - 1)` for all
`u > 0` by the sum of its endpoint powers as `s` varies in a vertical strip `σ₁ ≤ Re s ≤ σ₂`; and
for `0 < a ≤ u` and `s ≤ t`, `u ^ s ≤ a ^ (s - t) * u ^ t` raises the exponent on `(a, ∞)`.

A base at least `2` raised to a negative exponent of size at least `1` is at most `1 / 2`. This
is the shape in which the local ratio of an Euler factor is bounded away from `1`, so that the
denominator `1 - y ^ (-s)` stays bounded below.

A negative power reverses a comparison up to a constant: if `0 < x ≤ a y` with `a ≥ 0` (so that
`a` and `y` are positive), then `y ^ (-q) ≤ a ^ q x ^ (-q)` for `q ≥ 0`. This dominates a
power `y ^ (-q)` by a shifted power such as `(T + |s|) ^ (-q)` when `T + |s|` is at most a
multiple of `y`, as in splitting an integral of a decaying integrand.

For any `θ < 1` and any exponent `β`, some base `τ ∈ (0, 1)` has `θ < τ ^ β`. This is how a
geometric ratio is chosen in iteration arguments, such as the absorption lemma.

For `0 < α` and `0 < b`, every multiple `c r ^ α` is at most `b` for some `r ∈ (0, 1]`. This is
how a small scale is chosen to absorb a term `c r ^ α X` into `X` in a priori estimates.

For `1 ≤ p`, the graph of `u ↦ u ^ p` on `[0, ∞)` lies above each of its tangent lines:
`v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p`, strictly so when `1 < p` and `u ≠ v`. Conversely,
for `0 ≤ p ≤ 1`, `u ≥ 0`, and `v > 0`, concavity reverses the inequality:
`u ^ p ≤ v ^ p + p * v ^ (p - 1) * (u - v)`. These are the convex and concave forms of
Bernoulli's inequality made homogeneous, giving first-order optimality tests and secant-tangent
comparisons for real powers.

For `t ∈ [0, 1]` and any exponent `r`, the sum `(1 - t) ^ r + t ^ r` is positive, so it can be
used as the normalizing denominator of a pair of weights.

If `1 ≤ C`, `D < n` and `C ^ (D / (n - D)) < B + 1`, then `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n`. This
is the counting step of Siegel's lemma: it compares the integer points of a box with the cells
of a partition of the image of that box under `D` linear forms.

If `2 ≤ d ^ (p - 2)`, then `d ^ (-p) ≤ 1 / (2 d ^ 2)`. So when `d` is the reduced denominator of
a rational `q`, an error `|ξ - q|` strictly below `d ^ (-p)` is strictly below `1 / (2 d ^ 2)`,
which is the hypothesis of Legendre's theorem `Real.exists_rat_eq_convergent`.

For `0 ≤ p ≤ 1`, a nonnegative quantity `r ≤ 2 h` has `r ^ p ≤ 2 h ^ p`. This is how, in a
temporal Hölder estimate with exponent `p`, a time at most twice the time step `h` is bounded by
a multiple of `h ^ p`. Consequently, if two points `x` and `y` of a pseudometric space lie within
`c t ^ p` and `c t' ^ p` of a common point, with `0 ≤ c`, `0 ≤ t ≤ 2 h` and `0 ≤ t' ≤ h`, then
`dist x y ≤ 3 c h ^ p`.

If `2 ≤ q ≤ q'` and `q ^ p < q (q + q')`, then `q ^ (p - 1) < 2 q'`, so
`(p - 1) log q < log 2 + log q'`. Hence `t < log q' / log q` once `log 2 < (p - 1 - t) log q`.
This reads off the growth of consecutive continued-fraction denominators from the lower error
bound `1 / (q (q + q')) < |ξ - p / q|`.

For `s ≥ 0` the weight `(1 + ‖x‖) ^ s` on a seminormed group is subadditive up to the constant
`2 ^ s`. This is the weight inequality behind product estimates in weighted sequence spaces. The
weight `1 + ‖x‖` itself is submultiplicative: `1 + ‖x + y‖ ≤ (1 + ‖x‖) (1 + ‖y‖)`. For a
nonpositive exponent `p` and points at distance at most `1`, the weight `(1 + ‖x‖) ^ p` at `x`
is at most `2 ^ (-p)` times the weight at `y`; this compares a weight on a unit interval with its
value at an endpoint.

For nonpositive exponents `α ≤ 0`, `t ↦ t ^ α` is antitone on `(0, ∞)`, so unit-step differences
of the antiderivative `t ↦ t ^ (α + 1) / (α + 1)` bracket `x ^ α`:
`((x + 1) ^ (α + 1) - x ^ (α + 1)) / (α + 1) ≤ x ^ α` for every `0 < x` and `α ≤ 0`, and
`x ^ α ≤ (x ^ (α + 1) - (x - 1) ^ (α + 1)) / (α + 1)` for `1 ≤ x` and `-1 < α ≤ 0` (including the
endpoint `x = 1` where `(x - 1) ^ (α + 1) = 0`). Telescoping these bounds controls discrete power
sums `∑ j ^ α` in the sublinear regime `-1 < α ≤ 0`.

For every real exponent `β` and `0 ≤ t ≤ x`, `(x + t) ^ β ≤ max 1 (2 ^ β) * x ^ β`, bounding a
power of either sign uniformly across `[x, 2 * x]` as needed for derivative remainder bounds on
dyadic intervals.

## Main results

* `Real.abs_rpow_sub_one_le`: `|x ^ y - 1| ≤ 2 |log x · y|` for `0 < x` and `|log x · y| ≤ 1`.
* `Real.rpow_le_rpow_add_rpow_of_mem_Icc`: `u ^ p ≤ u ^ p₁ + u ^ p₂` for `0 < u` and
  `p ∈ Set.Icc p₁ p₂`.
* `Real.rpow_le_rpow_sub_mul_rpow_of_exponent_le`: `u ^ s ≤ a ^ (s - t) * u ^ t` for `0 < a ≤ u`
  and `s ≤ t`.
* `Real.rpow_neg_le_half`: `y ^ (-s) ≤ 1 / 2` for `2 ≤ y` and `1 ≤ s`.
* `Real.rpow_neg_le_mul_rpow_neg`: `y ^ (-q) ≤ a ^ q x ^ (-q)` for `0 < x ≤ a y`, `a ≥ 0` and
  `q ≥ 0`.
* `Real.exists_pos_lt_one_lt_rpow`: for `θ < 1` and any `β`, some `τ ∈ (0, 1)` has `θ < τ ^ β`.
* `Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow`,
  `Real.rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow`, and
  `Real.rpow_le_rpow_add_mul_rpow_sub_one_mul_sub`: convex and concave tangent-line inequalities
  for `u ↦ u ^ p`.
* `Real.one_sub_rpow_add_rpow_pos`: `0 < (1 - t) ^ r + t ^ r` for `t ∈ [0, 1]`.
* `Real.floor_mul_add_one_pow_lt`: `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n` for `1 ≤ C`, `D < n` and
  `C ^ (D / (n - D)) < B + 1`.
* `Real.rpow_neg_le_one_div_two_mul_sq`: `d ^ (-p) ≤ 1 / (2 d ^ 2)` for `2 ≤ d ^ (p - 2)`.
* `Real.rpow_le_two_mul_rpow_of_le_two_mul`: `r ^ p ≤ 2 h ^ p` for `0 ≤ r ≤ 2 h` and
  `0 ≤ p ≤ 1`.
* `Real.lt_log_div_log_of_rpow_lt`: `t < log q' / log q` for `2 ≤ q ≤ q'`,
  `q ^ p < q (q + q')` and `log 2 < (p - 1 - t) log q`.
* `Real.rpow_le_rpow_sub_sub_one_rpow_div` and `Real.add_one_rpow_sub_rpow_div_le_rpow`: unit
  backward- and forward-difference bounds on `t ↦ t ^ (α + 1) / (α + 1)` comparing with `x ^ α`
  for `α ≤ 0`.
* `Real.add_rpow_le_max_two_rpow_mul`: `(x + t) ^ β ≤ max 1 (2 ^ β) * x ^ β` for `0 ≤ t ≤ x`
  and every real `β`.
* `TauCeti.one_add_norm_add_rpow_le`: `(1 + ‖x + y‖) ^ s ≤ 2 ^ s ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s)`
  for `0 ≤ s`.
* `TauCeti.one_add_norm_add_le`: `1 + ‖x + y‖ ≤ (1 + ‖x‖) (1 + ‖y‖)`.
* `TauCeti.one_add_norm_add_rpow_le_mul`: `(1 + ‖x + y‖) ^ p ≤ (1 + ‖x‖) ^ |p| * (1 + ‖y‖) ^ p`
  for any `p : ℝ`.
* `TauCeti.one_add_norm_rpow_le_two_rpow_mul_of_norm_sub_le_one` and
  `TauCeti.one_add_norm_rpow_le_two_rpow_abs_mul_of_norm_sub_le_one`:
  `(1 + ‖x‖) ^ p ≤ 2 ^ |p| (1 + ‖y‖) ^ p` when `x` and `y` are at distance at most `1`.
* `TauCeti.rpow_mul_rpow_le_max`, `Prod.norm_fst_rpow_mul_norm_snd_rpow_le`, and
  `TauCeti.le_rpow_mul_rpow_mul_of_forall_pos`: `a ^ (1 - x) * b ^ x ≤ max a b` on `[0, 1]`, its
  product-seminorm corollary `‖p.1‖ ^ (1 - x) * ‖p.2‖ ^ x ≤ ‖p‖`, and right-continuity at `ε = 0`
  of `(M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * C` for `θ ∈ [0, 1]`.
-/

public section

namespace Real

/-- For `0 < x` and `|log x · y| ≤ 1`, `|x ^ y - 1| ≤ 2 |log x · y|`. -/
theorem abs_rpow_sub_one_le {x y : ℝ} (hx : 0 < x) (h : |log x * y| ≤ 1) :
    |x ^ y - 1| ≤ 2 * |log x * y| := by
  rw [rpow_def_of_pos hx]
  exact abs_exp_sub_one_le h

/-- For `0 < u` and `p ∈ Set.Icc p₁ p₂`, `u ^ p ≤ u ^ p₁ + u ^ p₂`. -/
theorem rpow_le_rpow_add_rpow_of_mem_Icc {u p p₁ p₂ : ℝ} (hu : 0 < u) (hp : p ∈ Set.Icc p₁ p₂) :
    u ^ p ≤ u ^ p₁ + u ^ p₂ := by
  rcases le_total u 1 with hu1 | hu1
  · exact le_add_of_le_of_nonneg (rpow_le_rpow_of_exponent_ge hu hu1 hp.1) (by positivity)
  · exact le_add_of_nonneg_of_le (by positivity) (rpow_le_rpow_of_exponent_le hu1 hp.2)

/-- For `0 < a ≤ u` and `s ≤ t`, `u ^ s ≤ a ^ (s - t) * u ^ t`. -/
theorem rpow_le_rpow_sub_mul_rpow_of_exponent_le {a u s t : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hst : s ≤ t) : u ^ s ≤ a ^ (s - t) * u ^ t :=
  calc u ^ s = u ^ (s - t) * u ^ t := by rw [← rpow_add (ha.trans_le hau), sub_add_cancel]
    _ ≤ a ^ (s - t) * u ^ t :=
      mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos ha hau (sub_nonpos.2 hst))
        (rpow_nonneg (ha.le.trans hau) t)

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

/-- A negative power reverses a comparison up to a constant: if `0 < x ≤ a y` with `a ≥ 0` and
`q ≥ 0`, then `y ^ (-q) ≤ a ^ q x ^ (-q)`. The hypotheses force `a > 0` and `y > 0`. -/
theorem rpow_neg_le_mul_rpow_neg {x y a q : ℝ} (hx : 0 < x) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hxy : x ≤ a * y) : y ^ (-q) ≤ a ^ q * x ^ (-q) := by
  have hay : 0 < a * y := hx.trans_le hxy
  have hy : 0 < y := pos_of_mul_pos_right hay ha
  replace ha : 0 < a := pos_of_mul_pos_left hay hy.le
  have h1 : (a * y) ^ (-q) ≤ x ^ (-q) := rpow_le_rpow_of_nonpos hx hxy (by linarith)
  rw [mul_rpow ha.le hy.le, rpow_neg ha.le] at h1
  calc y ^ (-q) = a ^ q * ((a ^ q)⁻¹ * y ^ (-q)) :=
        (mul_inv_cancel_left₀ (rpow_pos_of_pos ha q).ne' _).symm
    _ ≤ a ^ q * x ^ (-q) := by gcongr

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

/-- For `0 < α` and `0 < b`, every multiple `c r ^ α` is at most `b` for some `r ∈ (0, 1]`, since
`r ^ α → 0` as `r → 0`. -/
theorem exists_pos_le_one_mul_rpow_le (c : ℝ) {α b : ℝ} (hα : 0 < α) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ c * r ^ α ≤ b := by
  have ht : Filter.Tendsto (fun r : ℝ => c * r ^ α) (nhds 0) (nhds (c * 0 ^ α)) :=
    ((continuous_rpow_const hα.le).tendsto 0).const_mul c
  rw [zero_rpow hα.ne', mul_zero] at ht
  obtain ⟨r, ⟨hrb, hr1⟩, hr⟩ := ((eventually_nhdsWithin_of_eventually_nhds
    (s := Set.Ioi 0) ((ht.eventually (eventually_le_nhds hb)).and (eventually_le_nhds one_pos))).and
    self_mem_nhdsWithin).exists
  exact ⟨r, hr, hr1, hrb⟩

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

/-- **The concave tangent-line inequality for real powers.** For `0 ≤ p ≤ 1`, `0 ≤ u`, and `0 < v`,
`u ↦ u ^ p` lies below its tangent line at `v`. This is Bernoulli's inequality
`rpow_one_add_le_one_add_mul_self` made homogeneous. -/
theorem rpow_le_rpow_add_mul_rpow_sub_one_mul_sub {p u v : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hu : 0 ≤ u) (hv : 0 < v) : u ^ p ≤ v ^ p + p * v ^ (p - 1) * (u - v) := by
  have hs : -1 ≤ (u - v) / v := by
    rw [le_div_iff₀ hv]
    linarith
  have h := rpow_one_add_le_one_add_mul_self hs hp₀ hp₁
  have hu_div : 1 + (u - v) / v = u / v := by
    field_simp
    ring
  rw [hu_div, div_rpow hu hv.le, div_le_iff₀ (rpow_pos_of_pos hv p)] at h
  rw [rpow_sub_one hv.ne']
  calc u ^ p ≤ (1 + p * ((u - v) / v)) * v ^ p := h
    _ = v ^ p + p * (v ^ p / v) * (u - v) := by field_simp

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

/-- If `2 ≤ d ^ (p - 2)`, then `d ^ (-p) ≤ 1 / (2 d ^ 2)`. (For `d = 0` the hypothesis fails, as
`0 ^ x ≤ 1`.) -/
theorem rpow_neg_le_one_div_two_mul_sq {d p : ℝ} (h2 : 2 ≤ d ^ (p - 2)) :
    d ^ (-p) ≤ 1 / (2 * d ^ 2) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · linarith [zero_rpow_le_one (p - 2)]
  have hd : 0 < |d| := abs_pos.2 hd0
  have h2' : 2 ≤ |d| ^ (p - 2) :=
    h2.trans ((le_abs_self _).trans (abs_rpow_le_abs_rpow _ _))
  have hsplit : |d| ^ (-p) = (|d| ^ (p - 2))⁻¹ * (|d| ^ 2)⁻¹ := by
    rw [← rpow_neg hd.le, ← rpow_natCast, ← rpow_neg hd.le, ← rpow_add hd]
    congr 1
    push_cast
    ring
  calc d ^ (-p) ≤ |d| ^ (-p) := (le_abs_self _).trans (abs_rpow_le_abs_rpow _ _)
    _ = (|d| ^ (p - 2))⁻¹ * (|d| ^ 2)⁻¹ := hsplit
    _ ≤ 2⁻¹ * (d ^ 2)⁻¹ := by
        rw [sq_abs]
        gcongr
    _ = 1 / (2 * d ^ 2) := by rw [one_div, mul_inv]

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

/-- For `-1 < α ≤ 0` and `1 ≤ x`, `x ^ α` is bounded above by the unit backward difference of
`t ↦ t ^ (α + 1) / (α + 1)` (at `x = 1`, `(x - 1) ^ (α + 1) = 0` requires `-1 < α`). -/
theorem rpow_le_rpow_sub_sub_one_rpow_div {α : ℝ} (hα : -1 < α) (hα₀ : α ≤ 0) {x : ℝ}
    (hx : 1 ≤ x) :
    x ^ α ≤ (x ^ (α + 1) - (x - 1) ^ (α + 1)) / (α + 1) := by
  have hα₁ : 0 < α + 1 := by linarith
  have h := rpow_le_rpow_add_mul_rpow_sub_one_mul_sub (p := α + 1) (u := x - 1) (v := x)
    hα₁.le (by linarith) (by linarith) (by linarith)
  have hsub : x - 1 - x = -1 := by ring
  rw [add_sub_cancel_right, hsub, mul_neg_one] at h
  rw [le_div_iff₀ hα₁]
  linarith

/-- For `α ≤ 0` and `0 < x`, `x ^ α` is bounded below by the unit forward difference of
`t ↦ t ^ (α + 1) / (α + 1)`. -/
theorem add_one_rpow_sub_rpow_div_le_rpow {α : ℝ} (hα₀ : α ≤ 0) {x : ℝ} (hx : 0 < x) :
    ((x + 1) ^ (α + 1) - x ^ (α + 1)) / (α + 1) ≤ x ^ α := by
  rcases lt_trichotomy (α + 1) 0 with hlt | heq | hgt
  · have hprod : x ^ (α + 1) * (1 + x⁻¹) ^ (α + 1) = (x + 1) ^ (α + 1) := by
      rw [← mul_rpow hx.le (by positivity), mul_add, mul_one, mul_inv_cancel₀ hx.ne']
    have hrhs : x ^ (α + 1) * (1 + (α + 1) * x⁻¹) = x ^ (α + 1) + (α + 1) * x ^ α := by
      rw [rpow_add_one hx.ne']
      field_simp
    have hlog : log (1 + x⁻¹) ≤ x⁻¹ := by
      linarith [log_le_sub_one_of_pos (by positivity : 0 < 1 + x⁻¹)]
    have hbern : 1 + (α + 1) * x⁻¹ ≤ (1 + x⁻¹) ^ (α + 1) := by
      rw [rpow_def_of_pos (by positivity)]
      linarith [(add_one_le_exp (x⁻¹ * (α + 1))).trans
        (exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlog hlt.le))]
    have hmul := mul_le_mul_of_nonneg_left hbern (rpow_nonneg hx.le (α + 1))
    rw [hprod, hrhs] at hmul
    rw [div_le_iff_of_neg hlt]
    linarith
  · rw [heq, div_zero]
    positivity
  · have h := rpow_le_rpow_add_mul_rpow_sub_one_mul_sub (p := α + 1) (u := x + 1) (v := x)
      hgt.le (by linarith) (by positivity) hx
    rw [add_sub_cancel_right, add_sub_cancel_left, mul_one] at h
    rw [div_le_iff₀ hgt]
    linarith

/-- On `[x, 2 * x]`, a real power `(x + t) ^ β` of either sign is bounded above by
`max 1 (2 ^ β) * x ^ β` whenever `0 ≤ t ≤ x` (including at `x = t = 0`). -/
theorem add_rpow_le_max_two_rpow_mul (β : ℝ) {x t : ℝ} (ht₀ : 0 ≤ t) (htx : t ≤ x) :
    (x + t) ^ β ≤ max 1 (2 ^ β) * x ^ β := by
  rcases (ht₀.trans htx).eq_or_lt with rfl | hx
  · obtain rfl : t = 0 := le_antisymm htx ht₀
    rw [add_zero]
    exact le_mul_of_one_le_left (rpow_nonneg le_rfl β) (le_max_left 1 (2 ^ β))
  · have hxt : 0 < x + t := by linarith
    rcases le_total 0 β with hβ | hβ
    · calc (x + t) ^ β ≤ (2 * x) ^ β := rpow_le_rpow hxt.le (by linarith) hβ
        _ = 2 ^ β * x ^ β := mul_rpow zero_le_two hx.le
        _ ≤ max 1 (2 ^ β) * x ^ β :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_nonneg hx.le β)
    · calc (x + t) ^ β ≤ x ^ β := rpow_le_rpow_of_nonpos hx (by linarith) hβ
        _ = 1 * x ^ β := (one_mul _).symm
        _ ≤ max 1 (2 ^ β) * x ^ β :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg hx.le β)

end Real

namespace TauCeti

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

/-- Multiplicative shift bound (Peetre's inequality) for the weight `1 + ‖x‖`: for every real
exponent `p`, `(1 + ‖x + y‖) ^ p ≤ (1 + ‖x‖) ^ |p| * (1 + ‖y‖) ^ p`. -/
theorem one_add_norm_add_rpow_le_mul {E : Type*} [SeminormedAddGroup E] (p : ℝ) (x y : E) :
    (1 + ‖x + y‖) ^ p ≤ (1 + ‖x‖) ^ |p| * (1 + ‖y‖) ^ p := by
  rcases le_total 0 p with hp | hp
  · calc (1 + ‖x + y‖) ^ p ≤ ((1 + ‖x‖) * (1 + ‖y‖)) ^ p :=
            Real.rpow_le_rpow (by positivity) (one_add_norm_add_le x y) hp
      _ = (1 + ‖x‖) ^ |p| * (1 + ‖y‖) ^ p := by
            rw [Real.mul_rpow (by positivity) (by positivity), abs_of_nonneg hp]
  · have h1 : (1 + ‖y‖) * (1 + ‖x‖)⁻¹ ≤ 1 + ‖x + y‖ := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      simpa only [neg_add_cancel_left, norm_neg, mul_comm] using one_add_norm_add_le (-x) (x + y)
    calc (1 + ‖x + y‖) ^ p ≤ ((1 + ‖y‖) * (1 + ‖x‖)⁻¹) ^ p :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 hp
      _ = (1 + ‖x‖) ^ |p| * (1 + ‖y‖) ^ p := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
              ← Real.rpow_neg (by positivity), abs_of_nonpos hp, mul_comm]

/-- For a nonpositive exponent `p` and points at distance at most `1`, the weight
`(1 + ‖x‖) ^ p` is bounded by `2 ^ (-p)` times its value at `y`. -/
theorem one_add_norm_rpow_le_two_rpow_mul_of_norm_sub_le_one {E : Type*} [SeminormedAddGroup E]
    {p : ℝ} (hp : p ≤ 0) {x y : E} (h : ‖y - x‖ ≤ 1) :
    (1 + ‖x‖) ^ p ≤ (2 : ℝ) ^ (-p) * (1 + ‖y‖) ^ p := by
  have hy : ‖y‖ ≤ 1 + ‖x‖ := (norm_le_norm_sub_add y x).trans (by gcongr)
  have hbase : (1 + ‖y‖) / 2 ≤ 1 + ‖x‖ := by
    linarith [norm_nonneg x]
  calc
    (1 + ‖x‖) ^ p ≤ ((1 + ‖y‖) / 2) ^ p :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbase hp
    _ = (2 : ℝ) ^ (-p) * (1 + ‖y‖) ^ p := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
      ring

/-- For any real exponent `p` and points at distance at most `1`, the weight `(1 + ‖x‖) ^ p` is
bounded by `2 ^ |p|` times its value at `y`. -/
theorem one_add_norm_rpow_le_two_rpow_abs_mul_of_norm_sub_le_one {E : Type*}
    [SeminormedAddGroup E] (p : ℝ) {x y : E} (h : ‖x - y‖ ≤ 1) :
    (1 + ‖x‖) ^ p ≤ (2 : ℝ) ^ |p| * (1 + ‖y‖) ^ p := by
  calc (1 + ‖x‖) ^ p = (1 + ‖(x - y) + y‖) ^ p := by rw [sub_add_cancel]
    _ ≤ (1 + ‖x - y‖) ^ |p| * (1 + ‖y‖) ^ p := one_add_norm_add_rpow_le_mul p (x - y) y
    _ ≤ (2 : ℝ) ^ |p| * (1 + ‖y‖) ^ p := by
        gcongr
        linarith

/-- For `0 ≤ a`, `0 ≤ b`, and `x ∈ [0, 1]`, the geometric interpolant `a ^ (1 - x) * b ^ x` is at
most `max a b`. -/
theorem rpow_mul_rpow_le_max {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    a ^ (1 - x) * b ^ x ≤ max a b := by
  calc a ^ (1 - x) * b ^ x
      ≤ max a b ^ (1 - x) * max a b ^ x :=
        mul_le_mul (Real.rpow_le_rpow ha (le_max_left a b) (sub_nonneg.2 hx.2))
          (Real.rpow_le_rpow hb (le_max_right a b) hx.1)
          (Real.rpow_nonneg hb _) (Real.rpow_nonneg (ha.trans (le_max_left a b)) _)
    _ = max a b := by
        rw [← Real.rpow_add' (ha.trans (le_max_left a b)) (by simp), sub_add_cancel, Real.rpow_one]

/-- Continuity from the right of `(M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * C` at `ε = 0` for
`θ ∈ [0, 1]`, used to pass Riesz–Thorin bounds from positive endpoint constants to nonnegative
ones. -/
theorem le_rpow_mul_rpow_mul_of_forall_pos {A M₀ M₁ θ C : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hle : ∀ ε > 0, A ≤ (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * C) :
    A ≤ M₀ ^ (1 - θ) * M₁ ^ θ * C := by
  have hcont : Continuous fun ε : ℝ ↦ (M₀ + ε) ^ (1 - θ) * (M₁ + ε) ^ θ * C :=
    (((continuous_const.add continuous_id).rpow_const fun _ ↦ Or.inr (sub_nonneg.2 hθ.2)).mul
      ((continuous_const.add continuous_id).rpow_const fun _ ↦ Or.inr hθ.1)).mul continuous_const
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)

/-- If `x` lies within `c t ^ β` and `y` within `c t' ^ β` of a point `z`, where `0 ≤ c`,
`0 ≤ β ≤ 1`, `0 ≤ t ≤ 2 h` and `0 ≤ t' ≤ h`, then `dist x y ≤ 3 c h ^ β`. -/
theorem dist_le_three_mul_rpow_of_le_two_mul {X : Type*} [PseudoMetricSpace X] {x y z : X}
    {c β h t t' : ℝ} (hc : 0 ≤ c) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hth : t ≤ 2 * h)
    (ht' : 0 ≤ t') (ht'h : t' ≤ h) (hx : dist x z ≤ c * t ^ β) (hy : dist y z ≤ c * t' ^ β) :
    dist x y ≤ 3 * c * h ^ β := by
  have h₁ : t ^ β ≤ 2 * h ^ β := Real.rpow_le_two_mul_rpow_of_le_two_mul ht hth hβ₀ hβ₁
  have h₂ : t' ^ β ≤ h ^ β := Real.rpow_le_rpow ht' ht'h hβ₀
  calc dist x y ≤ dist x z + dist y z := dist_triangle_right x y z
    _ ≤ c * (2 * h ^ β) + c * h ^ β :=
        add_le_add (hx.trans (mul_le_mul_of_nonneg_left h₁ hc))
          (hy.trans (mul_le_mul_of_nonneg_left h₂ hc))
    _ = 3 * c * h ^ β := by ring

end TauCeti

/-- For `p` in a product of seminormed groups and `x ∈ [0, 1]`,
`‖p.1‖ ^ (1 - x) * ‖p.2‖ ^ x ≤ ‖p‖`. -/
theorem Prod.norm_fst_rpow_mul_norm_snd_rpow_le {E F : Type*} [SeminormedAddGroup E]
    [SeminormedAddGroup F] (p : E × F) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖p.1‖ ^ (1 - x) * ‖p.2‖ ^ x ≤ ‖p‖ := by
  rw [Prod.norm_def]
  exact TauCeti.rpow_mul_rpow_le_max (norm_nonneg p.1) (norm_nonneg p.2) hx
