/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.Analysis.SpecialFunctions.Log.TwoAdd
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Power-law asymptotics

## Rescaling power-weighted limits

If `x ^ α * f x` tends to `C` at positive infinity, then `x ^ α * f (c * x)` tends to
`C / c ^ α` for `c > 0`, and a fixed translation of `f` preserves the constant `C`.
For a positive exponent, a finite power-law limit also implies that `f` tends to zero.
These facts transfer power-law tail constants between proportional or translated thresholds.

## Comparison with `exp ‖s‖ ^ b` at infinity

On a seminormed group, as `‖s‖ → ∞`:

* `exp (c * ‖s‖ ^ a)` is `O(exp ‖s‖ ^ b)` whenever `a < b`, for every real `c`;
* every power `‖s‖ ^ n` is `O(exp ‖s‖ ^ b)` whenever `0 < b`, and `o(exp (c ‖s‖))` whenever
  `0 < c`, so a polynomial weight turns `O(exp (-c ‖s‖))` decay into `O(exp (-a ‖s‖))` decay for
  every `a < c`;
* `‖s‖ ^ a` is `o(‖s‖ ^ b)` whenever `a < b`, as is `x ^ a` against `x ^ b` for real `x → ∞`,
  and `O(‖s‖ ^ b)` whenever `a ≤ b`; in particular `√‖s‖ = o(s)`, `‖s‖ ^ a` tends to `0` whenever
  `a < 0`, and `√x / (x ^ a) ^ k → 0` for real `x → ∞` whenever `1 / 2 < a k`.

These are the comparisons behind the order of growth of an entire function.

## Positive powers near zero

As `h → 0⁺`, a positive power `h ^ θ` tends to zero, so every function `f = O(h ^ θ)`, in
particular every multiple `A * h ^ θ`, falls below any positive constant. This is how polynomial
rates in a small scale `h` become inequalities for all small `h`. Power laws multiply: if
`f = O(h ^ a)` and `g = O(h ^ b)` as `h → 0⁺`, then `f * g = O(h ^ (a + b))`, and a bound
`f = O(h ^ a)` weakens to `f = O(h ^ c)` for every `c ≤ a`; at `+∞` it weakens to
`f = O(x ^ c)` for every `c ≥ a`. Likewise, near a point `w` of a normed group, a bound
`f = O(‖x - w‖ ^ a)` within a set avoiding `w` weakens to `f = O(‖x - w‖ ^ c)` for
every `c ≤ a`.

## Complex powers of a positive real variable

Along any filter eventually in `(0, ∞)`, the complex power `t ^ w` of the real variable `t` is
`O(t ^ Re w)`, so a bound by `t ^ w` is a bound by the real power `t ^ Re w`
(`Asymptotics.IsBigO.trans_ofReal_cpow_rpow`). For natural `n ≠ 0`,
`‖ρ ^ n * n ^ α‖ = ‖ρ‖ ^ n * n ^ Re α` and
`‖ρ ^ n * n ^ α * n⁻ᴹ‖ = ‖ρ‖ ^ n * n ^ (Re α - M)`. As `n → ∞`, `ρ ^ n * n ^ α = o(r ^ n)` whenever
`‖ρ‖ < r`, and `‖ρ‖ ^ n * n ^ β = o(ρ ^ n * n ^ α)` whenever `β < Re α`.

## Families bounded by integer powers

A family whose norms are bounded by `r ^ g a`, with `1 < r` and integer exponents `g a → -∞`,
tends to zero. This is how valuation bounds on coefficients give convergence of series.

## Rounded logarithmic orders

For every real `B` and every `s > 0`, the rounded-up orders `⌈B * log x⌉₊` are `o(x ^ s)`, and so
are the shifted orders `⌈B * log (x + c)⌉₊` for every real `c`. This is how orders of logarithmic
size are chosen in the moment method for the largest eigenvalue of a random matrix.

## Powers of a fixed base tending to one

For `q > 1` and a nonzero real base `b`, the powers `b ^ (a / q ^ n)` tend to one.
For `B ≠ 0`, the power `B ^ q⁻¹` tends to `1` as the real number `q` tends to `∞`.

## Comparing exponents

If `(n + 1) ^ a ≤ C (n + 1) ^ b` for every natural number `n`, then `a ≤ b`: a power with a
larger exponent outgrows every constant multiple of a smaller one. Symmetrically, if
`t ^ a ≤ C t ^ b` for every `t ∈ (0, T]`, `T > 0`, then `b ≤ a`: near zero a power with a smaller
exponent dominates every constant multiple of a larger one.

## Logarithmic comparisons

At positive infinity, `(1 + r) log (2 + r)` is `o(r ^ p)` for every `p > 1`, and any negative real
power `x ^ r` (`r < 0`) is `o((log x)⁻¹)`.

## Powers outgrowing geometric sequences

For every real `C` and every natural number `r ≥ 4 C ^ 2`, `C ^ r r ^ ((1 - r) / 2) < 1`: the
power `r ^ (r / 2)` outgrows every geometric sequence. This is the final contradiction of Gelfond's
proof of the Gelfond–Schneider theorem.

## Exponential limits of rescaled powers

For all reals `a` and `b`, `(1 + a / x) ^ (b * x)` converges to `Real.exp (a * b)` as the real
number `x` tends to infinity (`Real.tendsto_one_add_div_rpow_mul_exp`).
-/

public section

open Filter Real
open scoped Topology

/-- Rescaling the argument by a positive constant divides a power-weighted limit by the
corresponding power of that constant. The exponent may be any real number. -/
theorem Filter.Tendsto.rpow_mul_comp_const_mul {f : ℝ → ℝ} {α C c : ℝ}
    (hf : Tendsto (fun x : ℝ ↦ x ^ α * f x) atTop (𝓝 C)) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ x ^ α * f (c * x)) atTop (𝓝 (C / c ^ α)) := by
  have ht := hf.comp (tendsto_id.const_mul_atTop hc)
  apply (ht.div_const (c ^ α)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply, id_eq]
  rw [mul_rpow hc.le hx]
  field_simp [(rpow_pos_of_pos hc α).ne']

/-- A real function with a finite power-law limit of positive exponent tends to zero. -/
theorem Filter.Tendsto.tendsto_zero_of_rpow_mul {f : ℝ → ℝ} {α C : ℝ}
    (h : Tendsto (fun x : ℝ ↦ x ^ α * f x) atTop (𝓝 C)) (hα : 0 < α) :
    Tendsto f atTop (𝓝 0) := by
  have hlim := h.mul (tendsto_rpow_neg_atTop hα)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp [(Real.rpow_pos_of_pos hx α).ne']

/-- A fixed translation of a real function preserves its finite power-law constant at infinity,
for any real exponent. -/
theorem Filter.Tendsto.rpow_mul_comp_add {f : ℝ → ℝ} {α C : ℝ}
    (h : Tendsto (fun x : ℝ ↦ x ^ α * f x) atTop (𝓝 C)) (c : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ α * f (x + c)) atTop (𝓝 C) := by
  have hshift : Tendsto (fun x : ℝ ↦ x + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have hratio : Tendsto (fun x : ℝ ↦ x / (x + c)) atTop (𝓝 1) := by
    simpa using TauCeti.tendsto_add_div_add_atTop (0 : ℝ) c
  have hlim := (hratio.rpow_const (p := α) (Or.inl one_ne_zero)).mul (h.comp hshift)
  simp only [Real.one_rpow, one_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-c)] with x hx hxc
  have hx' : 0 < x + c := by linarith
  simp only [Function.comp_apply]
  rw [Real.div_rpow hx.le hx'.le]
  field_simp [(Real.rpow_pos_of_pos hx' α).ne']

open Asymptotics Bornology

namespace TauCeti

/-- A positive power of `h` tends to zero as `h → 0⁺`. -/
theorem tendsto_rpow_nhdsGT_zero {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun h : ℝ ↦ h ^ θ) (𝓝[>] 0) (𝓝 0) := by
  have ht := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto
  rw [Real.zero_rpow hθ.ne'] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- A function bounded by a positive power of `h` is eventually below every positive bound as
`h → 0⁺`. -/
theorem eventually_lt_of_isBigO_rpow {f : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hf : f =O[𝓝[>] 0] fun h ↦ h ^ θ) {c : ℝ} (hc : 0 < c) : ∀ᶠ h in 𝓝[>] 0, f h < c :=
  (hf.trans_tendsto (tendsto_rpow_nhdsGT_zero hθ)).eventually (gt_mem_nhds hc)

/-- Near `0⁺`, a positive power of `h` with any coefficient is below any positive constant. -/
theorem eventually_mul_rpow_lt_nhdsGT_zero {θ : ℝ} (hθ : 0 < θ) (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), A * h ^ θ < c :=
  eventually_lt_of_isBigO_rpow hθ (isBigO_const_mul_self A _ _) hc

/-- Along a filter eventually in `(0, ∞)`, the complex power `t ^ w` is `O(t ^ Re w)`. -/
theorem isBigO_ofReal_cpow_rpow {l : Filter ℝ} (hl : ∀ᶠ t in l, 0 < t) (w : ℂ) :
    (fun t : ℝ ↦ (t : ℂ) ^ w) =O[l] fun t ↦ t ^ w.re :=
  IsBigO.of_bound 1 <| hl.mono fun t ht ↦ by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
      one_mul]

/-- The norm of `ρ ^ n * n ^ α` is `‖ρ‖ ^ n * n ^ Re α` for `n ≠ 0`. -/
theorem norm_pow_mul_cpow (ρ α : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖ρ ^ n * (n : ℂ) ^ α‖ = ‖ρ‖ ^ n * (n : ℝ) ^ α.re := by
  rw [norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]

/-- The norm of `ρ ^ n * n ^ α * n⁻ᴹ` is `‖ρ‖ ^ n * n ^ (Re α - M)` for `n ≠ 0`. -/
theorem norm_pow_mul_cpow_mul_inv_pow (ρ α : ℂ) (M : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ‖ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ M‖ = ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - M) := by
  have hn' : (0 : ℝ) < n := by positivity
  simp [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Real.rpow_sub hn',
    Real.rpow_natCast, div_eq_mul_inv, mul_assoc]

/-- The comparison `ρⁿ n^α = o(rⁿ)` for `‖ρ‖ < r`. -/
theorem isLittleO_pow_mul_cpow_pow_of_norm_lt {ρ : ℂ} (α : ℂ) {r : ℝ} (h : ‖ρ‖ < r) :
    (fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) =o[atTop] fun n ↦ r ^ n := by
  have hlo := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) ⌈α.re⌉₊
    (show ‖‖ρ‖‖ < r by rwa [norm_norm])
  refine IsBigO.trans_isLittleO ?_ hlo
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [norm_pow_mul_cpow ρ α (by omega), one_mul, Real.norm_of_nonneg (by positivity),
    mul_comm ((n : ℝ) ^ _)]
  exact mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hn' (Nat.le_ceil _)).trans_eq
    (Real.rpow_natCast _ _)) (by positivity)

variable {E : Type*} [SeminormedAddCommGroup E]

/-- For `a < b` and any real `c`, `exp (c * ‖s‖ ^ a)` is `O(exp ‖s‖ ^ b)` as `‖s‖ → ∞`. -/
theorem isBigO_exp_mul_norm_rpow (c : ℝ) {a b : ℝ} (hab : a < b) :
    (fun s : E ↦ Real.exp (c * ‖s‖ ^ a)) =O[cobounded E] fun s ↦ Real.exp (‖s‖ ^ b) := by
  have h : ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
    filter_upwards [(tendsto_rpow_atTop (sub_pos.2 hab)).eventually_ge_atTop c,
      eventually_gt_atTop 0] with x hx hx0
    calc c * x ^ a ≤ x ^ (b - a) * x ^ a :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)
      _ = x ^ b := by rw [← Real.rpow_add hx0, sub_add_cancel]
  refine Real.isBigO_exp_comp_exp_comp.2 (isBoundedUnder_of_eventually_le (a := 0) ?_)
  filter_upwards [tendsto_norm_cobounded_atTop.eventually h] with s hs
  simpa using hs

/-- For `b > 0`, every power `‖s‖ ^ n` is `O(exp ‖s‖ ^ b)` as `‖s‖ → ∞`. -/
theorem isBigO_norm_pow_exp_norm_rpow (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun s : E ↦ ‖s‖ ^ n) =O[cobounded E] fun s ↦ Real.exp (‖s‖ ^ b) := by
  have h : (fun x : ℝ ↦ x ^ n) =O[atTop] fun x ↦ Real.exp (x ^ b) := by
    refine ((isLittleO_rpow_exp_atTop (n / b)).comp_tendsto
      (tendsto_rpow_atTop hb)).isBigO.congr' ?_ .rfl
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Function.comp_apply, ← Real.rpow_mul hx, mul_div_cancel₀ _ hb.ne', Real.rpow_natCast]
  exact h.comp_tendsto tendsto_norm_cobounded_atTop

/-- For `c > 0`, every power `‖s‖ ^ n` is `o(exp (c ‖s‖))` as `‖s‖ → ∞`. -/
theorem isLittleO_norm_pow_exp_mul_norm (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (fun s : E ↦ ‖s‖ ^ n) =o[cobounded E] fun s ↦ Real.exp (c * ‖s‖) :=
  (isLittleO_pow_exp_pos_mul_atTop n hc).comp_tendsto tendsto_norm_cobounded_atTop

/-- A polynomial weight costs an arbitrarily small part of an exponential decay rate: if `f` is
`O(exp (-c ‖s‖))` and `a < c`, then `‖s‖ ^ n • f s` is `O(exp (-a ‖s‖))` as `‖s‖ → ∞`. -/
theorem isBigO_norm_pow_smul_of_isBigO_exp_neg_mul_norm {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) {a c : ℝ} (hac : a < c) {f : E → F}
    (hf : f =O[cobounded E] fun s ↦ Real.exp (-(c * ‖s‖))) :
    (fun s ↦ ‖s‖ ^ n • f s) =O[cobounded E] fun s ↦ Real.exp (-(a * ‖s‖)) := by
  refine ((isLittleO_norm_pow_exp_mul_norm n (sub_pos.2 hac)).isBigO.smul hf).congr_right
    fun s ↦ ?_
  rw [smul_eq_mul, ← Real.exp_add]
  ring_nf

/-- For `a < b`, the real power `x ^ a` is `o(x ^ b)` as `x → ∞`. -/
theorem isLittleO_rpow_rpow_atTop {a b : ℝ} (hab : a < b) :
    (fun x : ℝ ↦ x ^ a) =o[atTop] fun x ↦ x ^ b := by
  refine (isLittleO_iff_tendsto' ?_).mpr ((tendsto_rpow_neg_atTop (sub_pos.2 hab)).congr' ?_)
  · filter_upwards [eventually_gt_atTop 0] with x hx h
    exact absurd h (Real.rpow_pos_of_pos hx b).ne'
  · filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_sub hx, neg_sub]

/-- The comparison `‖ρ‖ⁿ n^β = o(ρⁿ n^α)` for `β < Re α`. -/
theorem isLittleO_norm_pow_mul_rpow_pow_mul_cpow (ρ : ℂ) {α : ℂ} {β : ℝ} (h : β < α.re) :
    (fun n : ℕ ↦ ‖ρ‖ ^ n * (n : ℝ) ^ β) =o[atTop] fun n ↦ ρ ^ n * (n : ℂ) ^ α := by
  have hβ : (fun n : ℕ ↦ (n : ℝ) ^ β) =o[atTop] fun n ↦ (n : ℝ) ^ α.re :=
    (isLittleO_rpow_rpow_atTop h).comp_tendsto tendsto_natCast_atTop_atTop
  refine ((isBigO_refl (fun n : ℕ ↦ ‖ρ‖ ^ n) atTop).mul_isLittleO hβ).trans_isBigO
    (isBigO_norm_right.1 (isBigO_refl _ _ |>.congr' .rfl ?_))
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [norm_pow_mul_cpow ρ α hn]

/-- For `1 / 2 < a * k`, the square root is negligible against the `k`-th power of `x ^ a`:
`√x / (x ^ a) ^ k → 0` as `x → ∞`. -/
theorem tendsto_sqrt_div_rpow_pow_atTop_nhds_zero {a : ℝ} {k : ℕ} (h : 1 / 2 < a * k) :
    Tendsto (fun x : ℝ ↦ √x / (x ^ a) ^ k) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (sub_pos.2 h)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx.le, ← Real.rpow_sub hx, neg_sub]

/-- For `a < b`, `‖s‖ ^ a` is `o(‖s‖ ^ b)` as `‖s‖ → ∞`. -/
theorem isLittleO_norm_rpow_norm_rpow_cobounded {a b : ℝ} (hab : a < b) :
    (fun s : E ↦ ‖s‖ ^ a) =o[cobounded E] fun s ↦ ‖s‖ ^ b :=
  (isLittleO_rpow_rpow_atTop hab).comp_tendsto tendsto_norm_cobounded_atTop

/-- For `a ≤ b`, `‖s‖ ^ a` is `O(‖s‖ ^ b)` as `‖s‖ → ∞`. -/
theorem isBigO_norm_rpow_norm_rpow_cobounded {a b : ℝ} (hab : a ≤ b) :
    (fun s : E ↦ ‖s‖ ^ a) =O[cobounded E] fun s ↦ ‖s‖ ^ b := by
  rcases hab.lt_or_eq with hab | rfl
  · exact (isLittleO_norm_rpow_norm_rpow_cobounded hab).isBigO
  · exact isBigO_refl _ _

/-- For `a < 0`, `‖s‖ ^ a` tends to `0` as `‖s‖ → ∞`. -/
theorem tendsto_norm_rpow_cobounded {a : ℝ} (ha : a < 0) :
    Tendsto (fun s : E ↦ ‖s‖ ^ a) (cobounded E) (𝓝 0) :=
  (Asymptotics.isLittleO_one_iff ℝ).1
    ((isLittleO_norm_rpow_norm_rpow_cobounded ha).congr_right fun _ ↦ Real.rpow_zero _)

/-- `√‖s‖` is `o(s)` as `‖s‖ → ∞`. -/
theorem isLittleO_sqrt_norm_id_cobounded : (fun s : E ↦ √‖s‖) =o[cobounded E] fun s ↦ s := by
  refine isLittleO_norm_right.mp ?_
  refine (isLittleO_norm_rpow_norm_rpow_cobounded (E := E) (show (1 / 2 : ℝ) < 1 by norm_num)).congr
    (fun s ↦ (Real.sqrt_eq_rpow _).symm) fun s ↦ Real.rpow_one _

/-- A family whose norms are bounded by `r ^ g a`, with `1 < r` and integer exponents `g a`
tending to `-∞`, tends to zero. -/
theorem tendsto_zero_of_norm_le_zpow {α F : Type*} [SeminormedAddGroup F] {l : Filter α}
    {f : α → F} {r : ℝ} (hr : 1 < r) {g : α → ℤ} (hf : ∀ a, ‖f a‖ ≤ r ^ g a)
    (hg : Tendsto g l atBot) : Tendsto f l (𝓝 0) := by
  refine squeeze_zero_norm hf ?_
  have h := (tendsto_rpow_atBot_of_base_gt_one r hr).comp
    ((tendsto_intCast_atBot_iff (R := ℝ)).2 hg)
  simpa [Function.comp_def, Real.rpow_intCast] using h

/-- For `q > 1`, the powers `b ^ (a / q ^ n)` of a fixed nonzero base `b` tend to one. -/
theorem tendsto_const_rpow_div_pow_atTop {b q : ℝ} (hb : b ≠ 0) (hq : 1 < q) (a : ℝ) :
    Tendsto (fun n : ℕ ↦ b ^ (a / q ^ n)) atTop (𝓝 1) := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt hq).const_div_atTop a
  simpa only [Function.comp_def, Real.rpow_zero] using
    (Real.continuousAt_const_rpow hb (b := 0)).tendsto.comp h

/-- If `(n + 1) ^ a ≤ C (n + 1) ^ b` for every natural number `n`, then `a ≤ b`. -/
theorem le_of_forall_rpow_le_mul_rpow {a b C : ℝ}
    (h : ∀ n : ℕ, ((n : ℝ) + 1) ^ a ≤ C * ((n : ℝ) + 1) ^ b) : a ≤ b := by
  by_contra hab
  push Not at hab
  have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hab)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop C).exists
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have := h n
  rw [Real.rpow_sub hpos, lt_div_iff₀ (Real.rpow_pos_of_pos hpos _)] at hn
  linarith

/-- If `t ^ a ≤ C t ^ b` for every `t ∈ (0, T]`, with `T > 0`, then `b ≤ a`. -/
theorem le_of_forall_mem_Ioc_rpow_le_mul_rpow {a b C T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Ioc 0 T, t ^ a ≤ C * t ^ b) : b ≤ a := by
  by_contra hab
  push Not at hab
  obtain ⟨t, hCt, ht⟩ := ((eventually_mul_rpow_lt_nhdsGT_zero (sub_pos.2 hab) C one_pos).and
    (Ioo_mem_nhdsGT hT)).exists
  have hsplit : C * t ^ b = C * t ^ (b - a) * t ^ a := by
    rw [mul_assoc, ← Real.rpow_add ht.1, sub_add_cancel]
  have hle := h t ⟨ht.1, ht.2.le⟩
  rw [hsplit] at hle
  nlinarith [Real.rpow_pos_of_pos ht.1 a]

end TauCeti

namespace Asymptotics

/-- Power laws multiply near `0⁺`: if `f = O(h ^ a)` and `g = O(h ^ b)` as `h → 0⁺`, then
`f * g = O(h ^ c)` for every `c ≤ a + b`. This is the counterpart near zero of
`Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow`. -/
theorem IsBigO.mul_nhdsGT_zero_rpow_of_isBigO_rpow {R : Type*} [SeminormedRing R] {f g : ℝ → R}
    {a b c : ℝ} (hf : f =O[𝓝[>] 0] fun h ↦ h ^ a) (hg : g =O[𝓝[>] 0] fun h ↦ h ^ b)
    (h : c ≤ a + b) : (f * g) =O[𝓝[>] 0] fun h ↦ h ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
  rw [← Real.rpow_add ht.1, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le (a + b))]
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le h

/-- Power laws weaken near `0⁺`: if `f = O(h ^ a)` as `h → 0⁺`, then `f = O(h ^ c)` for every
`c ≤ a`. -/
theorem IsBigO.nhdsGT_zero_rpow_of_le {R : Type*} [Norm R] {f : ℝ → R} {a c : ℝ}
    (hf : f =O[𝓝[>] 0] fun h ↦ h ^ a) (h : c ≤ a) : f =O[𝓝[>] 0] fun h ↦ h ^ c := by
  refine hf.trans (Eventually.isBigO ?_)
  filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le a)]
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le h

/-- Power laws weaken at `+∞`: if `f = O(x ^ a)` as `x → ∞`, then `f = O(x ^ c)` for every
`a ≤ c`. -/
theorem IsBigO.atTop_rpow_of_le {R : Type*} [Norm R] {f : ℝ → R} {a c : ℝ}
    (hf : f =O[atTop] fun x ↦ x ^ a) (h : a ≤ c) : f =O[atTop] fun x ↦ x ^ c := by
  refine hf.trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) a)]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- Along a filter eventually in `(0, ∞)`, a bound `f = O(t ^ w)` by a complex power of the real
variable is a bound `f = O(t ^ a)` by the real power with exponent `a = Re w`. -/
theorem IsBigO.trans_ofReal_cpow_rpow {R : Type*} [Norm R] {f : ℝ → R} {l : Filter ℝ} {w : ℂ}
    {a : ℝ} (hf : f =O[l] fun t ↦ (t : ℂ) ^ w) (hl : ∀ᶠ t in l, 0 < t) (ha : w.re = a) :
    f =O[l] fun t ↦ t ^ a :=
  ha ▸ hf.trans (TauCeti.isBigO_ofReal_cpow_rpow hl w)

/-- Power laws in the distance weaken near a point: if `f = O(‖x - w‖ ^ a)` as `x → w` within a
set `s` that does not contain `w`, then `f = O(‖x - w‖ ^ c)` there for every `c ≤ a`. -/
theorem IsBigO.nhdsWithin_norm_sub_rpow_of_le {E R : Type*} [NormedAddCommGroup E] [Norm R]
    {f : E → R} {s : Set E} {w : E} {a c : ℝ} (hf : f =O[𝓝[s] w] fun x ↦ ‖x - w‖ ^ a)
    (hw : w ∉ s) (h : c ≤ a) : f =O[𝓝[s] w] fun x ↦ ‖x - w‖ ^ c := by
  refine hf.trans (Eventually.isBigO ?_)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds w one_pos)]
    with x hxs hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) a)]
  exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.2 (sub_ne_zero.2 fun hxw ↦ hw (hxw ▸ hxs)))
    (mem_ball_iff_norm.1 hx).le h

end Asymptotics

namespace Real

/-- The Mellin growth scale `(1+r) log (2+r)` is negligible compared with every power above one. -/
theorem isLittleO_add_one_mul_log_add_two_rpow {p : ℝ} (hp : 1 < p) :
    (fun r : ℝ ↦ (1 + r) * log (2 + r)) =o[atTop] fun r ↦ r ^ p := by
  have hlin : (fun r : ℝ ↦ 1 + r) =O[atTop] fun r ↦ r := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  have hlog : (fun r : ℝ ↦ log (2 + r)) =O[atTop] log := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg (by linarith)),
      abs_of_nonneg (log_nonneg (by linarith))]
    calc
      log (2 + r) ≤ log (r * r) := log_le_log (by linarith) (by nlinarith)
      _ = 2 * log r := by rw [log_mul (by linarith) (by linarith)]; ring
  refine (hlin.mul_isLittleO (hlog.trans_isLittleO
    (isLittleO_log_rpow_atTop (sub_pos.mpr hp)))).congr' .rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    r * r ^ (p - 1) = r ^ (1 + (p - 1)) := by rw [rpow_add hr, rpow_one]
    _ = r ^ p := by congr 1; ring
/-- The logarithmic growth scale is stable under nonnegative affine majorants. -/
theorem add_one_mul_log_add_two_le {r t A : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (htA : t ≤ A * (1 + r)) :
    (1 + t) * log (2 + t) ≤ (A + 2) * (2 * (A + 2) + 1) * (1 + r) * log (2 + r) := by
  let M := A + 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hL := one_half_le_log_two_add hr
  have h1 : 1 + t ≤ M * (1 + r) := by dsimp [M]; nlinarith
  have h2 : 2 + t ≤ M * (2 + r) := by dsimp [M]; nlinarith
  have hlog : log (2 + t) ≤ log M + log (2 + r) := by
    rw [← log_mul hM.ne' (by positivity : 2 + r ≠ 0)]
    exact log_le_log (by positivity) h2
  have hlogM : log M ≤ M := (log_le_sub_one_of_pos hM).trans (by linarith)
  have hlog' : log (2 + t) ≤ (2 * M + 1) * log (2 + r) := by
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * M)]
  calc
    _ ≤ (M * (1 + r)) * ((2 * M + 1) * log (2 + r)) :=
      mul_le_mul h1 hlog' (log_nonneg (by linarith)) (by positivity)
    _ = _ := by dsimp [M]; ring

/-- Any negative real power `x ^ r` (`r < 0`) is negligible compared with `(log x)⁻¹` as
`x → ∞`. -/
theorem isLittleO_rpow_inv_log_atTop {r : ℝ} (hr : r < 0) :
    (fun x : ℝ ↦ x ^ r) =o[atTop] fun x ↦ (log x)⁻¹ := by
  refine ((isLittleO_log_rpow_atTop (neg_pos.mpr hr)).inv_rev ?_).congr' ?_ .rfl
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx h
    exact absurd h (log_pos hx).ne'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← rpow_neg hx, neg_neg]

/-- For every real `C` and every natural number `r ≥ 4 C ^ 2`, `C ^ r r ^ ((1 - r) / 2) < 1`. -/
theorem pow_mul_rpow_lt_one_of_four_mul_sq_le (C : ℝ) {r : ℕ} (hCr : 4 * C ^ 2 ≤ r) :
    C ^ r * (r : ℝ) ^ ((1 - (r : ℝ)) / 2) < 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · norm_num
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr₀ : (0 : ℝ) < r := zero_lt_one.trans_le hr₁
  set s := √(r : ℝ)
  have hs₀ : 0 < s := sqrt_pos.2 hr₀
  have hsr : s ≤ r := sqrt_le_self_iff.2 (Or.inr hr₁)
  -- `2 |C| ≤ s`, since `(2 |C|) ^ 2 = 4 C ^ 2 ≤ r`.
  have hCs : 2 * |C| ≤ s := le_sqrt_of_sq_le (by rw [mul_pow, sq_abs]; linarith)
  -- `r ^ ((1 - r) / 2) = s ^ (1 - r) = s / s ^ r`.
  have hrs : (r : ℝ) ^ ((1 - (r : ℝ)) / 2) = s / s ^ r := by
    rw [rpow_div_two_eq_sqrt _ hr₀.le, rpow_sub hs₀]
    simp
  have hCs' : |C| / s ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hs₀ two_pos]
    linarith
  calc C ^ r * (r : ℝ) ^ ((1 - (r : ℝ)) / 2) ≤ |C| ^ r * (r : ℝ) ^ ((1 - (r : ℝ)) / 2) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (abs_pow C r)) (by positivity)
    _ = s * (|C| / s) ^ r := by
        rw [hrs, div_pow]
        field_simp
    _ ≤ s * (1 / 2) ^ r := by gcongr
    _ = s / 2 ^ r := by rw [one_div_pow, mul_one_div]
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        exact hsr.trans_lt (by exact_mod_cast Nat.lt_two_pow_self)

/-- Rounded-up logarithmic orders are negligible against every positive power: for every real `B`
and every `s > 0`, `⌈B * log x⌉₊ / x ^ s` tends to zero as `x → ∞`. -/
theorem tendsto_natCeil_mul_log_div_rpow_atTop_nhds_zero (B : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ (⌈B * log x⌉₊ : ℝ) / x ^ s) atTop (𝓝 0) := by
  have hlim := (((isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero).const_mul |B|).add
    (tendsto_rpow_atTop hs).inv_tendsto_atTop
  rw [mul_zero, zero_add] at hlim
  -- For `x ≥ 1`, `0 ≤ ⌈B * log x⌉₊ ≤ |B| * log x + 1`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_ <;>
    filter_upwards [eventually_ge_atTop 1] with x hx
  · exact div_nonneg (Nat.cast_nonneg _) (rpow_nonneg (zero_le_one.trans hx) _)
  have hlog : 0 ≤ log x := log_nonneg hx
  have hceil : (⌈B * log x⌉₊ : ℝ) ≤ |B| * log x + 1 :=
    (Nat.cast_le.mpr (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self B) hlog))).trans
      (Nat.ceil_lt_add_one (by positivity)).le
  calc (⌈B * log x⌉₊ : ℝ) / x ^ s ≤ (|B| * log x + 1) / x ^ s :=
        div_le_div_of_nonneg_right hceil (rpow_nonneg (zero_le_one.trans hx) _)
    _ = |B| * (log x / x ^ s) + (x ^ s)⁻¹ := by ring

/-- Shifting the logarithm keeps rounded-up logarithmic orders negligible against every positive
power: for all reals `B` and `c` and every `s > 0`, `⌈B * log (x + c)⌉₊ / x ^ s` tends to zero as
`x → ∞`. -/
theorem tendsto_natCeil_mul_log_add_div_rpow_atTop_nhds_zero (B c : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ (⌈B * log (x + c)⌉₊ : ℝ) / x ^ s) atTop (𝓝 0) := by
  -- Compare with `⌈B * log (x + c)⌉₊ / (x + c) ^ s`, as `((x + c) / x) ^ s` tends to `1`.
  have hratio := (TauCeti.tendsto_add_div_add_atTop c 0).rpow_const (p := s) (Or.inr hs.le)
  have hlim := ((tendsto_natCeil_mul_log_div_rpow_atTop_nhds_zero B hs).comp
    (tendsto_atTop_add_const_right atTop c tendsto_id)).mul hratio
  rw [one_rpow, zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-c)] with x hx hxc
  have hx' : 0 < x + c := by linarith
  simp only [Function.comp_apply, id, add_zero]
  rw [div_rpow hx'.le hx.le]
  field_simp [(rpow_pos_of_pos hx' s).ne']

/-- For `B ≠ 0`, the power `B ^ q⁻¹` tends to `1` as the real number `q` tends to `∞`. -/
theorem tendsto_const_rpow_inv_atTop {B : ℝ} (hB : B ≠ 0) :
    Tendsto (fun q : ℝ => B ^ q⁻¹) atTop (𝓝 1) := by
  simpa only [Function.comp_def, rpow_zero] using
    (continuousAt_const_rpow hB).tendsto.comp tendsto_inv_atTop_zero

/-- For any real numbers `a` and `b`, `(1 + a / x) ^ (b * x)` converges to `exp (a * b)` as the
real number `x` tends to infinity. -/
theorem tendsto_one_add_div_rpow_mul_exp (a b : ℝ) :
    Tendsto (fun x : ℝ ↦ (1 + a / x) ^ (b * x)) atTop (𝓝 (exp (a * b))) := by
  have h1 : Tendsto (fun x : ℝ ↦ ((1 + a / x) ^ x) ^ b) atTop (𝓝 (exp a ^ b)) :=
    (tendsto_one_add_div_rpow_exp a).rpow_const (Or.inl (exp_pos _).ne')
  rw [← exp_mul] at h1
  have hpos : ∀ᶠ x : ℝ in atTop, 0 ≤ 1 + a / x := by
    have h0 : Tendsto (fun x : ℝ ↦ 1 + a / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_id (α := ℝ)))
    exact (h0.eventually (lt_mem_nhds zero_lt_one)).mono fun _ h ↦ h.le
  refine h1.congr' ?_
  filter_upwards [hpos] with x hbase
  rw [← rpow_mul hbase, mul_comm x b]

end Real
