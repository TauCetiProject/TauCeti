/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp

/-!
# Square-root estimates, derivatives and limits at zero

This file records a weighted form `|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)` of the
`1/2`-Hölder bound for the square root, the derivatives of `x ↦ √(x² + p)`, of
`x ↦ β x + √(x² + p)` and of related substitutions, that `c √u` tends to `0` as `u → 0`, and
through positive values as `u → 0⁺` when `c > 0`, and that the radial profile
`t ↦ ψ (√t) / (√t) ^ n` of a `C^k` function supported in `(0, ∞)` is `C^k`. The elementary
square-root bounds and identities that need no `rpow`, calculus or limits are in
`TauCeti.Analysis.Real.Sqrt`.

## Main results

* `Real.abs_sqrt_sub_sqrt_mul_max_rpow_le`: for `0 ≤ γ ≤ 1`, the weighted bound
  `|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)`.
* `Real.tendsto_mul_sqrt_nhds_zero`: `c √u → 0` as `u → 0`.
* `Real.tendsto_mul_sqrt_nhdsGT_zero`, `Real.tendsto_sqrt_nhdsGT_zero`: for `c > 0`,
  `c √u → 0⁺` as `u → 0⁺`.
* `Real.hasDerivAt_sqrt_sq_add`, `Real.hasDerivAt_mul_add_sqrt_sq_add`: the derivatives of
  `x ↦ √(x² + p)` and `x ↦ β x + √(x² + p)` wherever `t² + p ≠ 0`.
* `Real.hasDerivAt_add_sqrt_sq_add`: the substitution `t ↦ t + √(t² + p)` has an explicit
  derivative wherever `t² + p > 0`.
* `Real.hasDerivAt_div_mul_add_sqrt_sq_add`, `Real.tendsto_div_mul_add_sqrt_sq_add_atTop`: the
  function `y ↦ α / (β y + √(y² + c))` has an explicit derivative where `y² + c` and the
  denominator do not vanish and, for `β ≠ −1`, tends to `0` at `+∞`.
* `Real.contDiff_div_sqrt_pow`: if `ψ` is `C^k` with support in `(0, ∞)`, then
  `t ↦ ψ (√t) / (√t) ^ n` is `C^k`.

## References

`Real.hasDerivAt_add_sqrt_sq_add` is extracted from, and its proof adapted from, Jeremy Tan's
[Mathlib PR #34397](https://github.com/leanprover-community/mathlib4/pull/34397), commit
`376352b6e080265bc0380074baaf9aafa0b70a80`.

`Real.hasDerivAt_div_mul_add_sqrt_sq_add` and `Real.tendsto_div_mul_add_sqrt_sq_add_atTop` are
adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean`.
-/

public section

open Filter
open scoped Topology

namespace Real

/-- **A weighted Hölder bound for the square root.** For all reals `t` and `s` and `0 ≤ γ ≤ 1`,
`|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)`. At `γ = 0` this is the `1/2`-Hölder
bound `Real.abs_sqrt_sub_sqrt_le`. It is the time increment of a parabolic rescaling `x - √t y`
against a `γ`-Hölder modulus, as in the temporal Hölder estimate of heat potentials of `C^{1,γ}`
data. -/
theorem abs_sqrt_sub_sqrt_mul_max_rpow_le (t s : ℝ) {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    |√t - √s| * max √t √s ^ γ ≤ |t - s| ^ ((1 + γ) / 2) := by
  -- First the bound `|a - b| max a b ^ γ ≤ |a² - b²| ^ ((1 + γ) / 2)` for `a, b ≥ 0`.
  have key : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
      |a - b| * max a b ^ γ ≤ |a ^ 2 - b ^ 2| ^ ((1 + γ) / 2) := by
    intro a b ha hb
    wlog hab : b ≤ a generalizing a b
    · simpa [abs_sub_comm, max_comm] using this hb ha (le_of_not_ge hab)
    rcases (add_nonneg ha hb).eq_or_lt with hs | hs
    · obtain rfl : a = 0 := by linarith
      obtain rfl : b = 0 := by linarith
      simp only [sub_self, abs_zero, zero_mul]
      positivity
    have hd : 0 ≤ a - b := sub_nonneg.2 hab
    rw [abs_of_nonneg hd, max_eq_left hab, show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring,
      abs_of_nonneg (mul_nonneg hd hs.le), mul_rpow hd hs.le]
    -- Split `a - b = (a - b) ^ ((1 + γ) / 2) (a - b) ^ ((1 - γ) / 2)` and use `a - b ≤ a + b`.
    have he : (1 + γ) / 2 + (1 - γ) / 2 = 1 := by ring
    have h₁ : a - b ≤ (a - b) ^ ((1 + γ) / 2) * (a + b) ^ ((1 - γ) / 2) := by
      calc a - b = (a - b) ^ ((1 + γ) / 2) * (a - b) ^ ((1 - γ) / 2) := by
            rw [← rpow_add' hd (by rw [he]; exact one_ne_zero), he, rpow_one]
        _ ≤ _ := by gcongr; linarith
    have h₂ : a ^ γ ≤ (a + b) ^ γ := by gcongr; linarith
    calc (a - b) * a ^ γ
        ≤ (a - b) ^ ((1 + γ) / 2) * (a + b) ^ ((1 - γ) / 2) * (a + b) ^ γ := by gcongr
      _ = (a - b) ^ ((1 + γ) / 2) * (a + b) ^ ((1 + γ) / 2) := by
          rw [mul_assoc, ← rpow_add hs, show (1 - γ) / 2 + γ = (1 + γ) / 2 by ring]
  refine (key (sqrt_nonneg t) (sqrt_nonneg s)).trans
    (rpow_le_rpow (abs_nonneg _) ?_ (by positivity))
  rw [sq_sqrt', sq_sqrt']
  exact abs_max_sub_max_le_abs t s 0

/-- For every `c`, `c √u` tends to `0` as `u → 0`. -/
theorem tendsto_mul_sqrt_nhds_zero (c : ℝ) : Tendsto (fun u => c * √u) (𝓝 0) (𝓝 0) := by
  have h : Continuous fun u => c * √u := by fun_prop
  simpa using h.tendsto 0

/-- For `c > 0`, `c √u` tends to `0` through positive values as `u → 0⁺`. -/
theorem tendsto_mul_sqrt_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u => c * √u) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_mul_sqrt_nhds_zero c).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact mul_pos hc (sqrt_pos.2 hu)

/-- The square root tends to `0` through positive values as `u → 0⁺`. -/
theorem tendsto_sqrt_nhdsGT_zero : Tendsto (√·) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) := by
  simpa using tendsto_mul_sqrt_nhdsGT_zero one_pos

/-- The radial profile `t ↦ ψ (√t) / (√t) ^ n` of a `C^k` function `ψ` supported in `(0, ∞)` is
`C^k`. -/
lemma contDiff_div_sqrt_pow {k : WithTop ℕ∞} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ k ψ)
    (hψs : tsupport ψ ⊆ Set.Ioi 0) (n : ℕ) : ContDiff ℝ k fun t ↦ ψ (√t) / (√t) ^ n := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : √t ∈ tsupport ψ
  · have ht0 : 0 < t := sqrt_pos.mp (hψs ht)
    exact ((hψ.contDiffAt.comp t (contDiffAt_sqrt ht0.ne')).div
      ((contDiffAt_sqrt ht0.ne').pow _) (pow_ne_zero _ (sqrt_pos.mpr ht0).ne'))
  · have hev : ∀ᶠ s in 𝓝 t, ψ (√s) / (√s) ^ n = 0 := by
      have : ∀ᶠ s in 𝓝 t, √s ∉ tsupport ψ :=
        continuous_sqrt.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport ψ).isOpen_compl.mem_nhds ht)
      filter_upwards [this] with s hs
      simp [image_eq_zero_of_notMem_tsupport hs]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

/-- The derivative of `x ↦ √(x² + p)` at a point `t` where `t² + p ≠ 0`. Where `t² + p < 0`
the function vanishes near `t`, matching the junk value `t / √(t² + p) = 0`. -/
theorem hasDerivAt_sqrt_sq_add {p : ℝ} (t : ℝ) (h : t ^ 2 + p ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ √(x ^ 2 + p)) (t / √(t ^ 2 + p)) t :=
  (((hasDerivAt_pow 2 t).add_const p).sqrt h).congr_deriv
    (by norm_num [mul_div_mul_left _ _ (two_ne_zero' ℝ)])

/-- The derivative of `x ↦ β x + √(x² + p)` at a point `t` where `t² + p ≠ 0`. -/
theorem hasDerivAt_mul_add_sqrt_sq_add (β : ℝ) {p : ℝ} (t : ℝ) (h : t ^ 2 + p ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ β * x + √(x ^ 2 + p)) (β + t / √(t ^ 2 + p)) t :=
  (((hasDerivAt_id t).const_mul β).add (hasDerivAt_sqrt_sq_add t h)).congr_deriv (by simp)

/-- The derivative of `t ↦ t + √(t² + p)` at a point `t` where `0 < t² + p`. -/
theorem hasDerivAt_add_sqrt_sq_add {p : ℝ} (t : ℝ) (h : 0 < t ^ 2 + p) :
    HasDerivAt (fun t : ℝ ↦ t + √(t ^ 2 + p)) ((t + √(t ^ 2 + p)) / √(t ^ 2 + p)) t := by
  convert hasDerivAt_mul_add_sqrt_sq_add 1 t h.ne' using 1
  · simp only [one_mul]
  · rw [add_div, div_self (sqrt_pos.2 h).ne']
    ring

/-- The derivative of `y ↦ α / (β y + √(y² + c))` at a point where `y² + c` and the denominator
do not vanish. -/
theorem hasDerivAt_div_mul_add_sqrt_sq_add (α β c : ℝ) {y : ℝ} (hyc : y ^ 2 + c ≠ 0)
    (hy : β * y + √(y ^ 2 + c) ≠ 0) :
    HasDerivAt (fun y => α / (β * y + √(y ^ 2 + c)))
      (-α * (β + y / √(y ^ 2 + c)) / (β * y + √(y ^ 2 + c)) ^ 2) y := by
  have := (hasDerivAt_const y α).div (hasDerivAt_mul_add_sqrt_sq_add β y hyc) hy
  refine this.congr_deriv ?_
  ring

/-- For `β ≠ −1`, `α / (β y + √(y² + c))` tends to `0` as `y → +∞`. -/
theorem tendsto_div_mul_add_sqrt_sq_add_atTop (α : ℝ) {β : ℝ} (hβ : β ≠ -1) (c : ℝ) :
    Tendsto (fun y => α / (β * y + √(y ^ 2 + c))) atTop (𝓝 0) := by
  -- For `y > 0` the function is `(α / y) / (β + √(1 + c / y²))`.
  have hden : Tendsto (fun y : ℝ => β + √(1 + c / y ^ 2)) atTop (𝓝 (β + 1)) := by
    have : Tendsto (fun y : ℝ => 1 + c / y ^ 2) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero))
    simpa using tendsto_const_nhds.add this.sqrt
  have h := (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun y : ℝ => α / y) atTop (𝓝 0)).div
    hden fun h => hβ (by linarith)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hs : √(y ^ 2 + c) = y * √(1 + c / y ^ 2) := by
    rw [show y ^ 2 + c = y ^ 2 * (1 + c / y ^ 2) by field_simp, sqrt_mul (sq_nonneg y),
      sqrt_sq hy.le]
  simp only [Pi.div_apply, hs, div_div]
  ring

end Real

end
