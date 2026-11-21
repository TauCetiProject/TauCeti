/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp

import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Square-root displacement estimates and limits at zero

Two estimates comparing the real square-root and inverse-square-root functions
with the identity near `1`. These bounds control scalar spectral factors of
positive operators close to the identity. The file also records that the square root is
`1/2`-Hölder, `|√t - √s| ≤ √|t - s|`, that `1 ≤ √(1 + t²)`, and that
`|t / √(t² + p)| ≤ 1` for `p ≥ 0`. It also records that the
modular `√(1 + t²) - 1` is at most `|t|` and `t² / 2` and is locally Lipschitz, that `c √u` tends
to `0` as
`u → 0`, and through positive values as `u → 0⁺` when `c > 0`, and the cancellation
`|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹` used in changes of variables, and that the radial profile
`t ↦ ψ (√t) / (√t) ^ n` of a `C^k` function supported in `(0, ∞)` is `C^k`. Finally, it describes
the sets `{x | x² ≤ a}` and `{x | a ≤ x²}` as an interval and a union of two rays.

## Main results

* `Real.abs_sqrt_sub_one_le_abs_sub_one`: for every real `μ`,
  `|√μ - 1| ≤ |μ - 1|`.
* `Real.abs_one_sub_inv_sqrt_le`: if `|μ - 1| ≤ δ ≤ 1/2`,
  `|1 - (√μ)⁻¹| ≤ δ`.
* `Real.abs_sqrt_sub_sqrt_le`: for all reals `t` and `s`, `|√t - √s| ≤ √|t - s|`.
* `Real.one_le_sqrt_one_add_sq`: for every real `t`, `1 ≤ √(1 + t²)`.
* `Real.abs_div_sqrt_sq_add_le_one`: for `p ≥ 0` and every real `t`, `|t / √(t² + p)| ≤ 1`.
* `Real.sqrt_one_add_sq_sub_one_le_abs`: for every real `t`, `√(1 + t²) - 1 ≤ |t|`.
* `Real.sqrt_one_add_sq_sub_one_le_sq_div_two`: for every real `t`, `√(1 + t²) - 1 ≤ t² / 2`.
* `Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le`: for all reals `a` and `b`,
  `|√(1 + a²) - √(1 + b²)| ≤ |a - b| (|a| + |b|)`.
* `Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub`: `t ↦ √(1 + t²)` is `1`-Lipschitz.
* `Real.one_add_div_two_le_sqrt_one_add_sq`: for every real `t`, `(1 + t) / 2 ≤ √(1 + t²)`.
* `Real.le_sqrt_mul_of_sq_le_mul`: if `0 ≤ b` and `a² ≤ c b²` then `a ≤ √c * b`.
* `Real.abs_mul_inv_sqrt_sq_mul_mul`: for `d ≠ 0` and `0 ≤ c`,
  `|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`.
* `Real.inv_sqrt_two_sq_add_inv_sqrt_two_sq`: `((√2)⁻¹)² + ((√2)⁻¹)² = 1`.
* `Real.tendsto_mul_sqrt_nhds_zero`: `c √u → 0` as `u → 0`.
* `Real.tendsto_mul_sqrt_nhdsGT_zero`, `Real.tendsto_sqrt_nhdsGT_zero`: for `c > 0`,
  `c √u → 0⁺` as `u → 0⁺`.
* `Real.add_sqrt_sq_add_pos`, `Real.hasDerivAt_add_sqrt_sq_add`,
  `Real.image_add_sqrt_sq_add_eq_Ioi`: the substitution `t ↦ t + √(t² + p)`
  is positive, has an explicit derivative, and maps `ℝ` onto `(0, ∞)` for `p > 0`.
* `Real.hasDerivAt_div_mul_add_sqrt_sq_add`, `Real.tendsto_div_mul_add_sqrt_sq_add_atTop`: the
  function `y ↦ α / (β y + √(y² + c))` has an explicit derivative where `y² + c` and the
  denominator do not vanish and, for `β ≠ −1`, tends to `0` at `+∞`.
* `Real.strictMonoOn_mul_sqrt_sq_add_sub`: for `c > 0`, `y ↦ y (√(y² + c) − y)` is strictly
  increasing on `[0, ∞)`.
* `Real.contDiff_div_sqrt_pow`: if `ψ` is `C^k` with support in `(0, ∞)`, then
  `t ↦ ψ (√t) / (√t) ^ n` is `C^k`.
* `Real.tendsto_sqrt_mul_sqrt_add_one_sub_sqrt`: `√x (√(x + 1) - √x) → 1/2` as `x → ∞`.
* `Real.setOf_sq_le_eq_Icc`: for `0 ≤ a`, `{x | x² ≤ a} = [-√a, √a]`.
* `Real.setOf_le_sq_eq_union`: `{x | a ≤ x²} = (-∞, -√a] ∪ [√a, ∞)`.

## References

[AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
`ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`.

`Real.add_sqrt_sq_add_pos`, `Real.hasDerivAt_add_sqrt_sq_add` and
`Real.image_add_sqrt_sq_add_eq_Ioi` are extracted from, and their proofs adapted from, Jeremy
Tan's [Mathlib PR #34397](https://github.com/leanprover-community/mathlib4/pull/34397),
commit `376352b6e080265bc0380074baaf9aafa0b70a80`.

`Real.hasDerivAt_div_mul_add_sqrt_sq_add`, `Real.tendsto_div_mul_add_sqrt_sq_add_atTop` and
`Real.strictMonoOn_mul_sqrt_sq_add_sub` are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean`.
-/

public section

open Filter
open scoped Topology

namespace Real

/-- For every real `μ`, the square root is no farther from `1` than `μ` is:
`|√μ - 1| ≤ |μ - 1|`. -/
theorem abs_sqrt_sub_one_le_abs_sub_one {μ : ℝ} :
    |sqrt μ - 1| ≤ |μ - 1| := by
  rcases le_total 0 μ with hμ | hμ
  · have hs : 0 ≤ sqrt μ := sqrt_nonneg μ
    have hsq : sqrt μ * sqrt μ = μ := mul_self_sqrt hμ
    have key : |sqrt μ - 1| * (sqrt μ + 1) = |μ - 1| := by
      rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ sqrt μ + 1), ← abs_mul]
      congr 1
      nlinarith [hsq]
    nlinarith [key, mul_nonneg (abs_nonneg (sqrt μ - 1)) hs]
  · have hsqrt : sqrt μ = 0 := sqrt_eq_zero_of_nonpos hμ
    calc
      |sqrt μ - 1| = 1 := by rw [hsqrt]; norm_num
      _ ≤ |μ - 1| := by
        rw [abs_of_nonpos (by linarith : μ - 1 ≤ 0)]
        linarith

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The hypotheses force `μ` to be positive and keep the inverse square root
bounded near `1`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (sqrt μ)⁻¹| ≤ δ := by
  have hμlb : 1 - δ ≤ μ := by rw [abs_le] at hμ; linarith
  have hμpos : (0 : ℝ) < μ := by linarith
  set s := sqrt μ
  have hs0 : 0 < s := sqrt_pos.mpr hμpos
  have hssq : s ^ 2 = μ := sq_sqrt (le_of_lt hμpos)
  -- `s ≥ 1/2` (since `s² = μ ≥ 1/2`)
  have hssqlb : (1 : ℝ) / 2 ≤ s ^ 2 := by rw [hssq]; linarith
  have hsge : (1 : ℝ) / 2 ≤ s := by nlinarith [hs0, hssqlb]
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hμ
  rw [abs_le] at hμ ⊢
  obtain ⟨hμ1, hμ2⟩ := hμ
  have hssq' : s * s = μ := by nlinarith [hssq]
  -- Lower bound `1 ≤ (1 + δ) * s`: its square is `(1 + δ)² μ ≥ (1 + δ)² (1 - δ) ≥ 1`.
  have hlow : 1 ≤ (1 + δ) * s := by
    have hpos : 0 < (1 + δ) * s := by positivity
    nlinarith [hpos, hssq', hμ1, hμ2, hδ0, hsge, mul_nonneg hδ0 hδ0,
      mul_nonneg (mul_nonneg hδ0 hδ0) hδ0]
  -- Upper bound `(1 - δ) * s ≤ 1`: equivalently `(1 - δ)² μ ≤ 1` when `1 - δ ≥ 0`.
  have hhigh : (1 - δ) * s ≤ 1 := by
    rcases le_or_gt (1 - δ) 0 with h | h
    · nlinarith [hs0, h]
    · nlinarith [hssq', hμ1, hμ2, hδ0, hsge, h, mul_nonneg hδ0 hδ0]
  -- Translate the two multiplicative bounds into bounds on `s⁻¹`.
  have hinv_le : s⁻¹ ≤ 1 + δ := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]; linarith [hlow]
  have hle_inv : 1 - δ ≤ s⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hs0]; linarith [hhigh]
  exact ⟨by linarith [hinv_le], by linarith [hle_inv]⟩

/-- For all reals `t` and `s`, `√t ≤ √s + √|t - s|`. -/
theorem sqrt_le_sqrt_add_sqrt_abs_sub (t s : ℝ) : √t ≤ √s + √|t - s| := by
  rw [sqrt_le_left (by positivity)]
  have hts := sq_sqrt (abs_nonneg (t - s))
  rcases le_total 0 s with hs | hs
  · nlinarith [sq_sqrt hs, le_abs_self (t - s), mul_nonneg (sqrt_nonneg s) (sqrt_nonneg |t - s|)]
  · rw [sqrt_eq_zero_of_nonpos hs]
    nlinarith [le_abs_self (t - s)]

/-- **The square root is `1/2`-Hölder.** For all reals `t` and `s`, `|√t - √s| ≤ √|t - s|`. -/
theorem abs_sqrt_sub_sqrt_le (t s : ℝ) : |√t - √s| ≤ √|t - s| := by
  have h₁ := sqrt_le_sqrt_add_sqrt_abs_sub t s
  have h₂ := sqrt_le_sqrt_add_sqrt_abs_sub s t
  rw [abs_sub_comm s t] at h₂
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- For every real `t`, `1 ≤ √(1 + t²)`. -/
theorem one_le_sqrt_one_add_sq (t : ℝ) : 1 ≤ √(1 + t ^ 2) :=
  one_le_sqrt.mpr (by nlinarith [sq_nonneg t])

/-- For `p ≥ 0` and every real `t`, `|t / √(t² + p)| ≤ 1`, including when the
square root vanishes. -/
theorem abs_div_sqrt_sq_add_le_one {p : ℝ} (hp : 0 ≤ p) (t : ℝ) :
    |t / √(t ^ 2 + p)| ≤ 1 := by
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  exact div_le_one_of_le₀ (abs_le_sqrt (le_add_of_nonneg_right hp)) (sqrt_nonneg _)

/-- The modular `√(1 + t²) - 1` grows at most linearly: `√(1 + t²) - 1 ≤ |t|`. -/
theorem sqrt_one_add_sq_sub_one_le_abs (t : ℝ) : √(1 + t ^ 2) - 1 ≤ |t| := by
  rw [sub_le_iff_le_add', sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg t, sq_abs t]

/-- The modular `√(1 + t²) - 1` is at most quadratic: `√(1 + t²) - 1 ≤ t² / 2`. -/
theorem sqrt_one_add_sq_sub_one_le_sq_div_two (t : ℝ) : √(1 + t ^ 2) - 1 ≤ t ^ 2 / 2 := by
  rw [sub_le_iff_le_add', sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (t ^ 2)]

/-- The modular `√(1 + t²) - 1` is locally Lipschitz with a linear modulus:
`|√(1 + a²) - √(1 + b²)| ≤ |a - b| (|a| + |b|)`. -/
theorem abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le (a b : ℝ) :
    |√(1 + a ^ 2) - √(1 + b ^ 2)| ≤ |a - b| * (|a| + |b|) := by
  have ha := one_le_sqrt_one_add_sq a
  have hb := one_le_sqrt_one_add_sq b
  have hA : √(1 + a ^ 2) ^ 2 = 1 + a ^ 2 := sq_sqrt (by positivity)
  have hB : √(1 + b ^ 2) ^ 2 = 1 + b ^ 2 := sq_sqrt (by positivity)
  have key : (√(1 + a ^ 2) - √(1 + b ^ 2)) * (√(1 + a ^ 2) + √(1 + b ^ 2)) =
      (a - b) * (a + b) := by linear_combination hA - hB
  calc |√(1 + a ^ 2) - √(1 + b ^ 2)|
      ≤ |√(1 + a ^ 2) - √(1 + b ^ 2)| * (√(1 + a ^ 2) + √(1 + b ^ 2)) :=
        le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |a - b| * |a + b| := by
        rw [← abs_of_pos (by linarith : 0 < √(1 + a ^ 2) + √(1 + b ^ 2)), ← abs_mul, key,
          abs_mul]
    _ ≤ |a - b| * (|a| + |b|) := mul_le_mul_of_nonneg_left (abs_add_le a b) (abs_nonneg _)

/-- The function `t ↦ √(1 + t²)` is `1`-Lipschitz on the real line:
`|√(1 + a²) - √(1 + b²)| ≤ |a - b|`. -/
theorem abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub (a b : ℝ) :
    |√(1 + a ^ 2) - √(1 + b ^ 2)| ≤ |a - b| := by
  have hpos : 0 < √(1 + a ^ 2) + √(1 + b ^ 2) := by
    linarith [one_le_sqrt_one_add_sq a, one_le_sqrt_one_add_sq b]
  have hA : √(1 + a ^ 2) ^ 2 = 1 + a ^ 2 := sq_sqrt (by positivity)
  have hB : √(1 + b ^ 2) ^ 2 = 1 + b ^ 2 := sq_sqrt (by positivity)
  -- `|a| ≤ √(1 + a²)` and `|b| ≤ √(1 + b²)`, so the sum of the roots dominates `|a + b|`.
  have hab : |a + b| ≤ √(1 + a ^ 2) + √(1 + b ^ 2) :=
    (abs_add_le a b).trans (add_le_add (abs_le_sqrt (by nlinarith)) (abs_le_sqrt (by nlinarith)))
  refine le_of_mul_le_mul_right ?_ hpos
  -- `(√(1 + a²) - √(1 + b²)) (√(1 + a²) + √(1 + b²)) = (a - b) (a + b)`.
  rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos,
    show (√(1 + a ^ 2) - √(1 + b ^ 2)) * (√(1 + a ^ 2) + √(1 + b ^ 2)) = (a - b) * (a + b) by
      linear_combination hA - hB, abs_mul]
  exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)

/-- For every real `t`, `(1 + t) / 2 ≤ √(1 + t²)`. -/
theorem one_add_div_two_le_sqrt_one_add_sq (t : ℝ) : (1 + t) / 2 ≤ √(1 + t ^ 2) :=
  le_sqrt_of_sq_le (by nlinarith [sq_nonneg (t - 1)])

/-- If `a² ≤ c b²` with `0 ≤ b`, then `a ≤ √c * b`. -/
theorem le_sqrt_mul_of_sq_le_mul {a b c : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ c * b ^ 2) :
    a ≤ √c * b :=
  calc a ≤ |a| := le_abs_self a
    _ = √(a ^ 2) := (sqrt_sq_eq_abs a).symm
    _ ≤ √(c * b ^ 2) := sqrt_le_sqrt h
    _ = √c * b := by rw [sqrt_mul' _ (sq_nonneg b), sqrt_sq hb]

/-- **A square factor cancels against its absolute value.** For `d ≠ 0` and `0 ≤ c`,
`|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`. This is the cancellation of the Jacobian `|d|` of a change
of variables against the square root of an integrand that has acquired the factor `d²`. -/
theorem abs_mul_inv_sqrt_sq_mul_mul {d c : ℝ} (hd : d ≠ 0) (hc : 0 ≤ c) (p : ℝ) :
    |d| * (√(d ^ 2 * c * p))⁻¹ = (√c)⁻¹ * (√p)⁻¹ := by
  rw [sqrt_mul (mul_nonneg (sq_nonneg d) hc), sqrt_mul (sq_nonneg d), sqrt_sq_eq_abs, mul_inv,
    mul_inv, mul_assoc, mul_inv_cancel_left₀ (abs_ne_zero.2 hd)]

/-- The vector `((√2)⁻¹, (√2)⁻¹)` has unit length: `((√2)⁻¹)² + ((√2)⁻¹)² = 1`. -/
theorem inv_sqrt_two_sq_add_inv_sqrt_two_sq : (√2)⁻¹ ^ 2 + (√2)⁻¹ ^ 2 = (1 : ℝ) := by
  rw [inv_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

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

/-- For `0 < p`, `t + √(t² + p)` is positive. -/
theorem add_sqrt_sq_add_pos {p : ℝ} (hp : 0 < p) (t : ℝ) : 0 < t + √(t ^ 2 + p) := by
  rcases le_or_gt 0 t with ht | ht; · positivity
  rw [← neg_lt_iff_pos_add']
  nth_rw 1 [← abs_of_nonpos ht.le, ← sqrt_sq_eq_abs, ← add_zero (t ^ 2)]
  gcongr

/-- The derivative of `t ↦ t + √(t² + p)` for `0 < p`. -/
theorem hasDerivAt_add_sqrt_sq_add {p : ℝ} (hp : 0 < p) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ t + √(t ^ 2 + p)) ((t + √(t ^ 2 + p)) / √(t ^ 2 + p)) t := by
  rw [← div_add_one (by positivity), add_comm]
  apply (hasDerivAt_id' _).fun_add
  rw [← mul_div_mul_left _ _ two_ne_zero]
  refine ((HasDerivAt.add_const _) ?_).sqrt (by positivity)
  convert hasDerivAt_pow 2 t using 1
  ring

/-- For `0 < p`, the map `t ↦ t + √(t² + p)` sends `ℝ` onto `(0, ∞)`. -/
theorem image_add_sqrt_sq_add_eq_Ioi {p : ℝ} (hp : 0 < p) :
    (fun t : ℝ ↦ t + √(t ^ 2 + p)) '' Set.univ = Set.Ioi 0 := by
  ext x
  rw [Set.image_univ, Set.mem_range, Set.mem_Ioi]
  refine ⟨fun ⟨t, ht⟩ ↦ ht.symm ▸ add_sqrt_sq_add_pos hp t, fun hx ↦ ?_⟩
  use (x ^ 2 - p) / (2 * x)
  have hradicand : ((x ^ 2 - p) / (2 * x)) ^ 2 + p = ((x ^ 2 + p) / (2 * x)) ^ 2 := by
    field_simp
    ring
  have hsqrt : √(((x ^ 2 - p) / (2 * x)) ^ 2 + p) = (x ^ 2 + p) / (2 * x) := by
    rw [hradicand, sqrt_sq (by positivity)]
  rw [hsqrt]
  field_simp
  ring

/-- The derivative of `y ↦ α / (β y + √(y² + c))` at a point where `y² + c` and the denominator
do not vanish. -/
theorem hasDerivAt_div_mul_add_sqrt_sq_add (α β c : ℝ) {y : ℝ} (hyc : y ^ 2 + c ≠ 0)
    (hy : β * y + √(y ^ 2 + c) ≠ 0) :
    HasDerivAt (fun y => α / (β * y + √(y ^ 2 + c)))
      (-α * (β + y / √(y ^ 2 + c)) / (β * y + √(y ^ 2 + c)) ^ 2) y := by
  have hs : HasDerivAt (fun y => √(y ^ 2 + c)) (y / √(y ^ 2 + c)) y := by
    refine (((hasDerivAt_pow 2 y).add_const c).sqrt hyc).congr_deriv ?_
    norm_num [mul_div_mul_left _ _ (two_ne_zero' ℝ)]
  have hD : HasDerivAt (fun y => β * y + √(y ^ 2 + c)) (β + y / √(y ^ 2 + c)) y := by
    have := ((hasDerivAt_id y).const_mul β).add hs
    exact this.congr_deriv (by simp)
  have := (hasDerivAt_const y α).div hD hy
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

/-- For `c > 0`, `y ↦ y (√(y² + c) − y)` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_mul_sqrt_sq_add_sub {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun y => y * (√(y ^ 2 + c) - y)) (Set.Ici 0) := by
  intro y₁ h0 y₂ h2 h12
  simp only [Set.mem_Ici] at h0 h2
  have hs : ∀ y : ℝ, √(y ^ 2 + c) ^ 2 = y ^ 2 + c := fun y => sq_sqrt (by positivity)
  have hp : ∀ y : ℝ, 0 < √(y ^ 2 + c) := fun y => sqrt_pos.mpr (by positivity)
  -- `√(y² + c) − y = c / (√(y² + c) + y)`
  have hrw : ∀ y : ℝ, 0 ≤ y → √(y ^ 2 + c) - y = c / (√(y ^ 2 + c) + y) := by
    intro y hy
    rw [eq_div_iff (by linarith [hp y])]; nlinarith [hs y]
  dsimp only
  rw [hrw y₁ h0, hrw y₂ h2, mul_div_assoc', mul_div_assoc',
    div_lt_div_iff₀ (by linarith [hp y₁]) (by linarith [hp y₂])]
  have hkey : y₁ * √(y₂ ^ 2 + c) < y₂ * √(y₁ ^ 2 + c) := by
    refine lt_of_not_ge fun hcon => ?_
    have hnn : 0 ≤ y₂ * √(y₁ ^ 2 + c) := mul_nonneg h2 (hp _).le
    have := mul_self_le_mul_self hnn hcon
    nlinarith [hs y₁, hs y₂, mul_lt_mul_of_pos_left (mul_self_lt_mul_self h0 h12) hc]
  nlinarith [mul_lt_mul_of_pos_left hkey hc]

/-- Subadditivity of the square root: `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_add_sqrt (a b : ℝ) : √(a + b) ≤ √a + √b := by
  rcases le_or_gt 0 a with ha | ha
  · rcases le_or_gt 0 b with hb | hb
    · have h := rpow_add_le_add_rpow (p := 1 / 2) (a := a) (b := b) ha hb (by norm_num)
        (by norm_num)
      simpa only [← sqrt_eq_rpow] using h
    · rw [sqrt_eq_zero_of_nonpos hb.le, add_zero]
      exact sqrt_le_sqrt (by linarith)
  · rw [sqrt_eq_zero_of_nonpos ha.le, zero_add]
    exact sqrt_le_sqrt (by linarith)

/-- The forward difference of the square root is asymptotic to its derivative:
`√x (√(x + 1) - √x) → 1/2` as `x → ∞`. -/
theorem tendsto_sqrt_mul_sqrt_add_one_sub_sqrt :
    Tendsto (fun x : ℝ => √x * (√(x + 1) - √x)) atTop (𝓝 (1 / 2)) := by
  have hlim : Tendsto (fun x : ℝ => (√(1 + x⁻¹) + 1)⁻¹) atTop (𝓝 (1 / 2)) := by
    have h := ((tendsto_inv_atTop_zero.const_add 1).sqrt.add_const 1).inv₀ (by norm_num)
    norm_num at h
    simpa [one_div] using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have ha : 0 < √x := sqrt_pos.2 hx
  have hq : √(1 + x⁻¹) = √(x + 1) / √x := by
    rw [← sqrt_div (by linarith) x]
    congr 1
    field_simp
  rw [hq, div_add_one ha.ne', inv_div, eq_comm, eq_div_iff (by positivity)]
  linear_combination √x * (sq_sqrt (show 0 ≤ x + 1 by linarith) - sq_sqrt hx.le)

/-- The closed sublevel `{x² ≤ a}` of the square, for `0 ≤ a`, is the interval `[-√a, √a]`. -/
theorem setOf_sq_le_eq_Icc {a : ℝ} (ha : 0 ≤ a) : {x : ℝ | x ^ 2 ≤ a} = Set.Icc (-√a) √a := by
  ext x
  simp [sq_le ha]

/-- The closed superlevel `{a ≤ x²}` of the square is the union of the two rays
`(-∞, -√a]` and `[√a, ∞)`; for `a ≤ 0` they cover the line, since then `√a = 0`. -/
theorem setOf_le_sq_eq_union (a : ℝ) :
    {x : ℝ | a ≤ x ^ 2} = Set.Iic (-√a) ∪ Set.Ici √a := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  rw [← sqrt_le_sqrt_iff (sq_nonneg x), sqrt_sq_eq_abs, le_abs']

end Real

end
