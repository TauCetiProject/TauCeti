/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5, Claude Opus 4.8, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp

/-!
# Square-root displacement estimates and limits at zero

Two estimates comparing the real square-root and inverse-square-root functions
with the identity near `1`. These bounds control scalar spectral factors of
positive operators close to the identity. The file also records that the square root is
`1/2`-Hölder, `|√t - √s| ≤ √|t - s|`, that `c √u` tends to `0` as `u → 0`, and through
positive values as `u → 0⁺` when `c > 0`, and the cancellation `|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`
used in changes of variables, and that the radial profile `t ↦ ψ (√t) / (√t) ^ n` of a `C^k`
function supported in `(0, ∞)` is `C^k`.

## Main results

* `Real.abs_sqrt_sub_one_le_abs_sub_one`: for every real `μ`,
  `|√μ - 1| ≤ |μ - 1|`.
* `Real.abs_one_sub_inv_sqrt_le`: if `|μ - 1| ≤ δ ≤ 1/2`,
  `|1 - (√μ)⁻¹| ≤ δ`.
* `Real.abs_sqrt_sub_sqrt_le`: for all reals `t` and `s`, `|√t - √s| ≤ √|t - s|`.
* `Real.abs_mul_inv_sqrt_sq_mul_mul`: for `d ≠ 0` and `0 ≤ c`,
  `|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`.
* `Real.tendsto_mul_sqrt_nhds_zero`: `c √u → 0` as `u → 0`.
* `Real.tendsto_mul_sqrt_nhdsGT_zero`, `Real.tendsto_sqrt_nhdsGT_zero`: for `c > 0`,
  `c √u → 0⁺` as `u → 0⁺`.
* `Real.add_sqrt_sq_add_pos`, `Real.hasDerivAt_add_sqrt_sq_add`,
  `Real.image_add_sqrt_sq_add_eq_Ioi`: the substitution `t ↦ t + √(t² + p)`
  is positive, has an explicit derivative, and maps `ℝ` onto `(0, ∞)` for `p > 0`.
* `Real.contDiff_div_sqrt_pow`: if `ψ` is `C^k` with support in `(0, ∞)`, then
  `t ↦ ψ (√t) / (√t) ^ n` is `C^k`.

## References

[AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
`ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`.
-/

public section

open Filter
open scoped Topology

namespace Real

/-- For every real `μ`, the square root is no farther from `1` than `μ` is:
`|√μ - 1| ≤ |μ - 1|`. -/
theorem abs_sqrt_sub_one_le_abs_sub_one {μ : ℝ} :
    |Real.sqrt μ - 1| ≤ |μ - 1| := by
  rcases le_total 0 μ with hμ | hμ
  · have hs : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg μ
    have hsq : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ
    have key : |Real.sqrt μ - 1| * (Real.sqrt μ + 1) = |μ - 1| := by
      rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt μ + 1), ← abs_mul]
      congr 1
      nlinarith [hsq]
    nlinarith [key, mul_nonneg (abs_nonneg (Real.sqrt μ - 1)) hs]
  · have hsqrt : Real.sqrt μ = 0 := Real.sqrt_eq_zero_of_nonpos hμ
    calc
      |Real.sqrt μ - 1| = 1 := by rw [hsqrt]; norm_num
      _ ≤ |μ - 1| := by
        rw [abs_of_nonpos (by linarith : μ - 1 ≤ 0)]
        linarith

/-- If `|μ - 1| ≤ δ ≤ 1 / 2`, then `|1 - (√μ)⁻¹| ≤ δ`.

The hypotheses force `μ` to be positive and keep the inverse square root
bounded near `1`. -/
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) :
    |1 - (Real.sqrt μ)⁻¹| ≤ δ := by
  have hμlb : 1 - δ ≤ μ := by rw [abs_le] at hμ; linarith
  have hμpos : (0 : ℝ) < μ := by linarith
  set s := Real.sqrt μ
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμpos
  have hssq : s ^ 2 = μ := Real.sq_sqrt (le_of_lt hμpos)
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

/-- **A square factor cancels against its absolute value.** For `d ≠ 0` and `0 ≤ c`,
`|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`. This is the cancellation of the Jacobian `|d|` of a change
of variables against the square root of an integrand that has acquired the factor `d²`. -/
theorem abs_mul_inv_sqrt_sq_mul_mul {d c : ℝ} (hd : d ≠ 0) (hc : 0 ≤ c) (p : ℝ) :
    |d| * (√(d ^ 2 * c * p))⁻¹ = (√c)⁻¹ * (√p)⁻¹ := by
  rw [sqrt_mul (mul_nonneg (sq_nonneg d) hc), sqrt_mul (sq_nonneg d), sqrt_sq_eq_abs, mul_inv,
    mul_inv, mul_assoc, mul_inv_cancel_left₀ (abs_ne_zero.2 hd)]

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
  · have ht0 : 0 < t := Real.sqrt_pos.mp (hψs ht)
    exact ((hψ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0.ne')).div
      ((Real.contDiffAt_sqrt ht0.ne').pow _) (pow_ne_zero _ (Real.sqrt_pos.mpr ht0).ne'))
  · have hev : ∀ᶠ s in 𝓝 t, ψ (√s) / (√s) ^ n = 0 := by
      have : ∀ᶠ s in 𝓝 t, √s ∉ tsupport ψ :=
        Real.continuous_sqrt.continuousAt.preimage_mem_nhds
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
    rw [hradicand, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  field_simp
  ring

end Real

end
