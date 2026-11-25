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
import TauCeti.Analysis.Real.Sqrt

/-!
# Weighted square-root bounds, derivatives and regularity

This file records a weighted form `|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)` for
`0 ≤ γ ≤ 1` of the `1/2`-Hölder bound for the square root, the derivatives of `x ↦ √(x² + p)`,
`x ↦ β x + √(x² + p)`, `t ↦ t + √(t² + p)`, `y ↦ α / (β y + √(y² + c))` and `y ↦ √(a / y)`,
that `1 / √(1 + f²)` is as smooth as `f`, that `t ↦ √(1 + t²)` is smooth and `t ↦ δ √(1 + t²)`
has slope at most `|δ|`, that the radial
profile `t ↦ ψ (√t) / (√t) ^ n` of a `C^k` function supported in `(0, ∞)` is `C^k`, and the
Gaussian normalization `√(4 / π) = 2 / √π`. The elementary square-root bounds, identities and
limits that need no `rpow`, `π`, or calculus are in `TauCeti.Analysis.Real.Sqrt`.

## Main results

* `Real.abs_sqrt_sub_sqrt_mul_max_rpow_le`: for `0 ≤ γ ≤ 1`, the weighted bound
  `|√t - √s| max (√t) (√s) ^ γ ≤ |t - s| ^ ((1 + γ) / 2)`.
* `ContDiff.inv_sqrt_one_add_sq`: `x ↦ 1 / √(1 + f(x)²)` is as smooth as `f`.
* `Real.contDiff_sqrt_one_add_sq`: `t ↦ √(1 + t²)` is smooth.
* `Real.abs_deriv_mul_sqrt_one_add_sq_le`: the slope of `t ↦ δ √(1 + t²)` is at most `|δ|`.
* `Real.contDiff_div_sqrt_pow`: if `ψ` is `C^k` with support in `(0, ∞)`, then
  `t ↦ ψ (√t) / (√t) ^ n` is `C^k`.
* `Real.hasDerivAt_sqrt_sq_add`, `Real.hasDerivAt_mul_add_sqrt_sq_add`: the derivatives of
  `x ↦ √(x² + p)` and `x ↦ β x + √(x² + p)` wherever `t² + p ≠ 0`.
* `Real.hasDerivAt_add_sqrt_sq_add`: the substitution `t ↦ t + √(t² + p)` has an explicit
  derivative wherever `t² + p > 0`.
* `Real.hasDerivAt_div_mul_add_sqrt_sq_add`: the function `y ↦ α / (β y + √(y² + c))` has an
  explicit derivative where `y² + c` and the denominator do not vanish.
* `Real.hasDerivAt_sqrt_div`: the derivative of `y ↦ √(a / y)` wherever `y ≠ 0`.
* `TauCeti.sqrt_four_div_pi`: `√(4/π) = 2/√π`.

## References

`Real.hasDerivAt_add_sqrt_sq_add` is extracted from, and its proof adapted from, Jeremy Tan's
[Mathlib PR #34397](https://github.com/leanprover-community/mathlib4/pull/34397), commit
`376352b6e080265bc0380074baaf9aafa0b70a80`.

`Real.hasDerivAt_div_mul_add_sqrt_sq_add` is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean`.
-/

public section

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

/-- The function `x ↦ 1 / √(1 + f(x)²)` is as smooth as `f`. -/
theorem _root_.ContDiff.inv_sqrt_one_add_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n fun x ↦ (√(1 + f x ^ 2))⁻¹ :=
  ((contDiff_const.add (hf.pow 2)).sqrt fun _ ↦ by positivity).inv fun _ ↦ by positivity

/-- The function `t ↦ √(1 + t²)` is smooth. -/
theorem contDiff_sqrt_one_add_sq {n : WithTop ℕ∞} : ContDiff ℝ n fun t : ℝ ↦ √(1 + t ^ 2) :=
  (contDiff_const.add (contDiff_id.pow 2)).sqrt fun t ↦ by positivity

/-- The slope of `t ↦ δ √(1 + t²)` has absolute value at most `|δ|`, since `t ↦ √(1 + t²)` is
`1`-Lipschitz. For small `|δ|` this makes `e^{δ √(1 + t²)}` an admissible weight, comparable to
`e^{δ |t|}`, in weighted estimates that require a bounded slope. -/
theorem abs_deriv_mul_sqrt_one_add_sq_le (δ t : ℝ) :
    |deriv (fun t ↦ δ * √(1 + t ^ 2)) t| ≤ |δ| := by
  have h : LipschitzWith ‖δ‖₊ fun t : ℝ ↦ δ * √(1 + t ^ 2) :=
    LipschitzWith.of_dist_le_mul fun a b ↦ by
      rw [dist_eq, dist_eq, ← mul_sub, abs_mul, coe_nnNorm, norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub a b)
        (abs_nonneg δ)
  simpa using norm_deriv_le_of_lipschitz (x₀ := t) h

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

/-- The derivative of `y ↦ √(a / y)` at a point `x ≠ 0` is `-√(a / x) / (2x)`. Where `a / x < 0`
the function vanishes near `x`, matching the junk value `√(a / x) = 0`. -/
theorem hasDerivAt_sqrt_div (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ √(a / y)) (-(√(a / x) / (2 * x))) x := by
  by_cases ha : a = 0
  · simpa [ha] using hasDerivAt_const x (0 : ℝ)
  refine (((hasDerivAt_const x a).div (hasDerivAt_id' x) hx).sqrt
    (div_ne_zero ha hx)).congr_deriv ?_
  rw [Pi.div_apply]
  -- Both sides are `-(a / x) / √(a / x) / (2x)`, and `(a / x) / √(a / x) = √(a / x)`.
  conv_rhs => rw [← div_sqrt (x := a / x)]
  field_simp
  ring

end Real

namespace TauCeti

/-- The Gaussian normalization `√(4/π) = 2/√π`. It relates the constant `4/π` in the Mills-ratio
bounds of DLMF 7.8.2 to the prefactor `2/√π` of the error function. -/
theorem sqrt_four_div_pi : √(4 / Real.pi) = 2 / √Real.pi := by
  rw [Real.sqrt_div' _ Real.pi_pos.le,
    (Real.sqrt_eq_iff_mul_self_eq_of_pos two_pos).2 (by norm_num)]

end TauCeti

end
