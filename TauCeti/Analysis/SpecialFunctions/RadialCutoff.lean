/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth approximations of the indicator of `(-∞, 1)`

For the smooth transition function `s = Real.smoothTransition`, the function
`radialCutoffDeriv k t = s((k + 1)(1 - t))` is smooth, nonincreasing, with values in `[0, 1]`,
vanishes on `[1, ∞)` and is nondecreasing in `k`, tending to the indicator of `(-∞, 1)`.
Its primitive `radialCutoff k`, normalized to vanish on `[1, ∞)`, is smooth, nonpositive, and on
`[0, ∞)` bounded below by `-radialCutoffDeriv k`.

These are the radial cutoffs of the monotonicity formula for minimal submanifolds: testing the
first variation of area with the vector field `φ(|x - p|² / r²) (x - p)`, where
`φ = radialCutoff k` and `φ' = radialCutoffDeriv k`, yields identities involving the cutoff
and its derivative. In the limit, integrals of `φ'(|x - p|² / r²)` recover the area of the
submanifold inside the ball of radius `r` about `p`.

## Main definitions

* `TauCeti.radialCutoffDeriv`: the function `t ↦ s((k + 1)(1 - t))`.
* `TauCeti.radialCutoff`: its primitive vanishing on `[1, ∞)`.

## Main results

* `TauCeti.tendsto_radialCutoffDeriv`: `radialCutoffDeriv k t` tends to the indicator of
  `(-∞, 1)` at `t`.
* `TauCeti.antitone_radialCutoffDeriv`: each `radialCutoffDeriv k` is nonincreasing.
* `TauCeti.monotone_radialCutoffDeriv_apply`: `radialCutoffDeriv k t` is nondecreasing in `k`.
* `TauCeti.contDiff_radialCutoffDeriv`: each `radialCutoffDeriv k` is smooth.
* `TauCeti.hasDerivAt_radialCutoff` and `TauCeti.contDiff_radialCutoff`: `radialCutoff k` is a
  smooth primitive of `radialCutoffDeriv k`.
* `TauCeti.neg_radialCutoffDeriv_le_radialCutoff`: `-radialCutoffDeriv k τ ≤ radialCutoff k τ`
  for `τ ≥ 0`.

## References

* T. H. Colding and W. P. Minicozzi II, *A Course in Minimal Surfaces*, Graduate Studies in
  Mathematics 121, American Mathematical Society (2011), Chapter 1, §3.
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti

/-- The derivative of the `k`-th radial cutoff: `t ↦ s((k + 1)(1 - t))` for the smooth
transition function `s`. -/
def radialCutoffDeriv (k : ℕ) (t : ℝ) : ℝ := Real.smoothTransition ((k + 1) * (1 - t))

/-- The `k`-th radial cutoff, the primitive of `radialCutoffDeriv k` vanishing at `1`. -/
def radialCutoff (k : ℕ) (τ : ℝ) : ℝ := ∫ t in (1 : ℝ)..τ, radialCutoffDeriv k t

/-- The explicit smooth transition defining the cutoff derivative. -/
theorem radialCutoffDeriv_def (k : ℕ) (t : ℝ) :
    radialCutoffDeriv k t = Real.smoothTransition ((k + 1) * (1 - t)) := (rfl)

/-- The interval-integral formula for the cutoff normalized at `1`. -/
theorem radialCutoff_def (k : ℕ) (τ : ℝ) :
    radialCutoff k τ = ∫ t in (1 : ℝ)..τ, radialCutoffDeriv k t := (rfl)

/-- Each cutoff derivative is smooth to every order. -/
@[fun_prop]
theorem contDiff_radialCutoffDeriv (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (radialCutoffDeriv k) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

@[simp, grind =]
theorem radialCutoffDeriv_of_one_le {k : ℕ} {t : ℝ} (ht : 1 ≤ t) : radialCutoffDeriv k t = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (by linarith))

theorem radialCutoffDeriv_nonneg (k : ℕ) (t : ℝ) : 0 ≤ radialCutoffDeriv k t :=
  Real.smoothTransition.nonneg _

theorem radialCutoffDeriv_le_one (k : ℕ) (t : ℝ) : radialCutoffDeriv k t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff derivative equals one on the plateau of its defining transition. -/
theorem radialCutoffDeriv_eq_one {k : ℕ} {t : ℝ} (ht : 1 ≤ (k + 1 : ℝ) * (1 - t)) :
    radialCutoffDeriv k t = 1 := Real.smoothTransition.one_of_one_le ht

/-- The cutoff derivative is normalized to one at zero. -/
@[simp, grind =]
theorem radialCutoffDeriv_zero (k : ℕ) : radialCutoffDeriv k 0 = 1 :=
  radialCutoffDeriv_eq_one (by simp)

/-- The cutoff derivative vanishes exactly on `[1, ∞)`. -/
@[simp]
theorem radialCutoffDeriv_eq_zero_iff (k : ℕ) (t : ℝ) :
    radialCutoffDeriv k t = 0 ↔ 1 ≤ t := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [radialCutoffDeriv_def, Real.smoothTransition.zero_iff_nonpos]
  simpa only [mul_zero, sub_nonpos] using
    (mul_le_mul_iff_right₀ hk (b := 1 - t) (c := 0))

/-- Each `radialCutoffDeriv k` is nonincreasing. -/
theorem antitone_radialCutoffDeriv (k : ℕ) : Antitone (radialCutoffDeriv k) := fun _ _ hst ↦
  Real.smoothTransition.monotone (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- At each point, the cutoff derivatives are nondecreasing in the approximation index. -/
theorem monotone_radialCutoffDeriv_apply (t : ℝ) : Monotone (fun k ↦ radialCutoffDeriv k t) := by
  intro k l hkl
  rcases le_total t 1 with ht | ht
  · exact Real.smoothTransition.monotone
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hkl 1) (sub_nonneg.2 ht))
  · simp [ht]

/-- The derivative of `radialCutoffDeriv k`, the second derivative of the cutoff, is
nonpositive. -/
theorem deriv_radialCutoffDeriv_nonpos (k : ℕ) (t : ℝ) : deriv (radialCutoffDeriv k) t ≤ 0 :=
  (antitone_radialCutoffDeriv k).deriv_nonpos

/-- **Convergence to the indicator.** As `k → ∞`, `radialCutoffDeriv k t` tends to `1` for
`t < 1` and to `0` for `t ≥ 1`. -/
theorem tendsto_radialCutoffDeriv (t : ℝ) :
    Tendsto (fun k ↦ radialCutoffDeriv k t) atTop (𝓝 (if t < 1 then 1 else 0)) := by
  simpa [radialCutoffDeriv, sub_nonpos, ← not_lt, ite_not] using
    (Real.smoothTransition.tendsto_add_mul_add_deriv_mul
      (t := 1 - t) (d := 0) (e := 1) (k := 0))

/-- The normalized cutoff has derivative `radialCutoffDeriv k τ` at every point `τ`. -/
theorem hasDerivAt_radialCutoff (k : ℕ) (τ : ℝ) :
    HasDerivAt (radialCutoff k) (radialCutoffDeriv k τ) τ :=
  ((contDiff_radialCutoffDeriv k (n := 0)).continuous.integral_hasStrictDerivAt 1 τ).hasDerivAt

/-- The derivative of the normalized cutoff is the cutoff derivative as a function. -/
@[simp, grind =]
theorem deriv_radialCutoff (k : ℕ) : deriv (radialCutoff k) = radialCutoffDeriv k :=
  funext fun τ ↦ (hasDerivAt_radialCutoff k τ).deriv

/-- The normalized cutoff is a smooth primitive to every order. -/
@[fun_prop]
theorem contDiff_radialCutoff (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (radialCutoff k) :=
  (contDiff_infty_iff_deriv.2 ⟨fun τ ↦ (hasDerivAt_radialCutoff k τ).differentiableAt,
    deriv_radialCutoff k ▸ contDiff_radialCutoffDeriv k⟩).of_le (by exact_mod_cast le_top)

@[simp, grind =]
theorem radialCutoff_of_one_le {k : ℕ} {τ : ℝ} (hτ : 1 ≤ τ) : radialCutoff k τ = 0 := by
  rw [radialCutoff, intervalIntegral.integral_congr (g := fun _ ↦ 0) fun t ht ↦ ?_]
  · simp
  · rw [uIcc_of_le hτ] at ht
    exact radialCutoffDeriv_of_one_le ht.1

/-- The normalized cutoff vanishes exactly on `[1, ∞)`. -/
@[simp]
theorem radialCutoff_eq_zero_iff (k : ℕ) (τ : ℝ) : radialCutoff k τ = 0 ↔ 1 ≤ τ := by
  refine ⟨fun h ↦ ?_, radialCutoff_of_one_le⟩
  by_contra hτ
  have hτ' := lt_of_not_ge hτ
  have hpos : 0 < ∫ t in τ..1, radialCutoffDeriv k t :=
    intervalIntegral.integral_pos hτ'
      (contDiff_radialCutoffDeriv k (n := 0)).continuous.continuousOn
      (fun t _ ↦ radialCutoffDeriv_nonneg k t)
      ⟨τ, ⟨le_rfl, hτ'.le⟩, Real.smoothTransition.pos_of_pos (by positivity)⟩
  rw [radialCutoff_def, intervalIntegral.integral_symm] at h
  linarith

/-- The normalized cutoff is nondecreasing in its spatial argument. -/
theorem monotone_radialCutoff (k : ℕ) : Monotone (radialCutoff k) :=
  monotone_of_deriv_nonneg (fun τ ↦ (hasDerivAt_radialCutoff k τ).differentiableAt)
    (by simpa using radialCutoffDeriv_nonneg k)

theorem radialCutoff_nonpos (k : ℕ) (τ : ℝ) : radialCutoff k τ ≤ 0 := by
  rcases le_total 1 τ with hτ | hτ
  · rw [radialCutoff_of_one_le hτ]
  · rw [radialCutoff, intervalIntegral.integral_symm, neg_nonpos]
    exact intervalIntegral.integral_nonneg hτ fun t _ ↦ radialCutoffDeriv_nonneg k t

/-- On `[0, ∞)` the cutoff is bounded below by minus its derivative. -/
theorem neg_radialCutoffDeriv_le_radialCutoff (k : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    -radialCutoffDeriv k τ ≤ radialCutoff k τ := by
  rcases le_total 1 τ with h1 | h1
  · rw [radialCutoff_of_one_le h1, radialCutoffDeriv_of_one_le h1, neg_zero]
  · rw [radialCutoff, intervalIntegral.integral_symm, neg_le_neg_iff]
    calc ∫ t in τ..1, radialCutoffDeriv k t ≤ ∫ _ in τ..1, radialCutoffDeriv k τ :=
          intervalIntegral.integral_mono_on h1
            ((contDiff_radialCutoffDeriv k (n := 0)).continuous.intervalIntegrable _ _)
            intervalIntegrable_const fun t ht ↦ antitone_radialCutoffDeriv k ht.1
      _ = (1 - τ) * radialCutoffDeriv k τ := by simp
      _ ≤ radialCutoffDeriv k τ := by nlinarith [radialCutoffDeriv_nonneg k τ]

grind_pattern radialCutoffDeriv_nonneg => radialCutoffDeriv k t
grind_pattern radialCutoffDeriv_le_one => radialCutoffDeriv k t
grind_pattern deriv_radialCutoffDeriv_nonpos => deriv (radialCutoffDeriv k) t
grind_pattern radialCutoff_nonpos => radialCutoff k τ
grind_pattern neg_radialCutoffDeriv_le_radialCutoff => radialCutoff k τ

end TauCeti
