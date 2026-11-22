/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.FiniteProduct
-- Reuse the private `(0+)` keyhole contour helpers from `LoopIntegral.lean`.
import all TauCeti.Analysis.SpecialFunctions.Hypergeometric.LoopIntegral

/-!
# Pochhammer's double-loop contour integral for the Gauss hypergeometric function

Pochhammer's `(0+, 1+, 0-, 1-)` commutator contour integral `Complex.hypergeometricPochhammerLoop`
(DLMF 15.6.5) removes both endpoint integrability restrictions of Euler's integral
`Complex.eulerIntegral` simultaneously. Starting and ending at a basepoint `A ∈ (0, 1)` where
`ph t = ph (1 - t) = 0`, with circle radii `0 < ρ₀ < A` around `0` and `0 < ρ₁ < 1 - A` around `1`,
the contour avoids both branch points `0` and `1`: the circular arcs cross the branch cuts
`(-∞, 0]` of `t ^ (b - 1)` and `[1, ∞)` of `(1 - t) ^ (c - b - 1)` with explicitly tracked branches
(`t = ρ₀ e^{iθ}` for `θ ∈ [0, 2π]` and `t = 1 - ρ₁ e^{iφ}` for `φ ∈ [0, 2π]`), accruing the
monodromy factors `exp (2πi (b - 1))` and `exp (2πi (c - b - 1))` on the intervening radial
segments. Meanwhile, for `z` in the principal cut plane `{z | 1 - z ∈ Complex.slitPlane}`, the
admissibility conditions `‖z‖ * ρ₀ < 1` and
`Metric.closedBall (1 - z) (‖z‖ * ρ₁) ⊆ Complex.slitPlane` keep `1 - z * t` inside
`Complex.slitPlane` along the entire contour, so the principal branch of `(1 - z * t) ^ (-a)`
crosses no branch cut.

Splitting the radial segments at `A` expresses `Complex.hypergeometricPochhammerLoop` as a linear
combination of the two `(0+)` keyhole pieces from
`TauCeti.Analysis.SpecialFunctions.Hypergeometric.LoopIntegral`. Consequently:

* `Complex.hypergeometricPochhammerLoop_eq`: for all complex parameters `(a, b, c)`, the integral is
  independent of admissible `(A, ρ₀, ρ₁)` satisfying `0 < ρ₀ < A`, `0 < ρ₁ < 1 - A`,
  `‖z‖ * ρ₀ < 1`, and `Metric.closedBall (1 - z) (‖z‖ * ρ₁) ⊆ Complex.slitPlane`.
* `Complex.analyticOnNhd_hypergeometricPochhammerLoop`: for fixed `0 < ρ₀ < A` and `0 < ρ₁ < 1 - A`,
  the integral is jointly holomorphic in all four variables `(a, b, c, z)` on
  `{p | ‖p.2.2.2‖ * ρ₀ < 1 ∧ Metric.closedBall (1 - p.2.2.2) (‖p.2.2.2‖ * ρ₁) ⊆ Complex.slitPlane}`
  with no real-part restrictions.
* `Complex.hypergeometricPochhammerLoop_eq_integral`,
  `Complex.hypergeometricPochhammerLoop_eq_eulerIntegral`, and
  `Complex.eulerIntegral_eq_hypergeometricPochhammerLoop`: for `0 < re b < re c` and admissible
  `(A, ρ₀, ρ₁)`, shrinking the radii collapses the contour onto `[0, 1]`, yielding DLMF 15.6.5 on
  the cut plane (with `b, c - b ∉ {1, 2, …}` for
  `Complex.eulerIntegral_eq_hypergeometricPochhammerLoop`).
* `Complex.hypergeometricPochhammerLoop_zero` and `Complex.hypergeometricPochhammerLoop_zero_left`:
  at `z = 0` or `a = 0` with `0 < ρ₀ < A` and `0 < ρ₁ < 1 - A`, parameter holomorphy evaluates the
  integral in closed form via reciprocal Gamma factors across all `(b, c) ∈ ℂ × ℂ`, yielding
  Pochhammer's contour integral for Euler's Beta function (DLMF 5.12.12).

## References

* NIST Digital Library of Mathematical Functions, §§5.12 (5.12.12) and 15.6 (15.6.5).
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5, §9.3.
* N. M. Temme, *Special Functions*, §5.2.2; E. T. Whittaker and G. N. Watson, *A Course of Modern
  Analysis*, §§12.43 and 14.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Real Set
open scoped Topology Interval

namespace Complex

private theorem analyticAt_integral_affineSegIntegrand_compact {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] {fa fβ fγ fw₀ fw₁ : V → ℂ} {p : V}
    (ha : AnalyticAt ℂ fa p) (hβ : AnalyticAt ℂ fβ p) (hγ : AnalyticAt ℂ fγ p)
    (hw₀ : AnalyticAt ℂ fw₀ p) (hw₁ : AnalyticAt ℂ fw₁ p)
    {ρ A : ℝ} (hρ : 0 < ρ) (hρA : ρ ≤ A) (hA1 : A < 1)
    (hslit : ∀ u ∈ Icc ρ A, fw₀ p - fw₁ p * u ∈ slitPlane) :
    AnalyticAt ℂ (fun q => ∫ u : ℝ in ρ..A,
      affineSegIntegrand (fa q) (fβ q) (fγ q) (fw₀ q) (fw₁ q) u) p := by
  let φ : ℝ → ℂ := fun u => ((projIcc ρ A hρA u : ℝ) : ℂ)
  let K : Set ℂ := ofReal '' Icc ρ A
  have hφ : Continuous φ := continuous_ofReal.comp (continuous_subtypeVal.comp continuous_projIcc)
  have hφK (u : ℝ) : φ u ∈ K := ⟨_, (projIcc ρ A hρA u).property, rfl⟩
  have hkernel : ∀ y ∈ K, AnalyticAt ℂ (fun x : V × ℂ =>
      x.2 ^ (fβ x.1 - 1) * (1 - x.2) ^ (fγ x.1 - 1) *
        (fw₀ x.1 - fw₁ x.1 * x.2) ^ (-fa x.1)) (p, y) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu1 : 1 - (u : ℂ) ∈ slitPlane := by
      have h1 : (0 : ℝ) < 1 - u := sub_pos.mpr (hu.2.trans_lt hA1)
      simpa using ofReal_mem_slitPlane.mpr h1
    refine ((analyticAt_snd.cpow ((hβ.comp analyticAt_fst).sub analyticAt_const)
      (ofReal_mem_slitPlane.mpr (hρ.trans_le hu.1))).mul
      ((analyticAt_const.sub analyticAt_snd).cpow ((hγ.comp analyticAt_fst).sub analyticAt_const)
        hu1)).mul ?_
    exact ((hw₀.comp analyticAt_fst).sub ((hw₁.comp analyticAt_fst).mul analyticAt_snd)).cpow
      (ha.comp analyticAt_fst).neg (hslit u hu)
  have hweight : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ioc ρ A)) := by simp
  convert TauCeti.analyticAt_integral_smul (isCompact_Icc.image continuous_ofReal) hφ hφK hkernel
    hweight using 1
  ext q
  rw [intervalIntegral.integral_of_le hρA]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simp [φ, projIcc_of_mem hρA (Ioc_subset_Icc_self hu), affineSegIntegrand]

/-- Pochhammer's double-loop contour integral `(0+, 1+, 0-, 1-)` (DLMF 15.6.5) starting and
terminating at `A ∈ (0, 1)` where `ph t = 0` and `ph (1 - t) = 0`, with circle radii `ρ₀` around
`0` and `ρ₁` around `1`. -/
def hypergeometricPochhammerLoop (a b c z : ℂ) (A ρ₀ ρ₁ : ℝ) : ℂ :=
  (∫ t : ℝ in A..ρ₀,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) +
    (∫ θ : ℝ in 0..(2 * π),
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
    (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) +
    (∫ φ : ℝ in 0..(2 * π),
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
        ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
    (∫ t : ℝ in (1 - ρ₁)..ρ₀,
      (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
        ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) * (1 - z * t) ^ (-a)) +
    (∫ θ : ℝ in (2 * π)..0,
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
    (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
        (1 - z * t) ^ (-a)) +
    (∫ φ : ℝ in (2 * π)..0,
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) *
        ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
    ∫ t : ℝ in (1 - ρ₁)..A,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)

/-- The explicit nine-piece contour formula defining `Complex.hypergeometricPochhammerLoop`. -/
theorem hypergeometricPochhammerLoop_def (a b c z : ℂ) (A ρ₀ ρ₁ : ℝ) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      (∫ t : ℝ in A..ρ₀,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) +
        (∫ θ : ℝ in 0..(2 * π),
          ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
            (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
            (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
        (∫ t : ℝ in ρ₀..(1 - ρ₁),
          (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) * (1 - (t : ℂ)) ^ (c - b - 1) *
            (1 - z * t) ^ (-a)) +
        (∫ φ : ℝ in 0..(2 * π),
          (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
            ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
            (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
        (∫ t : ℝ in (1 - ρ₁)..ρ₀,
          (t : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
            ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
            (1 - z * t) ^ (-a)) +
        (∫ θ : ℝ in (2 * π)..0,
          ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
            ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
            (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
        (∫ t : ℝ in ρ₀..(1 - ρ₁),
          (t : ℂ) ^ (b - 1) * ((1 - (t : ℂ)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
            (1 - z * t) ^ (-a)) +
        (∫ φ : ℝ in (2 * π)..0,
          (1 - ρ₁ * exp (φ * I)) ^ (b - 1) *
            ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
            (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
        ∫ t : ℝ in (1 - ρ₁)..A,
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := (rfl)

private theorem pochhammer_seg_split (a b c z : ℂ) (hz : 1 - z ∈ slitPlane)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    (∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t) =
      (∫ t : ℝ in ρ₀..A, affineSegIntegrand a b (c - b) 1 z t) +
        ∫ u : ℝ in ρ₁..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u := by
  have h1ρ₁ : 1 - ρ₁ < 1 := by linarith
  have hcont := continuousOn_affineSegIntegrand_Icc a b (c - b) 1 z hρ₀ h1ρ₁ fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hz ⟨hρ₀.le.trans hu.1, hu.2.trans h1ρ₁.le⟩
  have hint_left : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume ρ₀ A :=
    (hcont.mono (by
      rw [uIcc_of_le hρ₀A.le]; exact Icc_subset_Icc_right (by linarith))).intervalIntegrable
  have hint_right : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume A (1 - ρ₁) :=
    (hcont.mono (by
      rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc_left hρ₀A.le)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_left hint_right]
  congr 1
  have hsub := intervalIntegral.integral_comp_sub_left
    (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A) (b := 1 - ρ₁)
  rw [sub_sub_cancel] at hsub
  rw [← hsub]
  exact intervalIntegral.integral_congr fun t _ => (affineSegIntegrand_one_sub a b c z t).symm

private theorem pochhammer_circ_sum (a b c z : ℂ) (ρ₀ ρ₁ : ℝ) :
    (∫ θ : ℝ in 0..(2 * π),
        ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
          (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
      (∫ φ : ℝ in 0..(2 * π),
        (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
          ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
          (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) +
      (∫ θ : ℝ in (2 * π)..0,
        ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
          ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * exp (2 * π * I * (c - b - 1))) *
          (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) +
      (∫ φ : ℝ in (2 * π)..0,
        (1 - ρ₁ * exp (φ * I)) ^ (b - 1) *
          ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
          (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) =
      (1 - exp (2 * π * I * (c - b - 1))) *
          (∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a b (c - b) 1 z ρ₀ θ) +
        (1 - exp (2 * π * I * (b - 1))) *
          ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ₁ φ := by
  set eb := exp (2 * π * I * (b - 1))
  set ecb := exp (2 * π * I * (c - b - 1))
  have hc2 : (∫ θ : ℝ in 0..(2 * π),
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) * (1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) =
      ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a b (c - b) 1 z ρ₀ θ := rfl
  have hc4 : (∫ φ : ℝ in 0..(2 * π),
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * eb * ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) =
      -eb * ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ₁ φ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hb : (1 - z) - (-z) * ((ρ₁ : ℂ) * exp (φ * I)) = 1 - z * (1 - ρ₁ * exp (φ * I)) := by ring
    simp only [affineCircIntegrand, hb]; ring
  have hc6 : (∫ θ : ℝ in (2 * π)..0,
      ((ρ₀ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        ((1 - ρ₀ * exp (θ * I)) ^ (c - b - 1) * ecb) *
        (1 - z * (ρ₀ * exp (θ * I))) ^ (-a) * (I * ρ₀ * exp (θ * I))) =
      -ecb * ∫ θ : ℝ in 0..(2 * π), affineCircIntegrand a b (c - b) 1 z ρ₀ θ := by
    rw [intervalIntegral.integral_symm, neg_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [affineCircIntegrand]; ring
  have hc8 : (∫ φ : ℝ in (2 * π)..0,
      (1 - ρ₁ * exp (φ * I)) ^ (b - 1) * ((ρ₁ : ℂ) ^ (c - b - 1) * exp (φ * I * (c - b - 1))) *
        (1 - z * (1 - ρ₁ * exp (φ * I))) ^ (-a) * (-I * ρ₁ * exp (φ * I))) =
      ∫ φ : ℝ in 0..(2 * π), affineCircIntegrand a (c - b) b (1 - z) (-z) ρ₁ φ := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hb : (1 - z) - (-z) * ((ρ₁ : ℂ) * exp (φ * I)) = 1 - z * (1 - ρ₁ * exp (φ * I)) := by ring
    simp only [affineCircIntegrand, hb]; ring
  rw [hc2, hc4, hc6, hc8]
  ring

private theorem hypergeometricPochhammerLoop_eq_affineLoopZero (a b c z : ℂ)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hz : 1 - z ∈ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      (1 - exp (2 * π * I * (c - b - 1))) * affineLoopZero a b (c - b) 1 z A ρ₀ +
        (1 - exp (2 * π * I * (b - 1))) *
          affineLoopZero a (c - b) b (1 - z) (-z) (1 - A) ρ₁ := by
  set eb := exp (2 * π * I * (b - 1))
  set ecb := exp (2 * π * I * (c - b - 1))
  have hs1 : (∫ t : ℝ in A..ρ₀,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      -∫ t : ℝ in ρ₀..A, affineSegIntegrand a b (c - b) 1 z t :=
    intervalIntegral.integral_symm ρ₀ A
  have hs3 : (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * eb * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      eb * ∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  have hs5 : (∫ t : ℝ in (1 - ρ₁)..ρ₀,
      (t : ℂ) ^ (b - 1) * eb * ((1 - (t : ℂ)) ^ (c - b - 1) * ecb) * (1 - z * t) ^ (-a)) =
      -(eb * ecb) * ∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t := by
    rw [intervalIntegral.integral_symm, neg_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  have hs7 : (∫ t : ℝ in ρ₀..(1 - ρ₁),
      (t : ℂ) ^ (b - 1) * ((1 - (t : ℂ)) ^ (c - b - 1) * ecb) * (1 - z * t) ^ (-a)) =
      ecb * ∫ t : ℝ in ρ₀..(1 - ρ₁), affineSegIntegrand a b (c - b) 1 z t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [affineSegIntegrand]; ring
  have hs9 : (∫ t : ℝ in (1 - ρ₁)..A,
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      -∫ u : ℝ in ρ₁..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u := by
    rw [intervalIntegral.integral_symm]
    congr 1
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A) (b := 1 - ρ₁)
    rw [sub_sub_cancel] at hsub
    rw [← hsub]
    exact intervalIntegral.integral_congr fun t _ => (affineSegIntegrand_one_sub a b c z t).symm
  have hcirc := pochhammer_circ_sum a b c z ρ₀ ρ₁
  rw [hypergeometricPochhammerLoop_def, hs1, hs3, hs5, hs7, hs9,
    pochhammer_seg_split a b c z hz hρ₀ hρ₀A hρ₁ hρ₁A, affineLoopZero, affineLoopZero]
  linear_combination hcirc

private theorem pochhammer_change_radii (a b c z : ℂ) {A ρ₀ ρ₀' ρ₁ ρ₁' : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₀' : 0 < ρ₀') (hρ₀'A : ρ₀' < A)
    (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) (hρ₁' : 0 < ρ₁') (hρ₁'A : ρ₁' < 1 - A)
    (hz₀ : ‖z‖ * ρ₀ < 1) (hz₀' : ‖z‖ * ρ₀' < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane)
    (hz₁' : closedBall (1 - z) (‖z‖ * ρ₁') ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      hypergeometricPochhammerLoop a b c z A ρ₀' ρ₁' := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  have hA1 : A < 1 := by linarith
  have h1A1 : 1 - A < 1 := by linarith
  have hint₀ (r : ℝ) (hr : 0 < r) (hrA : r < A) :
      IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume r A :=
    (continuousOn_affineSegIntegrand_Icc a b (c - b) 1 z hr hA1 fun u hu =>
      one_sub_mul_ofReal_mem_slitPlane hz
        ⟨hr.le.trans hu.1, hu.2.trans hA1.le⟩).intervalIntegrable_of_Icc hrA.le
  have hint₁ (r : ℝ) (hr : 0 < r) (hrA : r < 1 - A) :
      IntervalIntegrable (affineSegIntegrand a (c - b) b (1 - z) (-z)) volume r (1 - A) :=
    (continuousOn_affineSegIntegrand_Icc a (c - b) b (1 - z) (-z) hr h1A1 fun u hu => by
      rw [show (1 - z) - (-z) * (u : ℂ) = 1 - z * ((1 - u : ℝ) : ℂ) by push_cast; ring]
      exact one_sub_mul_ofReal_mem_slitPlane hz
        ⟨sub_nonneg.mpr (hu.2.trans h1A1.le),
          sub_le_self _ (hr.le.trans hu.1)⟩).intervalIntegrable_of_Icc hrA.le
  rw [hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hρ₀ hρ₀A hρ₁ hρ₁A hz,
    hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hρ₀' hρ₀'A hρ₁' hρ₁'A hz,
    affineLoopZero_eq_of_radius a b (c - b) 1 z hρ₀ (hρ₀A.trans hA1) hρ₀' (hρ₀'A.trans hA1)
      (closedBall_one_subset_slitPlane_iff.mpr hz₀) (closedBall_one_subset_slitPlane_iff.mpr hz₀')
      (hint₀ ρ₀ hρ₀ hρ₀A) (hint₀ ρ₀' hρ₀' hρ₀'A),
    affineLoopZero_eq_of_radius a (c - b) b (1 - z) (-z) hρ₁ (hρ₁A.trans h1A1) hρ₁'
      (hρ₁'A.trans h1A1) (by simpa only [norm_neg] using hz₁)
      (by simpa only [norm_neg] using hz₁') (hint₁ ρ₁ hρ₁ hρ₁A) (hint₁ ρ₁' hρ₁' hρ₁'A)]

private theorem pochhammer_change_basepoint (a b c z : ℂ) (hz : 1 - z ∈ slitPlane)
    {A A' r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₀A : r₀ < A) (hr₀A' : r₀ < A')
    (hr₁ : 0 < r₁) (hr₁A : r₁ < 1 - A) (hr₁A' : r₁ < 1 - A') :
    hypergeometricPochhammerLoop a b c z A r₀ r₁ =
      hypergeometricPochhammerLoop a b c z A' r₀ r₁ := by
  rw [hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hr₀ hr₀A hr₁ hr₁A hz,
    hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hr₀ hr₀A' hr₁ hr₁A' hz]
  have hAA' : max A A' < 1 := max_lt (by linarith) (by linarith)
  have h1AA' : max (1 - A) (1 - A') < 1 := max_lt (by linarith) (by linarith)
  have hcont₀ := continuousOn_affineSegIntegrand_Icc a b (c - b) 1 z hr₀ hAA' fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hz ⟨hr₀.le.trans hu.1, hu.2.trans hAA'.le⟩
  have hcont₁ := continuousOn_affineSegIntegrand_Icc a (c - b) b (1 - z) (-z) hr₁ h1AA'
    fun u hu => by
      rw [show (1 - z) - (-z) * (u : ℂ) = 1 - z * ((1 - u : ℝ) : ℂ) by push_cast; ring]
      exact one_sub_mul_ofReal_mem_slitPlane hz
        ⟨sub_nonneg.mpr (hu.2.trans h1AA'.le), sub_le_self _ (hr₁.le.trans hu.1)⟩
  have hsplit₀ : (∫ u : ℝ in r₀..A', affineSegIntegrand a b (c - b) 1 z u) =
      (∫ u : ℝ in r₀..A, affineSegIntegrand a b (c - b) 1 z u) +
        ∫ u : ℝ in A..A', affineSegIntegrand a b (c - b) 1 z u :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hcont₀.mono (by
        rw [uIcc_of_le hr₀A.le]
        exact Icc_subset_Icc_right (le_max_left A A'))).intervalIntegrable (μ := volume))
      ((hcont₀.mono (by
        rw [uIcc]
        exact Icc_subset_Icc (le_min hr₀A.le hr₀A'.le) le_rfl)).intervalIntegrable
          (μ := volume))).symm
  have hsplit₁ : (∫ u : ℝ in r₁..(1 - A'), affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
      (∫ u : ℝ in r₁..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u) -
        ∫ u : ℝ in A..A', affineSegIntegrand a b (c - b) 1 z u := by
    have hadj := (intervalIntegral.integral_add_adjacent_intervals
      ((hcont₁.mono (by
        rw [uIcc_of_le hr₁A.le]
        exact Icc_subset_Icc_right (le_max_left _ _))).intervalIntegrable (μ := volume))
      ((hcont₁.mono (by
        rw [uIcc]
        exact Icc_subset_Icc (le_min hr₁A.le hr₁A'.le) le_rfl)).intervalIntegrable
          (μ := volume))).symm
    rw [hadj]
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A') (b := A)
    have hcov : (∫ u : ℝ in (1 - A)..(1 - A'), affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
        -∫ t : ℝ in A..A', affineSegIntegrand a b (c - b) 1 z t := by
      rw [← hsub, intervalIntegral.integral_symm A A']
      congr 1
      exact intervalIntegral.integral_congr fun t _ => affineSegIntegrand_one_sub a b c z t
    rw [hcov]; ring
  simp only [affineLoopZero, hsplit₀, hsplit₁]
  ring

/-- **Independence of the basepoint and radii for Pochhammer's contour.** For all complex
parameters `a, b, c`, any basepoints `A, A'` and admissible loop radii `(ρ₀, ρ₁)`, `(ρ₀', ρ₁')`,
`Complex.hypergeometricPochhammerLoop` takes the same value. -/
theorem hypergeometricPochhammerLoop_eq (a b c z : ℂ) {A A' ρ₀ ρ₀' ρ₁ ρ₁' : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hρ₀' : 0 < ρ₀') (hρ₀'A : ρ₀' < A') (hρ₁' : 0 < ρ₁') (hρ₁'A : ρ₁' < 1 - A')
    (hz₀ : ‖z‖ * ρ₀ < 1) (hz₀' : ‖z‖ * ρ₀' < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane)
    (hz₁' : closedBall (1 - z) (‖z‖ * ρ₁') ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      hypergeometricPochhammerLoop a b c z A' ρ₀' ρ₁' := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  set r₀ := min ρ₀ ρ₀' / 2
  set r₁ := min ρ₁ ρ₁' / 2
  have hr₀ : 0 < r₀ := half_pos (lt_min hρ₀ hρ₀')
  have hr₁ : 0 < r₁ := half_pos (lt_min hρ₁ hρ₁')
  have hr₀_le : r₀ ≤ ρ₀ := (half_lt_self (lt_min hρ₀ hρ₀')).le.trans (min_le_left _ _)
  have hr₁_le : r₁ ≤ ρ₁ := (half_lt_self (lt_min hρ₁ hρ₁')).le.trans (min_le_left _ _)
  have hr₀A : r₀ < A := hr₀_le.trans_lt hρ₀A
  have hr₀A' : r₀ < A' :=
    ((half_lt_self (lt_min hρ₀ hρ₀')).le.trans (min_le_right _ _)).trans_lt hρ₀'A
  have hr₁A : r₁ < 1 - A := hr₁_le.trans_lt hρ₁A
  have hr₁A' : r₁ < 1 - A' :=
    ((half_lt_self (lt_min hρ₁ hρ₁')).le.trans (min_le_right _ _)).trans_lt hρ₁'A
  have hzr₀ : ‖z‖ * r₀ < 1 := (mul_le_mul_of_nonneg_left hr₀_le (norm_nonneg z)).trans_lt hz₀
  have hzr₁ : closedBall (1 - z) (‖z‖ * r₁) ⊆ slitPlane :=
    Subset.trans (closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hr₁_le (norm_nonneg z)))
      hz₁
  rw [pochhammer_change_radii a b c z hρ₀ hρ₀A hr₀ hr₀A hρ₁ hρ₁A hr₁ hr₁A hz₀ hzr₀ hz₁ hzr₁,
    pochhammer_change_radii a b c z hρ₀' hρ₀'A hr₀ hr₀A' hρ₁' hρ₁'A hr₁ hr₁A' hz₀' hzr₀ hz₁' hzr₁]
  exact pochhammer_change_basepoint a b c z hz hr₀ hr₀A hr₀A' hr₁ hr₁A hr₁A'

/-- **Joint holomorphy of Pochhammer's contour integral.** For fixed admissible `A, ρ₀, ρ₁`,
`Complex.hypergeometricPochhammerLoop` is jointly analytic in all four variables `(a, b, c, z)` on
`{p | ‖p.2.2.2‖ * ρ₀ < 1 ∧ closedBall (1 - p.2.2.2) (‖p.2.2.2‖ * ρ₁) ⊆ slitPlane}`. -/
theorem analyticOnNhd_hypergeometricPochhammerLoop {A ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ × ℂ =>
        hypergeometricPochhammerLoop p.1 p.2.1 p.2.2.1 p.2.2.2 A ρ₀ ρ₁)
      {p | ‖p.2.2.2‖ * ρ₀ < 1 ∧ closedBall (1 - p.2.2.2) (‖p.2.2.2‖ * ρ₁) ⊆ slitPlane} := by
  intro p hp
  have hz : 1 - p.2.2.2 ∈ slitPlane := hp.2 (mem_closedBall_self (by positivity))
  have hA1 : A < 1 := by linarith
  have h1A1 : 1 - A < 1 := by linarith
  have ha : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.1) p := analyticAt_fst
  have hb : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have hc : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have hz_an : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.2) p :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  have hcb : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.1 - q.2.1) p := hc.fun_sub hb
  have hw₀ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => 1 - q.2.2.2) p := analyticAt_const.fun_sub hz_an
  have hw₁ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => -q.2.2.2) p := hz_an.fun_neg
  have hslit₀ : ∀ u ∈ Icc ρ₀ A, (1 : ℂ) - p.2.2.2 * (u : ℂ) ∈ slitPlane := fun u hu =>
    one_sub_mul_ofReal_mem_slitPlane hz ⟨hρ₀.le.trans hu.1, hu.2.trans hA1.le⟩
  have hslit₁ : ∀ u ∈ Icc ρ₁ (1 - A), (1 - p.2.2.2) - (-p.2.2.2) * (u : ℂ) ∈ slitPlane :=
    fun u hu => by
      rw [show (1 - p.2.2.2) - (-p.2.2.2) * (u : ℂ) = 1 - p.2.2.2 * ((1 - u : ℝ) : ℂ) by
        push_cast; ring]
      exact one_sub_mul_ofReal_mem_slitPlane hz
        ⟨sub_nonneg.mpr (hu.2.trans h1A1.le), sub_le_self _ (hρ₁.le.trans hu.1)⟩
  have haff₀ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      affineLoopZero q.1 q.2.1 (q.2.2.1 - q.2.1) 1 q.2.2.2 A ρ₀) p :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      exp (2 * π * I * (q.2.1 - 1)) - 1) p).fun_mul
      (analyticAt_integral_affineSegIntegrand_compact (fw₀ := fun _ => 1) ha hb hcb
        analyticAt_const hz_an hρ₀ hρ₀A.le hA1 hslit₀)).fun_add
      (analyticAt_integral_affineCircIntegrand (fw₀ := fun _ => 1) ha hb hcb analyticAt_const
        hz_an hρ₀ (hρ₀A.trans hA1) (closedBall_one_subset_slitPlane_iff.mpr hp.1))
  have haff₁ : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      affineLoopZero q.1 (q.2.2.1 - q.2.1) q.2.1 (1 - q.2.2.2) (-q.2.2.2) (1 - A) ρ₁) p :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      exp (2 * π * I * (q.2.2.1 - q.2.1 - 1)) - 1) p).fun_mul
      (analyticAt_integral_affineSegIntegrand_compact ha hcb hb hw₀ hw₁ hρ₁ hρ₁A.le h1A1
        hslit₁)).fun_add
      (analyticAt_integral_affineCircIntegrand ha hcb hb hw₀ hw₁ hρ₁ (hρ₁A.trans h1A1)
        (by simpa only [norm_neg] using hp.2))
  have htot :=
    ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      1 - exp (2 * π * I * (q.2.2.1 - q.2.1 - 1))) p).fun_mul haff₀).fun_add
      ((by fun_prop : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
        1 - exp (2 * π * I * (q.2.1 - 1))) p).fun_mul haff₁)
  have hopen : IsOpen {q : ℂ × ℂ × ℂ × ℂ | 1 - q.2.2.2 ∈ slitPlane} :=
    Complex.isOpen_slitPlane.preimage
      (continuous_const.sub (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  refine htot.congr ?_
  filter_upwards [hopen.mem_nhds hz] with q hq
  exact (hypergeometricPochhammerLoop_eq_affineLoopZero q.1 q.2.1 q.2.2.1 q.2.2.2 hρ₀ hρ₀A hρ₁
    hρ₁A hq).symm

/-- **Collapsing Pochhammer's contour onto `[0, 1]`.** When `0 < re b < re c` and `(A, ρ₀, ρ₁)` is
admissible (`0 < ρ₀ < A`, `0 < ρ₁ < 1 - A`, `‖z‖ * ρ₀ < 1`, and
`Metric.closedBall (1 - z) (‖z‖ * ρ₁) ⊆ Complex.slitPlane`), Pochhammer's double-loop integral
equals `-(1 - e^{2πi b}) (1 - e^{2πi (c - b)})` times the unnormalized Euler integral over
`[0, 1]`. -/
theorem hypergeometricPochhammerLoop_eq_integral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁)
    (hρ₁A : ρ₁ < 1 - A) (hz₀ : ‖z‖ * ρ₀ < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      -(1 - exp (2 * π * I * b)) * (1 - exp (2 * π * I * (c - b))) *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z * t) ^ (-a) := by
  have hz : 1 - z ∈ slitPlane := hz₁ (mem_closedBall_self (by positivity))
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hA0 : 0 < A := hρ₀.trans hρ₀A
  have hA1 : A < 1 := by linarith
  have hint_full : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume 0 1 :=
    intervalIntegrable_eulerIntegrand a hb hbc hz
  have hint₀ : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume 0 A :=
    hint_full.mono_set (by
      rw [uIcc_of_le hA0.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_right hA1.le)
  have hint₁ :
      IntervalIntegrable (affineSegIntegrand a (c - b) b (1 - z) (-z)) volume 0 (1 - A) := by
    refine ((betaIntegral_convergent hcb hb).mul_continuousOn ?_).mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right (by linarith))
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_of_forall_continuousAt fun u hu =>
      ContinuousAt.cpow (by fun_prop) continuousAt_const (by
        rw [show (1 - z) - (-z) * (u : ℂ) = 1 - z * ((1 - u : ℝ) : ℂ) by push_cast; ring]
        exact one_sub_mul_ofReal_mem_slitPlane hz ⟨sub_nonneg.mpr hu.2, sub_le_self _ hu.1⟩)
  rw [hypergeometricPochhammerLoop_eq_affineLoopZero a b c z hρ₀ hρ₀A hρ₁ hρ₁A hz,
    affineLoopZero_eq_integral a b (c - b) 1 z hb hρ₀ (hρ₀A.trans hA1) hρ₀A.le
      (closedBall_one_subset_slitPlane_iff.mpr hz₀) hint₀,
    affineLoopZero_eq_integral a (c - b) b (1 - z) (-z) hcb hρ₁ (hρ₁A.trans (by linarith))
      hρ₁A.le (by simpa only [norm_neg] using hz₁) hint₁]
  have hcov : (∫ u : ℝ in 0..(1 - A), affineSegIntegrand a (c - b) b (1 - z) (-z) u) =
      ∫ t : ℝ in A..1, affineSegIntegrand a b (c - b) 1 z t := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (affineSegIntegrand a (c - b) b (1 - z) (-z)) (1 : ℝ) (a := A) (b := 1)
    rw [sub_self] at hsub
    rw [← hsub]
    exact intervalIntegral.integral_congr fun t _ => affineSegIntegrand_one_sub a b c z t
  have hadj : (∫ t : ℝ in 0..A, affineSegIntegrand a b (c - b) 1 z t) +
      (∫ t : ℝ in A..1, affineSegIntegrand a b (c - b) 1 z t) =
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
    have h2 : IntervalIntegrable (affineSegIntegrand a b (c - b) 1 z) volume A 1 :=
      hint_full.mono_set (by
        rw [uIcc_of_le hA1.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc_left hA0.le)
    exact intervalIntegral.integral_add_adjacent_intervals hint₀ h2
  have hexp_b : exp (2 * π * I * (b - 1)) = exp (2 * π * I * b) := by
    simpa [sub_eq_add_neg] using exp_two_pi_mul_I_mul_add_intCast b (-1)
  have hexp_cb : exp (2 * π * I * (c - b - 1)) = exp (2 * π * I * (c - b)) := by
    simpa [sub_eq_add_neg] using exp_two_pi_mul_I_mul_add_intCast (c - b) (-1)
  rw [hcov, hexp_b, hexp_cb]
  linear_combination -(1 - exp (2 * π * I * b)) * (1 - exp (2 * π * I * (c - b))) * hadj

/-- When `0 < re b < re c` and `(A, ρ₀, ρ₁)` is admissible (`0 < ρ₀ < A`, `0 < ρ₁ < 1 - A`,
`‖z‖ * ρ₀ < 1`, and `Metric.closedBall (1 - z) (‖z‖ * ρ₁) ⊆ Complex.slitPlane`), Pochhammer's
contour integral is `(4π² e^{cπi} / (Γ(1 - b) Γ(1 + b - c)))` times `Complex.eulerIntegral`,
including when `b` or `c - b` is a positive integer where both sides vanish. -/
theorem hypergeometricPochhammerLoop_eq_eulerIntegral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁)
    (hρ₁A : ρ₁ < 1 - A) (hz₀ : ‖z‖ * ρ₀ < 1)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c)) *
        eulerIntegral a b c z := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hrefl_b := Gamma_mul_sin_pi_mul (ne_neg_natCast_of_re_pos hb)
  have hrefl_cb := Gamma_mul_sin_pi_mul (ne_neg_natCast_of_re_pos hcb)
  have h1cb : 1 - (c - b) = 1 + b - c := by ring
  rw [h1cb] at hrefl_cb
  have h1sub (x : ℂ) : 1 - exp (2 * π * I * x) = -2 * I * exp (x * π * I) * sin (π * x) := by
    have h := one_sub_exp_mul_I (2 * π * x)
    rw [show I * (2 * π * x) = 2 * π * I * x by ring,
      show 2 * π * I * x / 2 = x * π * I by ring,
      show 2 * π * x / 2 = π * x by ring] at h
    exact h
  have hexpc : exp (b * π * I) * exp ((c - b) * π * I) = exp (c * π * I) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hypergeometricPochhammerLoop_eq_integral a hb hbc hρ₀ hρ₀A hρ₁ hρ₁A hz₀ hz₁,
    h1sub b, h1sub (c - b), eulerIntegral_def]
  set E := ∫ t : ℝ in 0..1,
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)
  have hE : E = Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E) := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hGb hGcb), one_mul]
  conv_lhs => rw [hE]
  calc -(-2 * I * exp (b * π * I) * sin (π * b)) *
        (-2 * I * exp ((c - b) * π * I) * sin (π * (c - b))) *
        (Gamma b * Gamma (c - b) * ((Gamma b * Gamma (c - b))⁻¹ * E))
      = -(4 * I ^ 2) * (exp (b * π * I) * exp ((c - b) * π * I)) *
          (Gamma b * sin (π * b)) * (Gamma (c - b) * sin (π * (c - b))) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by ring
    _ = 4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c)) *
          ((Gamma b * Gamma (c - b))⁻¹ * E) := by
          rw [I_sq, hexpc, hrefl_b, hrefl_cb]
          ring

/-- **DLMF 15.6.5 in the Euler convergence region.** For `0 < re b < re c`,
`b, c - b ∉ {1, 2, …}`, and admissible `(A, ρ₀, ρ₁)` (`0 < ρ₀ < A`, `0 < ρ₁ < 1 - A`,
`‖z‖ * ρ₀ < 1`, and `Metric.closedBall (1 - z) (‖z‖ * ρ₁) ⊆ Complex.slitPlane`),
`Complex.eulerIntegral` is represented on the cut plane by Pochhammer's double-loop contour
integral. -/
theorem eulerIntegral_eq_hypergeometricPochhammerLoop (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hcb_int : ∀ n : ℕ, c - b ≠ n + 1)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hz₀ : ‖z‖ * ρ₀ < 1) (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    eulerIntegral a b c z =
      exp (-c * π * I) * Gamma (1 - b) * Gamma (1 + b - c) / (4 * π ^ 2) *
        hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ := by
  have hG1b : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun n hn => hb_int n (by linear_combination -hn)
  have hG1cb : Gamma (1 + b - c) ≠ 0 :=
    Gamma_ne_zero fun n hn => hcb_int n (by linear_combination -hn)
  have hexp : exp (-(c * π * I)) * exp (c * π * I) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  rw [hypergeometricPochhammerLoop_eq_eulerIntegral a hb hbc hρ₀ hρ₀A hρ₁ hρ₁A hz₀ hz₁]
  field_simp
  linear_combination (eulerIntegral a b c z) * hexp.symm

/-- **Pochhammer's contour integral for Euler's Beta function (DLMF 5.12.12).** At zero argument,
`Complex.hypergeometricPochhammerLoop` evaluates in closed form for all complex `a`, `b`, and `c`
with no real-part restrictions whenever `0 < ρ₀ < A` and `0 < ρ₁ < 1 - A`. -/
@[simp]
theorem hypergeometricPochhammerLoop_zero (a b c : ℂ) {A ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    hypergeometricPochhammerLoop a b c 0 A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c) * Gamma c) := by
  have h0 : ‖(0 : ℂ)‖ * ρ₀ < 1 ∧ closedBall (1 - (0 : ℂ)) (‖(0 : ℂ)‖ * ρ₁) ⊆ slitPlane := by
    simp [one_mem_slitPlane]
  have han₁ : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => hypergeometricPochhammerLoop a p.1 p.2 0 A ρ₀ ρ₁) univ := fun p _ =>
    (analyticOnNhd_hypergeometricPochhammerLoop hρ₀ hρ₀A hρ₁ hρ₁A (a, p.1, p.2, 0) h0).comp₂
      analyticAt_const (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const))
  have hG (s : ℂ) : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s :=
    Complex.differentiable_one_div_Gamma.analyticAt s
  have han₂ : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => 4 * π ^ 2 * exp (p.2 * π * I) /
        (Gamma (1 - p.1) * Gamma (1 + p.1 - p.2) * Gamma p.2)) univ := fun p _ => by
    simp_rw [div_eq_mul_inv, mul_inv]
    exact (analyticAt_const.mul ((analyticAt_snd.mul analyticAt_const).mul
      analyticAt_const).cexp).mul
      ((((hG _).comp (analyticAt_const.sub analyticAt_fst)).mul
        ((hG _).comp ((analyticAt_const.add analyticAt_fst).sub analyticAt_snd))).mul
        ((hG _).comp analyticAt_snd))
  have hU : IsOpen {p : ℂ × ℂ | 0 < p.1.re ∧ p.1.re < p.2.re} :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt (Complex.continuous_re.comp continuous_fst)
        (Complex.continuous_re.comp continuous_snd))
  have heq := han₁.eq_of_eventuallyEq han₂ (z₀ := (1, 2)) ?_
  · exact congrFun heq (b, c)
  · filter_upwards [hU.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re ∧ (1 : ℂ).re < (2 : ℂ).re)]
      with p hp
    rw [hypergeometricPochhammerLoop_eq_eulerIntegral a hp.1 hp.2 hρ₀ hρ₀A hρ₁ hρ₁A h0.1 h0.2,
      eulerIntegral_zero a hp.1 hp.2, ← div_eq_mul_inv, div_div]

/-- With first parameter zero, Pochhammer's contour integral is independent of `z` and evaluates in
closed form for all complex `b`, `c`, and `z` whenever `0 < ρ₀ < A` and `0 < ρ₁ < 1 - A`. -/
@[simp]
theorem hypergeometricPochhammerLoop_zero_left (b c z : ℂ) {A ρ₀ ρ₁ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A) :
    hypergeometricPochhammerLoop 0 b c z A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c) * Gamma c) := by
  have heq : hypergeometricPochhammerLoop 0 b c z A ρ₀ ρ₁ =
      hypergeometricPochhammerLoop 0 b c 0 A ρ₀ ρ₁ := by
    simp only [hypergeometricPochhammerLoop_def, neg_zero, cpow_zero]
  rw [heq, hypergeometricPochhammerLoop_zero 0 b c hρ₀ hρ₀A hρ₁ hρ₁A]

end Complex
