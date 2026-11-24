/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Basic

import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Metric

/-!
# The first integral of a minimal revolution profile

The minimal-profile ODE in an arbitrary regular parameter has the first integral
`f g' / sqrt (f'² + g'²)`. Its vanishing gives a horizontal planar profile; its nonzero
value gives the neck radius of the catenoid. No arclength or height parametrization is assumed.
-/

public noncomputable section

open Set
open scoped ContDiff

namespace TauCeti.SurfaceOfRevolution

/-- The signed vertical flux per unit angular parameter of a regular revolution profile. -/
def profileFlux (f g : ℝ → ℝ) (v : ℝ) : ℝ :=
  f v * deriv g v / Real.sqrt (profileSpeedSq f g v)

/-- The coordinate formula for the vertical profile flux. -/
theorem profileFlux_def (f g : ℝ → ℝ) (v : ℝ) :
    profileFlux f g v = f v * deriv g v / Real.sqrt (profileSpeedSq f g v) := (rfl)

/-- The vertical flux is constant to first order at a regular minimal-profile point. -/
theorem hasDerivAt_profileFlux_eq_zero {f g : ℝ → ℝ} {v : ℝ}
    (hf : ContDiffAt ℝ 2 f v) (hg : ContDiffAt ℝ 2 g v)
    (hs : 0 < profileSpeedSq f g v)
    (heq : deriv g v * profileSpeedSq f g v +
      f v * (deriv f v * deriv (deriv g) v - deriv g v * deriv (deriv f) v) = 0) :
    HasDerivAt (profileFlux f g) 0 v := by
  have hf' := (hf.differentiableAt (by norm_num)).hasDerivAt
  have hff := ((hf.derivWithin (by norm_num : 1 + 1 ≤ (2 : ℕ∞ω))).differentiableAt
    (by norm_num)).hasDerivAt
  have hgg := ((hg.derivWithin (by norm_num : 1 + 1 ≤ (2 : ℕ∞ω))).differentiableAt
    (by norm_num)).hasDerivAt
  have hroot := (hasDerivAt_profileSpeedSq hff.differentiableAt
    hgg.differentiableAt).sqrt (ne_of_gt hs)
  have hd := (hf'.mul hgg).div hroot (ne_of_gt (Real.sqrt_pos.mpr hs))
  convert hd using 1
  · rfl
  · symm
    apply (div_eq_zero_iff).mpr
    left
    field_simp
    have hsq := Real.sq_sqrt hs.le
    simp only [Pi.mul_apply, profileSpeedSq_def] at *
    linear_combination
      (deriv f v * deriv g v + f v * deriv (deriv g) v) * hsq + deriv f v * heq

/-- The vertical flux is constant on a preconnected set of regular minimal-profile parameters. -/
theorem profileFlux_eq {f g : ℝ → ℝ} {s : Set ℝ}
    (hc : IsPreconnected s)
    (hf : ∀ v ∈ s, ContDiffAt ℝ 2 f v) (hg : ∀ v ∈ s, ContDiffAt ℝ 2 g v)
    (hreg : ∀ v ∈ s, 0 < profileSpeedSq f g v)
    (heq : ∀ v ∈ s, deriv g v * profileSpeedSq f g v +
      f v * (deriv f v * deriv (deriv g) v - deriv g v * deriv (deriv f) v) = 0)
    {v w : ℝ} (hv : v ∈ s) (hw : w ∈ s) : profileFlux f g v = profileFlux f g w := by
  have hd (v : ℝ) (hv : v ∈ s) :=
    hasDerivAt_profileFlux_eq_zero (hf v hv) (hg v hv) (hreg v hv) (heq v hv)
  exact hc.eq_of_hasDerivWithinAt_zero (fun t ht ↦ (hd t ht).hasDerivWithinAt) hv hw

private theorem sqrt_one_add_sq_deriv_div {f g : ℝ → ℝ} {v : ℝ}
    (hgne : deriv g v ≠ 0) :
    Real.sqrt (1 + (deriv f v / deriv g v) ^ 2) =
      Real.sqrt (profileSpeedSq f g v) / |deriv g v| := by
  have hs : 0 ≤ profileSpeedSq f g v := by
    rw [profileSpeedSq_def]
    positivity
  have hratio : 1 + (deriv f v / deriv g v) ^ 2 =
      profileSpeedSq f g v / deriv g v ^ 2 := by
    rw [profileSpeedSq_def]
    field_simp
    ring
  rw [hratio, Real.sqrt_div hs, Real.sqrt_sq_eq_abs]

/-- The centre height determined by a nonzero vertical flux has derivative zero. -/
private theorem hasDerivAt_profileCenter_eq_zero {f g : ℝ → ℝ} {v a : ℝ}
    (hf : ContDiffAt ℝ 2 f v) (hg : ContDiffAt ℝ 2 g v)
    (hr : 0 < f v) (hgne : deriv g v ≠ 0)
    (ha : a = |profileFlux f g v|)
    (heq : deriv g v * profileSpeedSq f g v +
      f v * (deriv f v * deriv (deriv g) v - deriv g v * deriv (deriv f) v) = 0) :
    HasDerivAt (fun t ↦ g t - a * Real.arsinh (deriv f t / deriv g t)) 0 v := by
  have hs : 0 < profileSpeedSq f g v := by
    rw [profileSpeedSq_def]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hgne)
  have hrootpos := Real.sqrt_pos.mpr hs
  have ha' : a = f v * |deriv g v| / Real.sqrt (profileSpeedSq f g v) := by
    rw [ha, profileFlux_def, abs_div, abs_mul, abs_of_pos hr, abs_of_pos hrootpos]
  have hg' := (hg.differentiableAt (by norm_num)).hasDerivAt
  have hff := ((hf.derivWithin (by norm_num : 1 + 1 ≤ (2 : ℕ∞ω))).differentiableAt
    (by norm_num)).hasDerivAt
  have hgg := ((hg.derivWithin (by norm_num : 1 + 1 ≤ (2 : ℕ∞ω))).differentiableAt
    (by norm_num)).hasDerivAt
  have hd := hg'.sub (((hff.div hgg hgne).arsinh).const_mul a)
  convert hd using 1
  symm
  simp only [smul_eq_mul, Pi.div_apply]
  rw [sqrt_one_add_sq_deriv_div hgne, ha']
  field_simp
  rw [sq_abs, Real.sq_sqrt hs.le]
  linear_combination deriv g v ^ 2 * heq

/-- A positive-radius regular profile that satisfies the minimality ODE on a preconnected
set has constant height or satisfies the catenoid profile equation. -/
theorem profile_plane_or_catenoid {f g : ℝ → ℝ} {s : Set ℝ}
    (hc : IsPreconnected s)
    (hf : ∀ v ∈ s, ContDiffAt ℝ 2 f v) (hg : ∀ v ∈ s, ContDiffAt ℝ 2 g v)
    (hr : ∀ v ∈ s, 0 < f v) (hreg : ∀ v ∈ s, 0 < profileSpeedSq f g v)
    (heq : ∀ v ∈ s, deriv g v * profileSpeedSq f g v +
      f v * (deriv f v * deriv (deriv g) v - deriv g v * deriv (deriv f) v) = 0) :
    (∃ b : ℝ, ∀ v ∈ s, g v = b) ∨
      ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ v ∈ s, f v = a * Real.cosh ((g v - b) / a) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · exact Or.inl ⟨0, by simp⟩
  have hflux (w : ℝ) (hw : w ∈ s) : profileFlux f g w = profileFlux f g v :=
    profileFlux_eq hc hf hg hreg heq hw hv
  by_cases hz : profileFlux f g v = 0
  · left
    refine ⟨g v, fun w hw ↦ ?_⟩
    apply hc.eq_of_hasDerivWithinAt_zero ?_ hw hv
    intro t ht
    have hzero := hflux t ht
    rw [hz, profileFlux_def] at hzero
    have hderiv : deriv g t = 0 := (mul_eq_zero.mp ((div_eq_zero_iff.mp hzero).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (hreg t ht))))).resolve_left (ne_of_gt (hr t ht))
    rw [← hderiv]
    exact ((hg t ht).differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt
  · right
    let a := |profileFlux f g v|
    have ha : 0 < a := abs_pos.mpr hz
    have hgne (w : ℝ) (hw : w ∈ s) : deriv g w ≠ 0 := by
      intro hzero
      apply hz
      rw [← hflux w hw, profileFlux_def, hzero, mul_zero, zero_div]
    have hcenter (w : ℝ) (hw : w ∈ s) :
        HasDerivAt (fun t ↦ g t - a * Real.arsinh (deriv f t / deriv g t)) 0 w :=
      hasDerivAt_profileCenter_eq_zero (hf w hw) (hg w hw) (hr w hw) (hgne w hw)
        (by simp only [a, hflux w hw]) (heq w hw)
    refine ⟨a, ha, g v - a * Real.arsinh (deriv f v / deriv g v), fun w hw ↦ ?_⟩
    have hb := hc.eq_of_hasDerivWithinAt_zero (fun t ht ↦ (hcenter t ht).hasDerivWithinAt) hw hv
    have harg : (g w - (g v - a * Real.arsinh (deriv f v / deriv g v))) / a =
        Real.arsinh (deriv f w / deriv g w) := by
      apply (div_eq_iff (ne_of_gt ha)).mpr
      linarith
    have ha' : a = f w * |deriv g w| / Real.sqrt (profileSpeedSq f g w) := by
      rw [show a = |profileFlux f g w| from congrArg abs (hflux w hw).symm,
        profileFlux_def, abs_div, abs_mul, abs_of_pos (hr w hw),
        abs_of_pos (Real.sqrt_pos.mpr (hreg w hw))]
    rw [harg, Real.cosh_arsinh, sqrt_one_add_sq_deriv_div (hgne w hw), ha']
    field_simp [abs_ne_zero.mpr (hgne w hw),
      ne_of_gt (Real.sqrt_pos.mpr (hreg w hw))]

end TauCeti.SurfaceOfRevolution
