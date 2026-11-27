/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.HalfAngle

/-!
# The Goemans–Williamson constant

The Goemans–Williamson constant `gwConstant` is the infimum of `(2 / π) · θ / (1 - cos θ)` over
`0 < θ ≤ π`. Rounding a solution of the semidefinite relaxation of Max-Cut by a random hyperplane
separates two unit vectors at angle `θ` with probability `θ / π`, while the relaxation counts
their pair with weight `(1 - cos θ) / 2`. The constant `gwConstant` is the worst ratio of the two,
and it is the factor in Goemans and Williamson's bound for the expected weight of the rounded cut
in terms of the value of the relaxation.

The derivative of `θ / (1 - cos θ)` has the sign of `1 - cos θ - θ sin θ`, whose derivative is
`-θ cos θ`. That numerator is negative on `(0, π / 2]`, increasing on `[π / 2, π]` and positive
at `π`, so it vanishes at exactly one point `gwAngle` of `(0, π]`, which lies in `(π / 2, π)`;
there `1 - cos θ - θ sin θ = 2 sin (θ / 2) (sin (θ / 2) - θ cos (θ / 2))`, so `gwAngle` is the
solution of `tan (θ / 2) = θ`. The ratio decreases before `gwAngle` and increases after it.

## Main declarations

* `TauCeti.gwConstant`, `TauCeti.gwAngle`: the constant and the angle `θ₀ = 2.33112…` at which
  it is attained.
* `TauCeti.gwConstant_eq`, `TauCeti.gwConstant_eq_iff`: the infimum is attained at `gwAngle` and
  nowhere else on `(0, π]`.
* `TauCeti.tan_div_two_eq_iff_eq_gwAngle`: `gwAngle` is the only solution of `tan (θ / 2) = θ`
  in `(0, π)`.
* `TauCeti.gwConstant_eq_one_add_sq_div`: the closed form `gwConstant = (1 + θ₀²) / (π θ₀)`.
* `TauCeti.gwConstant_mem_Ioo`: `0.878 < gwConstant < 0.879`.
* `TauCeti.gwConstant_mul_le_arccos`: `gwConstant · (1 - t) / 2 ≤ arccos t / π` for `-1 ≤ t`,
  with equality exactly at `t = 1` and `t = cos gwAngle` (`TauCeti.gwConstant_mul_eq_arccos_iff`).

## References

* M. X. Goemans and D. P. Williamson, *Improved approximation algorithms for maximum cut and
  satisfiability problems using semidefinite programming*, J. ACM **42** (1995), 1115–1145.
* D. P. Williamson and D. B. Shmoys, *The design of approximation algorithms*, Cambridge
  University Press, 2011, Lemma 6.8.
-/

public section

open Real Set

namespace TauCeti

/-- The **Goemans–Williamson constant**: the infimum of `(2 / π) · θ / (1 - cos θ)` over
`0 < θ ≤ π`. It is the ratio in the Goemans–Williamson guarantee for hyperplane rounding of the
semidefinite relaxation of Max-Cut. -/
noncomputable def gwConstant : ℝ :=
  sInf ((fun θ ↦ 2 / π * (θ / (1 - cos θ))) '' Ioc 0 π)

/-! ### The sign of `1 - cos θ - θ sin θ` -/

/-- The numerator `1 - cos θ - θ sin θ` of the derivative of `θ / (1 - cos θ)`. -/
private noncomputable def numer (θ : ℝ) : ℝ := 1 - cos θ - θ * sin θ

private lemma hasDerivAt_numer (θ : ℝ) : HasDerivAt numer (-(θ * cos θ)) θ := by
  unfold numer
  convert ((hasDerivAt_cos θ).const_sub 1).sub ((hasDerivAt_id' θ).mul (hasDerivAt_sin θ))
    using 1
  ring

private lemma continuous_numer : Continuous numer := by
  unfold numer; fun_prop

private lemma strictMonoOn_numer : StrictMonoOn numer (Icc (π / 2) π) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_numer.continuousOn fun x hx ↦ ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_numer x).deriv]
  have := cos_neg_of_pi_div_two_lt_of_lt hx.1 (by linarith [hx.2, pi_pos])
  nlinarith [hx.1, pi_pos]

private lemma strictAntiOn_numer : StrictAntiOn numer (Icc 0 (π / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_numer.continuousOn fun x hx ↦ ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_numer x).deriv]
  have := cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], hx.2⟩
  nlinarith [hx.1]

private lemma numer_neg_of_le_pi_div_two {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ ≤ π / 2) : numer θ < 0 := by
  have := strictAntiOn_numer ⟨le_rfl, by linarith [pi_pos]⟩ ⟨h₀.le, h₁⟩ h₀
  simpa [numer] using this

private lemma exists_numer_eq_zero : ∃ θ ∈ Ioo (π / 2) π, numer θ = 0 := by
  have h₁ : numer (π / 2) < 0 := numer_neg_of_le_pi_div_two (by linarith [pi_pos]) le_rfl
  have h₂ : 0 < numer π := by simp [numer]
  exact intermediate_value_Ioo (by linarith [pi_pos]) continuous_numer.continuousOn ⟨h₁, h₂⟩

/-- The angle at which the Goemans–Williamson ratio `θ / (1 - cos θ)` is smallest on `(0, π]`:
the unique solution of `tan (θ / 2) = θ` in `(0, π)`, see `TauCeti.tan_div_two_eq_iff_eq_gwAngle`.
Numerically `gwAngle = 2.33112…`. -/
noncomputable def gwAngle : ℝ := exists_numer_eq_zero.choose

/-- The Goemans–Williamson angle lies in `(π / 2, π)`. -/
theorem gwAngle_mem_Ioo : gwAngle ∈ Ioo (π / 2) π := exists_numer_eq_zero.choose_spec.1

private lemma numer_gwAngle : numer gwAngle = 0 := exists_numer_eq_zero.choose_spec.2

private lemma gwAngle_pos : 0 < gwAngle := by linarith [gwAngle_mem_Ioo.1, pi_pos]

private lemma numer_neg {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ < gwAngle) : numer θ < 0 := by
  rcases le_or_gt θ (π / 2) with h | h
  · exact numer_neg_of_le_pi_div_two h₀ h
  · rw [← numer_gwAngle]
    exact strictMonoOn_numer ⟨h.le, by linarith [gwAngle_mem_Ioo.2]⟩
      ⟨gwAngle_mem_Ioo.1.le, gwAngle_mem_Ioo.2.le⟩ h₁

private lemma numer_pos {θ : ℝ} (h₀ : gwAngle < θ) (h₁ : θ ≤ π) : 0 < numer θ := by
  rw [← numer_gwAngle]
  exact strictMonoOn_numer ⟨gwAngle_mem_Ioo.1.le, gwAngle_mem_Ioo.2.le⟩
    ⟨by linarith [gwAngle_mem_Ioo.1], h₁⟩ h₀

private lemma numer_eq_zero_iff {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ ≤ π) : numer θ = 0 ↔ θ = gwAngle := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ numer_gwAngle⟩
  rcases lt_trichotomy θ gwAngle with hlt | heq | hgt
  · exact absurd h (numer_neg h₀ hlt).ne
  · exact heq
  · exact absurd h (numer_pos hgt h₁).ne'

/-- On `(0, π)`, the equation `tan (θ / 2) = θ` has exactly one solution, `gwAngle`. -/
theorem tan_div_two_eq_iff_eq_gwAngle {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    tan (θ / 2) = θ ↔ θ = gwAngle := by
  have hs : 0 < sin (θ / 2) :=
    sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, pi_pos])
  have hc : 0 < cos (θ / 2) :=
    cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2]⟩
  have key : numer θ = 2 * sin (θ / 2) * (sin (θ / 2) - θ * cos (θ / 2)) := by
    have h2 : θ = 2 * (θ / 2) := by ring
    conv_lhs => rw [numer, h2, cos_two_mul, sin_two_mul]
    linear_combination (-2) * sin_sq_add_cos_sq (θ / 2)
  rw [← numer_eq_zero_iff hθ.1 hθ.2.le, key, tan_eq_sin_div_cos, div_eq_iff hc.ne']
  constructor
  · intro h; rw [h]; ring
  · intro h
    have := (mul_eq_zero.1 h).resolve_left (by positivity)
    linarith

/-- `gwAngle` solves `tan (θ / 2) = θ`. -/
theorem tan_gwAngle_div_two : tan (gwAngle / 2) = gwAngle :=
  (tan_div_two_eq_iff_eq_gwAngle ⟨gwAngle_pos, gwAngle_mem_Ioo.2⟩).2 rfl

/-! ### Monotonicity of the ratio -/

private lemma hasDerivAt_ratio {θ : ℝ} (h : 1 - cos θ ≠ 0) :
    HasDerivAt (fun θ ↦ θ / (1 - cos θ)) (numer θ / (1 - cos θ) ^ 2) θ := by
  convert (hasDerivAt_id' θ).div ((hasDerivAt_cos θ).const_sub 1) h using 1
  unfold numer
  ring

private lemma continuousOn_ratio : ContinuousOn (fun θ ↦ θ / (1 - cos θ)) (Ioc 0 π) :=
  continuousOn_id.div (continuous_const.sub continuous_cos).continuousOn fun θ hθ ↦
    (one_sub_cos_pos hθ.1 (by linarith [hθ.2, pi_pos])).ne'

private lemma deriv_ratio {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ ≤ π) :
    deriv (fun θ ↦ θ / (1 - cos θ)) θ = numer θ / (1 - cos θ) ^ 2 :=
  (hasDerivAt_ratio (one_sub_cos_pos h₀ (by linarith [pi_pos])).ne').deriv

private lemma strictAntiOn_ratio : StrictAntiOn (fun θ ↦ θ / (1 - cos θ)) (Ioc 0 gwAngle) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    (continuousOn_ratio.mono (Ioc_subset_Ioc_right gwAngle_mem_Ioo.2.le)) fun x hx ↦ ?_
  rw [interior_Ioc] at hx
  rw [deriv_ratio hx.1 (by linarith [hx.2, gwAngle_mem_Ioo.2])]
  exact div_neg_of_neg_of_pos (numer_neg hx.1 hx.2)
    (pow_pos (one_sub_cos_pos hx.1 (by linarith [hx.2, gwAngle_mem_Ioo.2, pi_pos])) 2)

private lemma strictMonoOn_ratio : StrictMonoOn (fun θ ↦ θ / (1 - cos θ)) (Icc gwAngle π) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuousOn_ratio.mono fun x hx ↦ ⟨gwAngle_pos.trans_le hx.1, hx.2⟩) fun x hx ↦ ?_
  rw [interior_Icc] at hx
  have h₀ : 0 < x := gwAngle_pos.trans hx.1
  rw [deriv_ratio h₀ hx.2.le]
  exact div_pos (numer_pos hx.1 hx.2.le)
    (pow_pos (one_sub_cos_pos h₀ (by linarith [hx.2, pi_pos])) 2)

private lemma ratio_gwAngle_lt {θ : ℝ} (hθ : θ ∈ Ioc 0 π) (hne : θ ≠ gwAngle) :
    gwAngle / (1 - cos gwAngle) < θ / (1 - cos θ) := by
  rcases hne.lt_or_gt with h | h
  · exact strictAntiOn_ratio ⟨hθ.1, h.le⟩ ⟨gwAngle_pos, le_rfl⟩ h
  · exact strictMonoOn_ratio ⟨le_rfl, gwAngle_mem_Ioo.2.le⟩ ⟨h.le, hθ.2⟩ h

/-! ### The constant -/

private lemma isLeast_gwAngle :
    IsLeast ((fun θ ↦ 2 / π * (θ / (1 - cos θ))) '' Ioc 0 π)
      (2 / π * (gwAngle / (1 - cos gwAngle))) := by
  refine ⟨⟨gwAngle, ⟨gwAngle_pos, gwAngle_mem_Ioo.2.le⟩, rfl⟩, ?_⟩
  rintro _ ⟨θ, hθ, rfl⟩
  rcases eq_or_ne θ gwAngle with rfl | hne
  · exact le_rfl
  · exact (mul_lt_mul_of_pos_left (ratio_gwAngle_lt hθ hne) (by positivity)).le

/-- The infimum defining `gwConstant` is attained at `gwAngle`. -/
theorem gwConstant_eq : gwConstant = 2 / π * (gwAngle / (1 - cos gwAngle)) :=
  isLeast_gwAngle.csInf_eq

/-- The Goemans–Williamson constant is the least value of `(2 / π) · θ / (1 - cos θ)` on
`(0, π]`. -/
theorem isLeast_gwConstant :
    IsLeast ((fun θ ↦ 2 / π * (θ / (1 - cos θ))) '' Ioc 0 π) gwConstant :=
  gwConstant_eq ▸ isLeast_gwAngle

/-- `gwConstant` is a lower bound of `(2 / π) · θ / (1 - cos θ)` on `(0, π]`. -/
theorem gwConstant_le {θ : ℝ} (hθ : θ ∈ Ioc 0 π) : gwConstant ≤ 2 / π * (θ / (1 - cos θ)) :=
  isLeast_gwConstant.2 ⟨θ, hθ, rfl⟩

/-- On `(0, π]` the infimum defining `gwConstant` is attained only at `gwAngle`. -/
theorem gwConstant_eq_iff {θ : ℝ} (hθ : θ ∈ Ioc 0 π) :
    gwConstant = 2 / π * (θ / (1 - cos θ)) ↔ θ = gwAngle := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ gwConstant_eq⟩
  by_contra hne
  have := mul_lt_mul_of_pos_left (ratio_gwAngle_lt hθ hne) (by positivity : 0 < 2 / π)
  rw [← gwConstant_eq, ← h] at this
  exact this.false

/-- The cosine of the Goemans–Williamson angle: `cos θ₀ = (1 - θ₀²) / (1 + θ₀²)`. -/
theorem cos_gwAngle : cos gwAngle = (1 - gwAngle ^ 2) / (1 + gwAngle ^ 2) := by
  have hne : cos gwAngle ≠ -1 := fun h ↦ (one_add_cos_pos (by linarith [gwAngle_pos, pi_pos])
    gwAngle_mem_Ioo.2).ne' (by rw [h]; ring)
  rw [cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq gwAngle hne, tan_gwAngle_div_two]

/-- The closed form `gwConstant = (1 + θ₀²) / (π θ₀)` at the Goemans–Williamson angle `θ₀`. -/
theorem gwConstant_eq_one_add_sq_div : gwConstant = (1 + gwAngle ^ 2) / (π * gwAngle) := by
  have h : 1 - cos gwAngle = 2 * gwAngle ^ 2 / (1 + gwAngle ^ 2) := by
    rw [cos_gwAngle]; field_simp; ring
  rw [gwConstant_eq, h]
  have := gwAngle_pos
  field_simp

/-! ### Numerical bounds -/

private lemma numer_lt_zero_d2 : numer 2.33 < 0 := by
  have hc : cos (2.33 : ℝ) = -cos (π - 2.33) := by rw [cos_pi_sub, neg_neg]
  have hs : sin (2.33 : ℝ) = sin (π - 2.33) := by rw [sin_pi_sub]
  have h₁ : cos (π - 2.33) ≤ cos 0.811592 :=
    cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_d6]) (by linarith [pi_gt_d6])
  have h₂ : sin 0.811592 ≤ sin (π - 2.33) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_gt_d6]) (by linarith [pi_lt_d6])
      (by linarith [pi_gt_d6])
  have h₃ := abs_le.1 (cos_bound_six (x := 0.811592) (by norm_num [abs_of_pos]))
  have h₄ := abs_le.1 (sin_bound_seven (x := 0.811592) (by norm_num [abs_of_pos]))
  norm_num [abs_of_pos] at h₃ h₄
  rw [numer, hc, hs]
  linarith

private lemma numer_pos_d3 : 0 < numer 2.332 := by
  have hc : cos (2.332 : ℝ) = -cos (π - 2.332) := by rw [cos_pi_sub, neg_neg]
  have hs : sin (2.332 : ℝ) = sin (π - 2.332) := by rw [sin_pi_sub]
  have h₁ : cos 0.809593 ≤ cos (π - 2.332) :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_gt_d6]) (by linarith [pi_gt_d6])
      (by linarith [pi_lt_d6])
  have h₂ : sin (π - 2.332) ≤ sin 0.809593 :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_gt_d6]) (by linarith [pi_gt_d6])
      (by linarith [pi_lt_d6])
  have h₃ := abs_le.1 (cos_bound_six (x := 0.809593) (by norm_num [abs_of_pos]))
  have h₄ := abs_le.1 (sin_bound_seven (x := 0.809593) (by norm_num [abs_of_pos]))
  norm_num [abs_of_pos] at h₃ h₄
  rw [numer, hc, hs]
  linarith

/-- The lower bound `2.33 < gwAngle`. -/
theorem gwAngle_gt_d2 : 2.33 < gwAngle := by
  by_contra! h
  have h₁ : π / 2 ≤ 2.33 := by linarith [pi_lt_d2]
  have := strictMonoOn_numer.le_iff_le ⟨gwAngle_mem_Ioo.1.le, gwAngle_mem_Ioo.2.le⟩
    ⟨h₁, by linarith [pi_gt_d2]⟩ |>.2 h
  rw [numer_gwAngle] at this
  linarith [numer_lt_zero_d2]

/-- The upper bound `gwAngle < 2.332`. -/
theorem gwAngle_lt_d3 : gwAngle < 2.332 := by
  by_contra! h
  have h₁ : π / 2 ≤ 2.332 := by linarith [pi_lt_d2]
  have := strictMonoOn_numer.le_iff_le ⟨h₁, by linarith [pi_gt_d2]⟩
    ⟨gwAngle_mem_Ioo.1.le, gwAngle_mem_Ioo.2.le⟩ |>.2 h
  rw [numer_gwAngle] at this
  linarith [numer_pos_d3]

/-- The numerical bounds `0.878 < gwConstant < 0.879`. -/
theorem gwConstant_mem_Ioo : gwConstant ∈ Ioo 0.878 0.879 := by
  have h₁ := gwAngle_gt_d2
  have h₂ := gwAngle_lt_d3
  have hπ₁ := pi_gt_d6
  have hπ₂ := pi_lt_d6
  rw [gwConstant_eq_one_add_sq_div]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

/-- The Goemans–Williamson constant is positive. -/
theorem gwConstant_pos : 0 < gwConstant := by
  rw [gwConstant_eq_one_add_sq_div]
  have := gwAngle_pos
  positivity

/-! ### The rounding inequality -/

/-- The Goemans–Williamson inequality `gwConstant · (1 - t) / 2 ≤ arccos t / π` for `-1 ≤ t`.
For `t ∈ [-1, 1]` the right side is the probability that a random hyperplane separates two unit
vectors with inner product `t`, and the left side is `gwConstant` times their contribution
to the semidefinite relaxation of Max-Cut. -/
theorem gwConstant_mul_le_arccos {t : ℝ} (ht : -1 ≤ t) :
    gwConstant * (1 - t) / 2 ≤ arccos t / π := by
  rcases le_or_gt 1 t with h | h
  · rw [arccos_eq_zero.2 h, zero_div]
    have := gwConstant_pos
    nlinarith
  · have hθ : arccos t ∈ Ioc 0 π := ⟨arccos_pos.2 h, arccos_le_pi t⟩
    have hle := gwConstant_le hθ
    rw [cos_arccos ht h.le] at hle
    calc gwConstant * (1 - t) / 2 ≤ 2 / π * (arccos t / (1 - t)) * (1 - t) / 2 := by gcongr
      _ = arccos t / π := by field_simp

/-- Equality holds in `gwConstant_mul_le_arccos` exactly at `t = 1` and at `t = cos gwAngle`. -/
theorem gwConstant_mul_eq_arccos_iff {t : ℝ} (ht : -1 ≤ t) :
    gwConstant * (1 - t) / 2 = arccos t / π ↔ t = 1 ∨ t = cos gwAngle := by
  have hcos : cos gwAngle < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt gwAngle_mem_Ioo.1 (by linarith [gwAngle_mem_Ioo.2, pi_pos])
  rcases le_or_gt 1 t with h | h
  · rw [arccos_eq_zero.2 h, zero_div, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
    simp only [gwConstant_pos.ne', false_or, two_ne_zero, or_false]
    exact ⟨fun e ↦ .inl e.symm, by rintro (rfl | rfl) <;> [rfl; linarith]⟩
  · have hθ : arccos t ∈ Ioc 0 π := ⟨arccos_pos.2 h, arccos_le_pi t⟩
    have h1 : 0 < 1 - t := by linarith
    have e : gwConstant * (1 - t) / 2 = arccos t / π ↔
        gwConstant = 2 / π * (arccos t / (1 - cos (arccos t))) := by
      rw [cos_arccos ht h.le]
      constructor <;> intro he
      · rw [div_eq_div_iff two_ne_zero pi_pos.ne'] at he
        field_simp
        linear_combination he
      · rw [he]; field_simp
    rw [e, gwConstant_eq_iff hθ]
    constructor
    · intro he
      exact .inr (by rw [← he, cos_arccos ht h.le])
    · rintro (rfl | rfl)
      · exact absurd h (lt_irrefl 1)
      · exact arccos_cos gwAngle_pos.le gwAngle_mem_Ioo.2.le

end TauCeti
