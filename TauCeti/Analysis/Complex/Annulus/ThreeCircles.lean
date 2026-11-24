/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.Annulus.Basic
import TauCeti.Analysis.Complex.VerticalStrip.Basic

/-!
# Hadamard's three-circles theorem

Let `0 < r₁ < r₃` and let `f : ℂ → E` be holomorphic on the open annulus `r₁ < ‖z - z₀‖ < r₃` and
continuous on its closure, the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃`. Write `M r` for the supremum
of `‖f‖` on the circle `sphere z₀ r`, spelled `⨆ w : sphere z₀ r, ‖f w‖`. Hadamard's
three-circles theorem is the inequality `M r₂ ≤ M r₁ ^ (1 - θ) * M r₃ ^ θ` for `r₁ ≤ r₂ ≤ r₃`,
with `θ = log (r₂ / r₁) / log (r₃ / r₁)`. If `f` is not identically zero then every `M r` is
positive, and the inequality says that `log (M r)` is a convex function of `log r`.

The hypothesis on `f` is `DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)`: differentiability on
the open annulus and continuity on its closure. For `0 ≤ r₁ < r₃` that closure is the closed
annulus (`TauCeti.Complex.closure_ball_diff_closedBall`). For `r₁ = r₃` the open annulus and its
closure are empty and the hypothesis says nothing about `f`, not even on the circle of radius
`r₁`; the two inequalities are stated for `r₁ ≤ r₃` and are trivial in that case, whereas the
vanishing and positivity statements are about the closure of the open annulus and not about the
set `r₁ ≤ ‖z - z₀‖ ≤ r₃`.

The proof applies Mathlib's three-lines theorem
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` to `w ↦ f (z₀ + exp w)`
on the strip `log r₁ ≤ re w ≤ log r₃`, which the translated exponential `w ↦ z₀ + exp w` maps
onto the closed annulus.

## Main results

* `TauCeti.Complex.norm_le_rpow_mul_rpow_of_diffContOnCl_annulus`: the pointwise form, with
  arbitrary bounds for `‖f‖` on the two boundary circles.
* `TauCeti.Complex.iSup_norm_sphere_le_rpow_mul_rpow`: the three-circles inequality for the
  suprema over circles.
* `TauCeti.Complex.eqOn_zero_closure_of_iSup_norm_sphere_eq_zero`,
  `TauCeti.Complex.iSup_norm_sphere_pos`: if the supremum vanishes on one circle of positive
  radius `r` with `r₁ ≤ r ≤ r₃` then `f` vanishes on the closure of the open annulus; if `f` is
  not identically zero on that closure, every such supremum is positive.
* `DiffContOnCl.convexOn_log_iSup_norm_sphere`: `t ↦ log (M (exp t))` is convex on the set of `t`
  with `r₁ ≤ exp t ≤ r₃`.

The maximum modulus principle on a disc in terms of `M` is
`DiffContOnCl.norm_le_iSup_norm_sphere_of_mem_closedBall`, in `TauCeti.Analysis.Complex.AbsMax`.

No hypothesis is placed on `f` off the closure of the annulus, so the functions `(z - z₀) ^ k`
with `k < 0`, which are equality cases, are covered. The exponent is `log`-linear in the radius:
for `f z = z - z₀` and the radii `1, 2, 4` the inequality is the equality
`2 = 1 ^ (1/2) * 4 ^ (1/2)`, whereas the exponent `(r₂ - r₁) / (r₃ - r₁) = 1/3` would give the
false bound `2 ≤ 4 ^ (1/3)`.

## References

* J. Hadamard, *Sur les fonctions entières*, Bull. Soc. Math. France 24 (1896)
* E. C. Titchmarsh, *The Theory of Functions*, second edition, section 5.3
-/

public section

open Complex Complex.HadamardThreeLines Metric Set

namespace TauCeti.Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {z₀ z : ℂ}
  {r r₁ r₂ r₃ a b : ℝ}

/-- **Hadamard's three-circles theorem**, pointwise form. Let `0 < r₁` and let `f` be holomorphic
on the open annulus `r₁ < ‖z - z₀‖ < r₃` and continuous on its closure. If `‖f‖ ≤ a` on the circle
of radius `r₁` and `‖f‖ ≤ b` on the circle of radius `r₃`, then at every point `z` with
`r₁ ≤ ‖z - z₀‖ ≤ r₃` we have `‖f z‖ ≤ a ^ (1 - θ) * b ^ θ`, where
`θ = log (‖z - z₀‖ / r₁) / log (r₃ / r₁)`. For `r₁ = r₃` the closure of the open annulus is empty,
`θ = 0`, and the conclusion is the hypothesis `‖f z‖ ≤ a` on the circle of radius `r₁`. -/
theorem norm_le_rpow_mul_rpow_of_diffContOnCl_annulus (hr₁ : 0 < r₁)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁))
    (ha : ∀ w ∈ sphere z₀ r₁, ‖f w‖ ≤ a) (hb : ∀ w ∈ sphere z₀ r₃, ‖f w‖ ≤ b)
    (hz₁ : r₁ ≤ ‖z - z₀‖) (hz₃ : ‖z - z₀‖ ≤ r₃) :
    ‖f z‖ ≤ a ^ (1 - Real.log (‖z - z₀‖ / r₁) / Real.log (r₃ / r₁)) *
      b ^ (Real.log (‖z - z₀‖ / r₁) / Real.log (r₃ / r₁)) := by
  rcases (hz₁.trans hz₃).eq_or_lt with rfl | h
  · have hz : z ∈ sphere z₀ r₁ := mem_sphere_iff_norm.2 (le_antisymm hz₃ hz₁)
    simpa [div_self hr₁.ne'] using ha z hz
  have hr₃ : 0 < r₃ := hr₁.trans h
  have hl : Real.log r₁ < Real.log r₃ := Real.log_lt_log hr₁ h
  have hne : z - z₀ ≠ 0 := norm_pos_iff.1 (hr₁.trans_le hz₁)
  have hd : DiffContOnCl ℂ (f ∘ fun w => z₀ + exp w)
      (verticalStrip (Real.log r₁) (Real.log r₃)) :=
    hf.comp (by fun_prop : Differentiable ℂ fun w : ℂ => z₀ + exp w).diffContOnCl
      (HadamardThreeLines.mapsTo_add_exp_verticalStrip z₀ r₁ hr₃)
  have hB : BddAbove ((norm ∘ (f ∘ fun w => z₀ + exp w)) ''
      verticalClosedStrip (Real.log r₁) (Real.log r₃)) := by
    refine ((isBounded_ball.subset sdiff_subset).isCompact_closure.bddAbove_image
      hf.continuousOn.norm).mono ?_
    rw [← Function.comp_assoc, image_comp, closure_ball_diff_closedBall hr₁.le h]
    exact image_mono
      (HadamardThreeLines.mapsTo_add_exp_verticalClosedStrip z₀ r₁ hr₃).image_subset
  have hsphere : ∀ {ρ : ℝ} {w : ℂ}, w ∈ re ⁻¹' {Real.log ρ} → 0 < ρ →
      z₀ + exp w ∈ sphere z₀ ρ := by
    intro ρ w hw hρ
    rw [mem_preimage, mem_singleton_iff] at hw
    rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_exp, hw, Real.exp_log hρ]
  have hlog : log (z - z₀) ∈ verticalClosedStrip (Real.log r₁) (Real.log r₃) := by
    rw [HadamardThreeLines.mem_verticalClosedStrip_iff, log_re]
    exact ⟨Real.log_le_log hr₁ hz₁, Real.log_le_log (norm_pos_iff.2 hne) hz₃⟩
  have key := norm_le_interp_of_mem_verticalClosedStrip' hl hlog hd hB
    (fun w hw => ha _ (hsphere hw hr₁)) (fun w hw => hb _ (hsphere hw hr₃))
  simpa [exp_log hne, log_re, Real.log_div (norm_ne_zero_iff.2 hne) hr₁.ne',
    Real.log_div hr₃.ne' hr₁.ne'] using key

/-- **Hadamard's three-circles theorem.** Let `0 < r₁` and let `f` be holomorphic on the open
annulus `r₁ < ‖z - z₀‖ < r₃` and continuous on its closure. Then for `r₁ ≤ r₂ ≤ r₃` the suprema
`M r` of `‖f‖` over the circles `sphere z₀ r` satisfy `M r₂ ≤ M r₁ ^ (1 - θ) * M r₃ ^ θ` with
`θ = log (r₂ / r₁) / log (r₃ / r₁)`. For `r₁ = r₃` the closure of the open annulus is empty,
`θ = 0`, and the inequality reads `M r₁ ≤ M r₁`. -/
theorem iSup_norm_sphere_le_rpow_mul_rpow (hr₁ : 0 < r₁)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃) :
    ⨆ w : sphere z₀ r₂, ‖f w‖ ≤
      (⨆ w : sphere z₀ r₁, ‖f w‖) ^ (1 - Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) *
        (⨆ w : sphere z₀ r₃, ‖f w‖) ^ (Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) := by
  rcases (h₁₂.trans h₂₃).eq_or_lt with rfl | h
  · obtain rfl := le_antisymm h₂₃ h₁₂
    simp [div_self hr₁.ne']
  have hM : ∀ {ρ : ℝ}, r₁ ≤ ρ → ρ ≤ r₃ → ∀ w ∈ sphere z₀ ρ, ‖f w‖ ≤ ⨆ w : sphere z₀ ρ, ‖f w‖ :=
    fun h₁ h₃ w hw => le_ciSup (hf.continuousOn.mono
      (sphere_subset_closure_ball_diff_closedBall hr₁.le h h₁ h₃)).bddAbove_range_norm_sphere
      ⟨w, hw⟩
  refine Real.iSup_le (fun w => ?_) (mul_nonneg
    (Real.rpow_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) _)
    (Real.rpow_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) _))
  have hw : ‖(w : ℂ) - z₀‖ = r₂ := mem_sphere_iff_norm.1 w.property
  have key := norm_le_rpow_mul_rpow_of_diffContOnCl_annulus hr₁ hf (hM le_rfl h.le)
    (hM h.le le_rfl) (h₁₂.trans_eq hw.symm) (hw.trans_le h₂₃)
  rwa [hw] at key

/-- The case `0 < r₁` of `eqOn_zero_closure_of_iSup_norm_sphere_eq_zero`, by the three-circles
inequality on the two sub-annuli cut out by the circle of radius `r`. -/
private theorem eqOn_zero_closure_of_pos (hr₁ : 0 < r₁)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁ : r₁ ≤ r) (h₃ : r ≤ r₃)
    (h0 : ⨆ w : sphere z₀ r, ‖f w‖ = 0) :
    EqOn f 0 (closure (ball z₀ r₃ \ closedBall z₀ r₁)) := by
  have hr : 0 < r := hr₁.trans_le h₁
  refine EqOn.of_subset_closure (fun z hz => ?_) hf.continuousOn continuous_zero.continuousOn
    subset_closure subset_rfl
  obtain ⟨hz₃, hz₁⟩ : ‖z - z₀‖ < r₃ ∧ r₁ < ‖z - z₀‖ := by
    rwa [mem_sdiff, mem_ball_iff_norm, mem_closedBall_iff_norm, not_le] at hz
  have hzM : ‖f z‖ ≤ ⨆ w : sphere z₀ ‖z - z₀‖, ‖f w‖ :=
    le_ciSup (hf.continuousOn.mono (sphere_subset_closure_ball_diff_closedBall hr₁.le
      (hz₁.trans hz₃) hz₁.le hz₃.le)).bddAbove_range_norm_sphere ⟨z, mem_sphere_iff_norm.2 rfl⟩
  have hle : ⨆ w : sphere z₀ ‖z - z₀‖, ‖f w‖ ≤ 0 := by
    rcases le_or_gt ‖z - z₀‖ r with hzr | hzr
    · have key := iSup_norm_sphere_le_rpow_mul_rpow hr₁
        (hf.mono (sdiff_subset_sdiff_left (ball_subset_ball h₃))) hz₁.le hzr
      have hθ : Real.log (‖z - z₀‖ / r₁) / Real.log (r / r₁) ≠ 0 :=
        (div_pos (Real.log_pos ((one_lt_div hr₁).2 hz₁))
          (Real.log_pos ((one_lt_div hr₁).2 (hz₁.trans_le hzr)))).ne'
      rwa [h0, Real.zero_rpow hθ, mul_zero] at key
    · have key := iSup_norm_sphere_le_rpow_mul_rpow hr
        (hf.mono (sdiff_subset_sdiff_right (closedBall_subset_closedBall h₁))) hzr.le hz₃.le
      have hθ : 1 - Real.log (‖z - z₀‖ / r) / Real.log (r₃ / r) ≠ 0 :=
        (sub_pos.2 ((div_lt_one (Real.log_pos ((one_lt_div hr).2 (hzr.trans hz₃)))).2
          (Real.log_lt_log (div_pos (hr.trans hzr) hr) (div_lt_div_of_pos_right hz₃ hr)))).ne'
      rwa [h0, Real.zero_rpow hθ, zero_mul] at key
  exact norm_le_zero_iff.1 (hzM.trans hle)

/-- If `f` is holomorphic on the open annulus `r₁ < ‖z - z₀‖ < r₃` and continuous on its closure,
and the supremum of `‖f‖` over one circle `sphere z₀ r` with `0 < r` and `r₁ ≤ r ≤ r₃` is zero,
then `f` vanishes on the closure of the open annulus. The circle may be one of the two boundary
circles, where the identity theorem does not apply. The inner radius `r₁` may be zero or negative,
when the annulus is a punctured disc or a disc; the circle of radius `0` is excluded, as
`f z = z - z₀` shows. For `r₁ = r₃` the closure of the open annulus is empty and the statement is
vacuous: nothing is claimed on the circle of radius `r₁`. -/
theorem eqOn_zero_closure_of_iSup_norm_sphere_eq_zero (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁ : r₁ ≤ r) (h₃ : r ≤ r₃)
    (h0 : ⨆ w : sphere z₀ r, ‖f w‖ = 0) :
    EqOn f 0 (closure (ball z₀ r₃ \ closedBall z₀ r₁)) := by
  have hopen : IsOpen (ball z₀ r₃ \ closedBall z₀ r₁) := isOpen_ball.sdiff isClosed_closedBall
  refine EqOn.of_subset_closure (fun z hz => ?_) hf.continuousOn continuous_zero.continuousOn
    (inter_subset_left.trans subset_closure)
    (closure_minimal ((dense_compl_singleton z₀).open_subset_closure_inter hopen) isClosed_closure)
  obtain ⟨hzA, hzne⟩ := hz
  obtain ⟨hz₃, hz₁⟩ : ‖z - z₀‖ < r₃ ∧ r₁ < ‖z - z₀‖ := by
    rwa [mem_sdiff, mem_ball_iff_norm, mem_closedBall_iff_norm, not_le] at hzA
  have hs : 0 < min ‖z - z₀‖ r := lt_min (norm_pos_iff.2 (sub_ne_zero.2 hzne)) hr
  exact eqOn_zero_closure_of_pos hs
    (hf.mono (sdiff_subset_sdiff_right (closedBall_subset_closedBall (le_min hz₁.le h₁))))
    (min_le_right _ _) h₃ h0
    (sphere_subset_closure_ball_diff_closedBall hs.le ((min_le_left _ _).trans_lt hz₃)
      (min_le_left _ _) hz₃.le (mem_sphere_iff_norm.2 rfl))

/-- If `f` is holomorphic on the open annulus `r₁ < ‖z - z₀‖ < r₃`, continuous on its closure and
not identically zero on that closure, then the supremum of `‖f‖` over every circle `sphere z₀ r`
with `0 < r` and `r₁ ≤ r ≤ r₃` is positive. The hypothesis `hne` forces `r₁ < r₃`, since the
closure is empty otherwise. -/
theorem iSup_norm_sphere_pos (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁ : r₁ ≤ r) (h₃ : r ≤ r₃)
    (hne : ∃ z ∈ closure (ball z₀ r₃ \ closedBall z₀ r₁), f z ≠ 0) :
    0 < ⨆ w : sphere z₀ r, ‖f w‖ := by
  obtain ⟨z, hz, hfz⟩ := hne
  exact (Real.iSup_nonneg fun _ => norm_nonneg _).lt_of_ne' fun h0 =>
    hfz (eqOn_zero_closure_of_iSup_norm_sphere_eq_zero hr hf h₁ h₃ h0 hz)

/-- The convexity inequality of `DiffContOnCl.convexOn_log_iSup_norm_sphere` between two radii
`exp x < exp y`, for a function satisfying `DiffContOnCl` on the annulus between them. If `f`
vanishes on the closure of that annulus, the three suprema are `0` and so are their logarithms. -/
private theorem log_iSup_norm_sphere_exp_le {x y : ℝ} (hxy : x < y)
    (hf : DiffContOnCl ℂ f (ball z₀ (Real.exp y) \ closedBall z₀ (Real.exp x)))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.log (⨆ w : sphere z₀ (Real.exp (a • x + b • y)), ‖f w‖) ≤
      a • Real.log (⨆ w : sphere z₀ (Real.exp x), ‖f w‖) +
        b • Real.log (⨆ w : sphere z₀ (Real.exp y), ‖f w‖) := by
  have hmem : a • x + b • y ∈ Icc x y :=
    convex_Icc x y (left_mem_Icc.2 hxy.le) (right_mem_Icc.2 hxy.le) ha.le hb.le hab
  have h₁ : Real.exp x ≤ Real.exp (a • x + b • y) := Real.exp_le_exp.2 hmem.1
  have h₃ : Real.exp (a • x + b • y) ≤ Real.exp y := Real.exp_le_exp.2 hmem.2
  have hxy' : Real.exp x ≤ Real.exp y := Real.exp_le_exp.2 hxy.le
  by_cases hne : ∃ z ∈ closure (ball z₀ (Real.exp y) \ closedBall z₀ (Real.exp x)), f z ≠ 0
  · have hpos : ∀ {ρ : ℝ}, Real.exp x ≤ ρ → ρ ≤ Real.exp y → 0 < ⨆ w : sphere z₀ ρ, ‖f w‖ :=
      fun hρ₁ hρ₃ => iSup_norm_sphere_pos ((Real.exp_pos x).trans_le hρ₁) hf hρ₁ hρ₃ hne
    have hθ : Real.log (Real.exp (a • x + b • y) / Real.exp x) /
        Real.log (Real.exp y / Real.exp x) = b := by
      simp only [← Real.exp_sub, Real.log_exp, smul_eq_mul]
      rw [div_eq_iff (sub_pos.2 hxy).ne']
      linear_combination x * hab
    have key := iSup_norm_sphere_le_rpow_mul_rpow (Real.exp_pos x) hf h₁ h₃
    rw [hθ, sub_eq_iff_eq_add.2 hab.symm] at key
    calc Real.log (⨆ w : sphere z₀ (Real.exp (a • x + b • y)), ‖f w‖)
      _ ≤ Real.log ((⨆ w : sphere z₀ (Real.exp x), ‖f w‖) ^ a *
            (⨆ w : sphere z₀ (Real.exp y), ‖f w‖) ^ b) := Real.log_le_log (hpos h₁ h₃) key
      _ = a • Real.log (⨆ w : sphere z₀ (Real.exp x), ‖f w‖) +
            b • Real.log (⨆ w : sphere z₀ (Real.exp y), ‖f w‖) := by
          simp only [smul_eq_mul, Real.log_rpow (hpos le_rfl hxy'),
            Real.log_rpow (hpos hxy' le_rfl),
            Real.log_mul (Real.rpow_pos_of_pos (hpos le_rfl hxy') a).ne'
              (Real.rpow_pos_of_pos (hpos hxy' le_rfl) b).ne']
  · push Not at hne
    have h0 : ∀ {ρ : ℝ}, Real.exp x ≤ ρ → ρ ≤ Real.exp y → ⨆ w : sphere z₀ ρ, ‖f w‖ = 0 :=
      fun hρ₁ hρ₃ => le_antisymm (Real.iSup_le (fun w => (norm_eq_zero.2 (hne w
        (sphere_subset_closure_ball_diff_closedBall (Real.exp_pos x).le (Real.exp_lt_exp.2 hxy)
          hρ₁ hρ₃ w.property))).le) le_rfl) (Real.iSup_nonneg fun _ => norm_nonneg _)
    rw [h0 h₁ h₃, h0 le_rfl hxy', h0 hxy' le_rfl, Real.log_zero, smul_zero, smul_zero, add_zero]

end TauCeti.Complex

/-- **Hadamard's three-circles theorem**, convexity form. If `f` is holomorphic on the open
annulus `r₁ < ‖z - z₀‖ < r₃` and continuous on its closure, then the logarithm of the supremum of
`‖f‖` over `sphere z₀ r` is a convex function of `log r`: the function
`t ↦ log (⨆ w : sphere z₀ (exp t), ‖f w‖)` is convex on the set of `t` with `r₁ ≤ exp t ≤ r₃`.
That set is `[log r₁, log r₃]` for `0 < r₁`, and `(-∞, log r₃]` for `r₁ ≤ 0 < r₃`, when the annulus
is a punctured disc or a disc. No condition is placed on the radii, and `f` may vanish
identically: the supremum is then `0` on every circle involved, and `Real.log 0 = 0`. -/
theorem DiffContOnCl.convexOn_log_iSup_norm_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {z₀ : ℂ} {r₁ r₃ : ℝ}
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) :
    ConvexOn ℝ (Real.exp ⁻¹' Icc r₁ r₃)
      fun t => Real.log (⨆ w : sphere z₀ (Real.exp t), ‖f w‖) :=
  LinearOrder.convexOn_of_lt (ordConnected_Icc.preimage_mono Real.exp_monotone).convex
    fun _ hx _ hy hxy _ _ ha hb hab => TauCeti.Complex.log_iSup_norm_sphere_exp_le hxy
      (hf.mono (sdiff_subset_sdiff (ball_subset_ball hy.2) (closedBall_subset_closedBall hx.1)))
      ha hb hab
