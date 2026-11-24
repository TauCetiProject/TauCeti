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
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Hadamard
import TauCeti.Analysis.Complex.Annulus.Basic
import TauCeti.Analysis.Complex.VerticalStrip.Basic

/-!
# Hadamard's three-circles theorem

Let `0 < r₁ ≤ r₃` and let `f : ℂ → E` be continuous on the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃`
and holomorphic on the open annulus, that is `DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)`.
Write `M r` for the supremum of `‖f‖` on the circle `sphere z₀ r`, spelled
`⨆ w : sphere z₀ r, ‖f w‖`. Hadamard's three-circles theorem says that `log (M r)` is a convex
function of `log r`: for `r₁ ≤ r₂ ≤ r₃`,
`M r₂ ≤ M r₁ ^ (1 - θ) * M r₃ ^ θ` with `θ = log (r₂ / r₁) / log (r₃ / r₁)`.

The proof applies Mathlib's three-lines theorem
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` to `w ↦ f (z₀ + exp w)`
on the strip `log r₁ ≤ re w ≤ log r₃`, which the exponential maps onto the closed annulus.

## Main results

* `TauCeti.Complex.norm_le_rpow_mul_rpow_of_diffContOnCl_annulus`: the pointwise form, with
  arbitrary bounds for `‖f‖` on the two boundary circles.
* `TauCeti.Complex.iSup_norm_sphere_le_rpow_mul_rpow`: the three-circles inequality for the
  suprema over circles.
* `TauCeti.Complex.eqOn_zero_closure_of_iSup_norm_sphere_eq_zero`,
  `TauCeti.Complex.iSup_norm_sphere_pos`: if the supremum vanishes on one circle of positive
  radius in the closed annulus then `f` vanishes on the whole closed annulus; otherwise every such
  supremum is positive.
* `TauCeti.Complex.convexOn_log_iSup_norm_sphere`: for `f` not identically zero on the annulus,
  `t ↦ log (M (exp t))` is convex on `[log r₁, log r₃]`.
* `TauCeti.Complex.norm_le_iSup_norm_sphere_of_mem_closedBall`: the maximum modulus principle on
  a closed disc, in terms of the supremum over the boundary circle.

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

/-- The exponential parametrisation `w ↦ z₀ + exp w` maps the open strip
`log r₁ < re w < log r₃` into the open annulus `r₁ < ‖z - z₀‖ < r₃`. -/
private theorem mapsTo_add_exp_verticalStrip (z₀ : ℂ) (hr₁ : 0 < r₁) (hr₃ : 0 < r₃) :
    MapsTo (fun w => z₀ + exp w) (verticalStrip (Real.log r₁) (Real.log r₃))
      (ball z₀ r₃ \ closedBall z₀ r₁) := by
  intro w hw
  have h₁ : r₁ < Real.exp w.re := (Real.log_lt_iff_lt_exp hr₁).1 hw.1
  have h₃ : Real.exp w.re < r₃ := (Real.lt_log_iff_exp_lt hr₃).1 hw.2
  simp [norm_exp, h₁, h₃]

/-- For `0 ≤ r₁ < r₃`, the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃` lies in the closure of the open
annulus: the translate to the centre `z₀` of `closure_ball_diff_closedBall`. -/
private theorem closedBall_diff_ball_subset_closure (z₀ : ℂ) (hr₁ : 0 ≤ r₁) (h : r₁ < r₃) :
    closedBall z₀ r₃ \ ball z₀ r₁ ⊆ closure (ball z₀ r₃ \ closedBall z₀ r₁) := by
  intro z hz
  have h0 : z - z₀ ∈ closure (ball (0 : ℂ) r₃ \ closedBall 0 r₁) := by
    rw [closure_ball_diff_closedBall hr₁ h]
    simpa [dist_eq_norm] using hz
  have hmem := map_mem_closure (continuous_id.add continuous_const : Continuous fun w : ℂ => w + z₀)
    h0 (t := ball z₀ r₃ \ closedBall z₀ r₁) fun w hw => by simpa [dist_eq_norm] using hw
  simpa using hmem

/-- A function satisfying `DiffContOnCl` on an open annulus is bounded on every circle of the
closed annulus. -/
private theorem bddAbove_range_norm_sphere (hr₁ : 0 ≤ r₁) (h : r₁ < r₃)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁ : r₁ ≤ r) (h₃ : r ≤ r₃) :
    BddAbove (range fun w : sphere z₀ r => ‖f w‖) := by
  rw [← image_eq_range (fun w => ‖f w‖) (sphere z₀ r)]
  refine (isCompact_sphere z₀ r).bddAbove_image (hf.continuousOn.norm.mono fun w hw => ?_)
  exact closedBall_diff_ball_subset_closure z₀ hr₁ h
    ⟨mem_closedBall.2 ((mem_sphere.1 hw).le.trans h₃),
      fun hw' => not_lt.2 (h₁.trans_eq (mem_sphere.1 hw).symm) (mem_ball.1 hw')⟩

/-- **Hadamard's three-circles theorem**, pointwise form. Let `0 < r₁` and let `f` be continuous
on the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃` and holomorphic on the open one. If `‖f‖ ≤ a` on the
circle of radius `r₁` and `‖f‖ ≤ b` on the circle of radius `r₃`, then at every point `z` of the
closed annulus `‖f z‖ ≤ a ^ (1 - θ) * b ^ θ` with `θ = log (‖z - z₀‖ / r₁) / log (r₃ / r₁)`. -/
theorem norm_le_rpow_mul_rpow_of_diffContOnCl_annulus (hr₁ : 0 < r₁)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁))
    (ha : ∀ w ∈ sphere z₀ r₁, ‖f w‖ ≤ a) (hb : ∀ w ∈ sphere z₀ r₃, ‖f w‖ ≤ b)
    (hz₁ : r₁ ≤ ‖z - z₀‖) (hz₃ : ‖z - z₀‖ ≤ r₃) :
    ‖f z‖ ≤ a ^ (1 - Real.log (‖z - z₀‖ / r₁) / Real.log (r₃ / r₁)) *
      b ^ (Real.log (‖z - z₀‖ / r₁) / Real.log (r₃ / r₁)) := by
  rcases (hz₁.trans hz₃).eq_or_lt with rfl | h
  · have hz : z ∈ sphere z₀ r₁ := by simpa [dist_eq_norm] using le_antisymm hz₃ hz₁
    simpa [div_self hr₁.ne'] using ha z hz
  have hr₃ : 0 < r₃ := hr₁.trans h
  have hl : Real.log r₁ < Real.log r₃ := Real.log_lt_log hr₁ h
  have hne : z - z₀ ≠ 0 := norm_pos_iff.1 (hr₁.trans_le hz₁)
  have hmaps := mapsTo_add_exp_verticalStrip z₀ hr₁ hr₃
  have hg : Continuous fun w : ℂ => z₀ + exp w := by fun_prop
  have hd : DiffContOnCl ℂ (f ∘ fun w => z₀ + exp w)
      (verticalStrip (Real.log r₁) (Real.log r₃)) :=
    hf.comp (by fun_prop : Differentiable ℂ fun w : ℂ => z₀ + exp w).diffContOnCl hmaps
  have hB : BddAbove ((norm ∘ (f ∘ fun w => z₀ + exp w)) ''
      verticalClosedStrip (Real.log r₁) (Real.log r₃)) := by
    obtain ⟨C, hC⟩ := (isBounded_ball.subset sdiff_subset).isCompact_closure
      |>.exists_bound_of_continuousOn hf.continuousOn
    refine ⟨C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← HadamardThreeLines.closure_verticalStrip hl] at hw
    exact hC _ (hmaps.closure hg hw)
  have hsphere : ∀ {ρ : ℝ} {w : ℂ}, w.re = Real.log ρ → 0 < ρ → z₀ + exp w ∈ sphere z₀ ρ := by
    intro ρ w hw hρ
    simp [norm_exp, hw, Real.exp_log hρ]
  have hlog : log (z - z₀) ∈ verticalClosedStrip (Real.log r₁) (Real.log r₃) :=
    ⟨by rw [log_re]; exact Real.log_le_log hr₁ hz₁,
      by rw [log_re]; exact Real.log_le_log (norm_pos_iff.2 hne) hz₃⟩
  have key := norm_le_interp_of_mem_verticalClosedStrip' hl hlog hd hB
    (fun w hw => ha _ (hsphere hw hr₁)) (fun w hw => hb _ (hsphere hw hr₃))
  simpa [exp_log hne, log_re, Real.log_div (norm_ne_zero_iff.2 hne) hr₁.ne',
    Real.log_div hr₃.ne' hr₁.ne'] using key

/-- **Hadamard's three-circles theorem.** Let `0 < r₁` and let `f` be continuous on the closed
annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃` and holomorphic on the open one. Then for `r₁ ≤ r₂ ≤ r₃` the suprema
`M r` of `‖f‖` over the circles `sphere z₀ r` satisfy `M r₂ ≤ M r₁ ^ (1 - θ) * M r₃ ^ θ` with
`θ = log (r₂ / r₁) / log (r₃ / r₁)`. -/
theorem iSup_norm_sphere_le_rpow_mul_rpow (hr₁ : 0 < r₁)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁₂ : r₁ ≤ r₂) (h₂₃ : r₂ ≤ r₃) :
    ⨆ w : sphere z₀ r₂, ‖f w‖ ≤
      (⨆ w : sphere z₀ r₁, ‖f w‖) ^ (1 - Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) *
        (⨆ w : sphere z₀ r₃, ‖f w‖) ^ (Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) := by
  rcases (h₁₂.trans h₂₃).eq_or_lt with rfl | h
  · obtain rfl := le_antisymm h₂₃ h₁₂
    simp [div_self hr₁.ne']
  have hM : ∀ {ρ : ℝ}, r₁ ≤ ρ → ρ ≤ r₃ → ∀ w ∈ sphere z₀ ρ, ‖f w‖ ≤ ⨆ w : sphere z₀ ρ, ‖f w‖ :=
    fun h₁ h₃ w hw => le_ciSup (bddAbove_range_norm_sphere hr₁.le h hf h₁ h₃) ⟨w, hw⟩
  refine Real.iSup_le (fun w => ?_) (mul_nonneg
    (Real.rpow_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) _)
    (Real.rpow_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) _))
  have hw : ‖(w : ℂ) - z₀‖ = r₂ := by simpa [dist_eq_norm] using w.property
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
  have hz₁ : r₁ < ‖z - z₀‖ := by simpa [dist_eq_norm] using hz.2
  have hz₃ : ‖z - z₀‖ < r₃ := by simpa [dist_eq_norm] using hz.1
  have hzM : ‖f z‖ ≤ ⨆ w : sphere z₀ ‖z - z₀‖, ‖f w‖ :=
    le_ciSup (bddAbove_range_norm_sphere hr₁.le (hz₁.trans hz₃) hf hz₁.le hz₃.le)
      ⟨z, by simp⟩
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

/-- If `f` is continuous on the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃` and holomorphic on the open
one, and the supremum of `‖f‖` over one circle `sphere z₀ r` with `0 < r` and `r₁ ≤ r ≤ r₃` is
zero, then `f` vanishes on the closure of the open annulus. The circle may be one of the two
boundary circles, where the identity theorem does not apply. The inner radius `r₁` may be zero or
negative, when the annulus is a punctured disc or a disc; the circle of radius `0` is excluded, as
`f z = z - z₀` shows. -/
theorem eqOn_zero_closure_of_iSup_norm_sphere_eq_zero (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁ : r₁ ≤ r) (h₃ : r ≤ r₃)
    (h0 : ⨆ w : sphere z₀ r, ‖f w‖ = 0) :
    EqOn f 0 (closure (ball z₀ r₃ \ closedBall z₀ r₁)) := by
  have hopen : IsOpen (ball z₀ r₃ \ closedBall z₀ r₁) := isOpen_ball.sdiff isClosed_closedBall
  refine EqOn.of_subset_closure (fun z hz => ?_) hf.continuousOn continuous_zero.continuousOn
    (inter_subset_left.trans subset_closure)
    (closure_minimal ((dense_compl_singleton z₀).open_subset_closure_inter hopen) isClosed_closure)
  have hz₁ : r₁ < ‖z - z₀‖ := by simpa [dist_eq_norm] using hz.1.2
  have hz₃ : ‖z - z₀‖ < r₃ := mem_ball_iff_norm.1 hz.1.1
  have hs : 0 < min ‖z - z₀‖ r := lt_min (norm_pos_iff.2 (sub_ne_zero.2 hz.2)) hr
  refine eqOn_zero_closure_of_pos hs
    (hf.mono (sdiff_subset_sdiff_right (closedBall_subset_closedBall (le_min hz₁.le h₁))))
    (min_le_right _ _) h₃ h0 ?_
  exact closedBall_diff_ball_subset_closure z₀ hs.le ((min_le_left _ _).trans_lt hz₃)
    ⟨mem_closedBall_iff_norm.2 hz₃.le,
      fun h => not_lt.2 (min_le_left _ _) (mem_ball_iff_norm.1 h)⟩

/-- If `f` is continuous on the closed annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃`, holomorphic on the open one
and not identically zero there, then the supremum of `‖f‖` over every circle `sphere z₀ r` with
`0 < r` and `r₁ ≤ r ≤ r₃` is positive. -/
theorem iSup_norm_sphere_pos (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁)) (h₁ : r₁ ≤ r) (h₃ : r ≤ r₃)
    (hne : ∃ z ∈ closure (ball z₀ r₃ \ closedBall z₀ r₁), f z ≠ 0) :
    0 < ⨆ w : sphere z₀ r, ‖f w‖ := by
  obtain ⟨z, hz, hfz⟩ := hne
  exact (Real.iSup_nonneg fun _ => norm_nonneg _).lt_of_ne' fun h0 =>
    hfz (eqOn_zero_closure_of_iSup_norm_sphere_eq_zero hr hf h₁ h₃ h0 hz)

/-- **Hadamard's three-circles theorem**, convexity form. If `f` is continuous on the closed
annulus `r₁ ≤ ‖z - z₀‖ ≤ r₃`, holomorphic on the open one and not identically zero there, then
the logarithm of the supremum of `‖f‖` over `sphere z₀ r` is a convex function of `log r`: the
function `t ↦ log (⨆ w : sphere z₀ (exp t), ‖f w‖)` is convex on `[log r₁, log r₃]`. No sign
condition on `r₁` is needed: `r₁ ≤ exp (log r₁)` also holds for the junk values of `log`. -/
theorem convexOn_log_iSup_norm_sphere
    (hf : DiffContOnCl ℂ f (ball z₀ r₃ \ closedBall z₀ r₁))
    (hne : ∃ z ∈ closure (ball z₀ r₃ \ closedBall z₀ r₁), f z ≠ 0) :
    ConvexOn ℝ (Icc (Real.log r₁) (Real.log r₃))
      fun t => Real.log (⨆ w : sphere z₀ (Real.exp t), ‖f w‖) := by
  have hr₃ : 0 < r₃ := by
    obtain ⟨z, hz, -⟩ := hne
    obtain ⟨w, hw⟩ := closure_nonempty_iff.1 ⟨z, hz⟩
    exact dist_nonneg.trans_lt (mem_ball.1 hw.1)
  have hr₁ : r₁ ≤ Real.exp (Real.log r₁) := Real.le_exp_log r₁
  have hpos : ∀ t ∈ Icc (Real.log r₁) (Real.log r₃), 0 < ⨆ w : sphere z₀ (Real.exp t), ‖f w‖ :=
    fun t ht => iSup_norm_sphere_pos (Real.exp_pos t) hf (hr₁.trans (Real.exp_le_exp.2 ht.1))
      ((Real.le_log_iff_exp_le hr₃).1 ht.2) hne
  refine LinearOrder.convexOn_of_lt (convex_Icc _ _) fun x hx y hy hxy a b ha hb hab => ?_
  have hmem : a • x + b • y ∈ Icc x y :=
    convex_Icc x y (left_mem_Icc.2 hxy.le) (right_mem_Icc.2 hxy.le) ha.le hb.le hab
  have hθ : Real.log (Real.exp (a • x + b • y) / Real.exp x) /
      Real.log (Real.exp y / Real.exp x) = b := by
    rw [← Real.exp_sub, ← Real.exp_sub, Real.log_exp, Real.log_exp,
      div_eq_iff (sub_pos.2 hxy).ne']
    simp only [smul_eq_mul]
    linear_combination x * hab
  have key := iSup_norm_sphere_le_rpow_mul_rpow (Real.exp_pos x)
    (hf.mono (sdiff_subset_sdiff (ball_subset_ball ((Real.le_log_iff_exp_le hr₃).1 hy.2))
      (closedBall_subset_closedBall (hr₁.trans (Real.exp_le_exp.2 hx.1)))))
    (Real.exp_le_exp.2 hmem.1) (Real.exp_le_exp.2 hmem.2)
  rw [hθ, show 1 - b = a by linarith] at key
  calc Real.log (⨆ w : sphere z₀ (Real.exp (a • x + b • y)), ‖f w‖)
    _ ≤ Real.log ((⨆ w : sphere z₀ (Real.exp x), ‖f w‖) ^ a *
          (⨆ w : sphere z₀ (Real.exp y), ‖f w‖) ^ b) :=
        Real.log_le_log (hpos _ (convex_Icc _ _ hx hy ha.le hb.le hab)) key
    _ = a • Real.log (⨆ w : sphere z₀ (Real.exp x), ‖f w‖) +
          b • Real.log (⨆ w : sphere z₀ (Real.exp y), ‖f w‖) := by
        rw [smul_eq_mul, smul_eq_mul,
          Real.log_mul (Real.rpow_pos_of_pos (hpos x hx) a).ne'
            (Real.rpow_pos_of_pos (hpos y hy) b).ne',
          Real.log_rpow (hpos x hx), Real.log_rpow (hpos y hy)]

/-- The maximum modulus principle on a closed disc, in terms of the supremum over the boundary
circle: if `f` is continuous on `closedBall z₀ r` and holomorphic on `ball z₀ r`, then `‖f z‖` is
at most the supremum of `‖f‖` over `sphere z₀ r` for every `z` in the closed disc. -/
theorem norm_le_iSup_norm_sphere_of_mem_closedBall (hf : DiffContOnCl ℂ f (ball z₀ r))
    (hz : z ∈ closedBall z₀ r) : ‖f z‖ ≤ ⨆ w : sphere z₀ r, ‖f w‖ := by
  have hbdd : BddAbove (range fun w : sphere z₀ r => ‖f w‖) := by
    rw [← image_eq_range (fun w => ‖f w‖) (sphere z₀ r)]
    exact (isCompact_sphere z₀ r).bddAbove_image
      (hf.continuousOn_ball.norm.mono sphere_subset_closedBall)
  rcases eq_or_ne r 0 with rfl | hr
  · exact le_ciSup hbdd ⟨z, by simpa using hz⟩
  · refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf (fun w hw => ?_)
      (by rwa [closure_ball z₀ hr])
    rw [frontier_ball z₀ hr] at hw
    exact le_ciSup hbdd ⟨w, hw⟩

end TauCeti.Complex
