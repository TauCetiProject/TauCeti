/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Contour.Curve.Rectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.Laurent.Basic
import TauCeti.Analysis.Contour.Cauchy.Circle
import TauCeti.Analysis.Contour.Cycle.Circle
import TauCeti.Analysis.Contour.Cycle.Fubini
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Cauchy boundary integral identities on rectangles and L-shaped half-strips

This file establishes Cauchy-type integral identities on axis-parallel rectangles and left-infinite
L-shaped half-strips in the presence of finitely many isolated singularities. Unlike the residue
theorem, no meromorphy and no open neighbourhood of the closed region are assumed: the function
need only be continuous on the closed region off the finite singular set `P` and complex
differentiable on its interior off `P`, so points of `P` may be essential singularities. All
theorems are stated for functions valued in an arbitrary complex normed space `E`, matching
Mathlib's `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`.

For a closed rectangle `[σ₁, σ₂] ×ℂ [t₁, t₂]` containing pairwise disjoint closed discs
`Metric.closedBall ρ r` (`r > 0`) in its interior, subtracting the exterior Cauchy integrals
`z ↦ (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w` removes every singularity by the two-circle
annulus Cauchy formula, reducing the rectangle boundary integral to `∑ ρ ∈ P, ∮ z in C(ρ, r), f z`
via Fubini's theorem for contour cycles (`TauCeti.Contour.Cycle.integral_integral_swap`). Combining
this on `[-X, σ₂] ×ℂ [Im w, t₂]` with Cauchy's theorem on `[Re w, σ₂] ×ℂ [t₁, Im w]` and letting
`X → ∞` shifts a finite vertical segment on `Re s = σ₂` to an L-shaped contour running to
`Re s = -∞`, without requiring holomorphy or decay in the removed lower-left block.

## Main results

* `TauCeti.Contour.integral_rectPolygon_sub_inv`: the cycle integral of the Cauchy kernel
  `z ↦ (z - w)⁻¹` around `(rectPolygon z₀ w₀).contourCycle` about an interior point `w` equals
  `2πi`, with four-edge corollary `TauCeti.Contour.rectangle_boundary_integral_sub_inv`.
* `TauCeti.Contour.integral_rectPolygon_eq_sum_circleIntegral`: the cycle integral of `f` around
  `(rectPolygon z₀ w₀).contourCycle` equals the sum of circle integrals around pairwise disjoint
  discs enclosing the isolated singularities `P`, with four-edge corollary
  `TauCeti.Contour.rectangle_boundary_integral_eq_sum_circleIntegral`.
* `TauCeti.Contour.vertical_integral_eq_truncated_lShaped_add_sum_circleIntegral`: finite-cutoff
  L-shaped contour shift from `Re s = σ₂` to a left vertical edge at `Re s = σ₁`.
* `TauCeti.Contour.vertical_integral_eq_lShaped_add_sum_circleIntegral`: shifting a vertical
  segment integral to an L-shaped contour running to `Re s = -∞` plus circle integrals around
  isolated singularities in the upper half-strip.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4.
* S. Lang, *Complex Analysis* (GTM 103), Ch. IV–V.

## Provenance

The statements of `rectangle_boundary_integral_eq_sum_circleIntegral` and
`vertical_integral_eq_lShaped_add_sum_circleIntegral` follow the contour-integration and L-shaped
contour shift formulations in the `IEANTN` formalization (`ContourIntegration` and `CH2`), here
generalized to arbitrary complex normed-space-valued functions and to continuity on the closed
region with complex differentiability on its interior off the singular set.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Interval Real Topology

namespace TauCeti.Contour

section Kernel

/-- **Cauchy kernel cycle integral on a rectangle.** For a point `w` in the open rectangle
`(z₀.re, w₀.re) ×ℂ (z₀.im, w₀.im)`, the cycle integral of `z ↦ (z - w)⁻¹` around
`(rectPolygon z₀ w₀).contourCycle` equals `2πi`. -/
theorem integral_rectPolygon_sub_inv {z₀ w₀ w : ℂ}
    (hw : w ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im) :
    Cycle.integral (fun z ↦ (z - w)⁻¹) (rectPolygon z₀ w₀).contourCycle = 2 * π * I := by
  have hre : z₀.re ≤ w₀.re := (hw.1.1.trans hw.1.2).le
  have him : z₀.im ≤ w₀.im := (hw.2.1.trans hw.2.2).le
  have hfr : w ∉ frontier (Rectangle z₀ w₀) :=
    disjoint_left.1 disjoint_interior_frontier (by rwa [interior_rectangle hre him])
  have havoid : ∀ t ∈ uIcc (0 : ℝ) 4, rectBoundary z₀ w₀ t ≠ w :=
    fun t _ h ↦ hfr (h ▸ rectBoundary_mem_frontier t)
  have hγ := isPiecewiseC1On_rectBoundary z₀ w₀
  have hwind := windingNumber_rectBoundary_eq_one hw
  rw [windingNumber_eq_integral_of_avoidance hγ.continuousOn havoid
    (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn havoid hγ.intervalIntegrable_deriv)]
    at hwind
  have hne : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hint : ∫ t in (0 : ℝ)..4, deriv (rectBoundary z₀ w₀) t • (rectBoundary z₀ w₀ t - w)⁻¹ =
      2 * π * I := by
    have hmul := congrArg (fun x ↦ (2 * (π : ℂ) * I) * x) hwind
    simp only [mul_one, mul_inv_cancel_left₀ hne] at hmul
    rw [← hmul]
    exact intervalIntegral.integral_congr fun t _ ↦ by rw [smul_eq_mul, mul_comm]
  rw [(rectPolygon z₀ w₀).integral_contourCycle_eq_integral_boundaryParam, Nat.cast_ofNat,
    ← rectBoundary_def, hint]

/-- **Cauchy kernel integral on a rectangle boundary.** Four-edge corollary of
`integral_rectPolygon_sub_inv`: for a point `w` in the open rectangle `(σ₁, σ₂) ×ℂ (t₁, t₂)`,
Mathlib's four-edge boundary expression for `z ↦ (z - w)⁻¹` equals `2πi`. -/
theorem rectangle_boundary_integral_sub_inv {σ₁ σ₂ t₁ t₂ : ℝ} {w : ℂ}
    (hw : w ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) :
    (∫ x : ℝ in σ₁..σ₂, ((x : ℂ) + t₁ * I - w)⁻¹) -
      (∫ x : ℝ in σ₁..σ₂, ((x : ℂ) + t₂ * I - w)⁻¹) +
      I * (∫ y : ℝ in t₁..t₂, ((σ₂ : ℂ) + y * I - w)⁻¹) -
      I * (∫ y : ℝ in t₁..t₂, ((σ₁ : ℂ) + y * I - w)⁻¹) = 2 * π * I := by
  let z₀ : ℂ := σ₁ + t₁ * I
  let w₀ : ℂ := σ₂ + t₂ * I
  have hw' : w ∈ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by simpa [z₀, w₀] using hw
  have hre : z₀.re ≤ w₀.re := (hw'.1.1.trans hw'.1.2).le
  have him : z₀.im ≤ w₀.im := (hw'.2.1.trans hw'.2.2).le
  have hfr : w ∉ frontier (Rectangle z₀ w₀) :=
    disjoint_left.1 disjoint_interior_frontier (by rwa [interior_rectangle hre him])
  have hcont : ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹) (frontier (Rectangle z₀ w₀)) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦
      sub_ne_zero.2 fun h ↦ by simp only [id_eq] at h; exact hfr (h ▸ hz)
  have h := (integral_contourCycle_rectPolygon hcont).symm.trans (integral_rectPolygon_sub_inv hw')
  simpa [z₀, w₀, smul_eq_mul] using h

end Kernel

section CircleSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- By Fubini's theorem for cycles and the Cauchy kernel integral on a rectangle, the boundary
integral of the exterior Cauchy integral of `f` over `C(ρ, r)` around an enclosing rectangle
equals `∮ w in C(ρ, r), f w`. -/
private theorem integral_rectPolygon_exteriorCauchy [CompleteSpace E]
    {z₀ w₀ : ℂ} {r : ℝ} (hre : z₀.re ≤ w₀.re) (him : z₀.im ≤ w₀.im) (hr : 0 < r) {ρ : ℂ}
    (hρ : closedBall ρ r ⊆ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im) {f : ℂ → E}
    (hf : ContinuousOn f (sphere ρ r)) :
    Cycle.integral (fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w)
        (rectPolygon z₀ w₀).contourCycle =
      ∮ w in C(ρ, r), f w := by
  let C : Cycle := (rectPolygon z₀ w₀).contourCycle
  let D : Cycle := circleCycle ρ r
  have htraceC : Cycle.trace C = frontier (Rectangle z₀ w₀) := by
    rw [Polygon.trace_contourCycle, boundary_rectPolygon]
  have htraceD : Cycle.trace D = sphere ρ r := by
    rw [Cycle.trace_circleCycle, abs_of_pos hr]
  have hDsub : sphere ρ r ⊆ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im :=
    sphere_subset_closedBall.trans hρ
  have hF : ContinuousOn (Function.uncurry fun z w : ℂ ↦ (z - w)⁻¹ • f w)
      (Cycle.trace C ×ˢ Cycle.trace D) := by
    rw [htraceC, htraceD]
    refine ((continuousOn_fst.sub continuousOn_snd).inv₀ fun p hp ↦ ?_).smul
      (hf.comp continuousOn_snd fun p hp ↦ hp.2)
    refine sub_ne_zero.2 fun heq ↦ disjoint_left.1 disjoint_interior_frontier ?_ hp.1
    rw [interior_rectangle hre him, heq]
    exact hDsub hp.2
  have hswap := Cycle.integral_integral_swap hF
  have hne : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have houter : Cycle.integral (fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w) C =
      (2 * π * I : ℂ)⁻¹ •
        Cycle.integral (fun z ↦ Cycle.integral (fun w ↦ (z - w)⁻¹ • f w) D) C := by
    have hfun : (fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w) =
        fun z ↦ (2 * π * I : ℂ)⁻¹ • Cycle.integral (fun w ↦ (z - w)⁻¹ • f w) D := by
      funext z
      simp only [D, Cycle.integral_circleCycle]
    rw [hfun, Cycle.integral_smul]
  rw [houter, hswap, Cycle.integral_circleCycle]
  have hinner : EqOn (fun w ↦ Cycle.integral (fun z ↦ (z - w)⁻¹ • f w) C)
      (fun w ↦ (2 * π * I : ℂ) • f w) (sphere ρ r) := fun w hw ↦ by
    dsimp only
    rw [Cycle.integral_smul_const, integral_rectPolygon_sub_inv (hDsub hw)]
  rw [circleIntegral.integral_congr hr.le hinner, circleIntegral.integral_smul,
    inv_smul_smul₀ hne]

/-- **Rectangle cycle integral as a sum of circle integrals.** Let `z₀.re ≤ w₀.re`, `z₀.im ≤ w₀.im`,
`r > 0`, and let `P` be a finite set whose closed discs `closedBall ρ r` are pairwise disjoint and
contained in the open rectangle `(z₀.re, w₀.re) ×ℂ (z₀.im, w₀.im)`. If `f : ℂ → E` is continuous
on the closed rectangle minus `P` and complex differentiable on the open rectangle minus `P`, then
`Cycle.integral f (rectPolygon z₀ w₀).contourCycle` equals `∑ ρ ∈ P, ∮ z in C(ρ, r), f z`.

No open neighbourhood of the closed rectangle and no meromorphy at `P` are assumed, so the points
of `P` may be essential singularities. -/
theorem integral_rectPolygon_eq_sum_circleIntegral
    {z₀ w₀ : ℂ} {r : ℝ} (hre : z₀.re ≤ w₀.re) (him : z₀.im ≤ w₀.im) (hr : 0 < r)
    {P : Finset ℂ} (hP : ∀ ρ ∈ P, closedBall ρ r ⊆ Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im)
    (hdisj : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r) (closedBall ρ' r))
    {f : ℂ → E}
    (hc : ContinuousOn f (Rectangle z₀ w₀ \ P))
    (hd : DifferentiableOn ℂ f (Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im \ P)) :
    Cycle.integral f (rectPolygon z₀ w₀).contourCycle =
      ∑ ρ ∈ P, ∮ z in C(ρ, r), f z := by
  wlog hE : CompleteSpace E
  · simp [Cycle.integral_eq_sum_support, circleIntegral, intervalIntegral,
      integral_of_not_completeSpace hE]
  have hP_int : ∀ ρ ∈ P, closedBall ρ r ⊆ interior (Rectangle z₀ w₀) := fun ρ hρ ↦ by
    rw [interior_rectangle hre him]; exact hP ρ hρ
  obtain ⟨g, hg_cont, hg_diff, hg_eq⟩ :=
    TauCeti.exists_continuousOn_differentiableOn_sub_sum_circleIntegral hr hP_int hdisj hc
      (by rwa [interior_rectangle hre him])
  have hUrect : Ioo (min z₀.re w₀.re) (max z₀.re w₀.re) ×ℂ
      Ioo (min z₀.im w₀.im) (max z₀.im w₀.im) = Ioo z₀.re w₀.re ×ℂ Ioo z₀.im w₀.im := by
    simp [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him]
  have hg_zero : Cycle.integral g (rectPolygon z₀ w₀).contourCycle = 0 := by
    rw [integral_contourCycle_rectPolygon (hg_cont.mono (isClosed_rectangle z₀ w₀).frontier_subset)]
    exact Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      g z₀ w₀ hg_cont (by rwa [hUrect, ← interior_rectangle hre him])
  have hfr_out : ∀ z ∈ frontier (Rectangle z₀ w₀), ∀ ρ ∈ P, z ∉ closedBall ρ r := by
    intro z hz ρ hρ hzr
    exact disjoint_left.1 disjoint_interior_frontier (hP_int ρ hρ hzr) hz
  have htrace : Cycle.trace (rectPolygon z₀ w₀).contourCycle = frontier (Rectangle z₀ w₀) := by
    rw [Polygon.trace_contourCycle, boundary_rectPolygon]
  have hf_fr : ContinuousOn f (frontier (Rectangle z₀ w₀)) :=
    hc.mono fun z hz ↦ ⟨(isClosed_rectangle z₀ w₀).frontier_subset hz,
      fun hzP ↦ hfr_out z hz z hzP (mem_closedBall_self hr.le)⟩
  have hfc_r : ∀ ρ ∈ P, ContinuousOn f (sphere ρ r) := fun ρ hρ ↦
    TauCeti.continuousOn_sphere_of_closedBall_subset hr le_rfl
      (fun ρ' hρ' ↦ (hP_int ρ' hρ').trans interior_subset) hdisj hc hρ
  have hext_fr : ∀ ρ ∈ P,
      ContinuousOn (fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w)
        (Cycle.trace (rectPolygon z₀ w₀).contourCycle) := by
    rw [htrace]
    exact fun ρ hρ z hz ↦
      (differentiableAt_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_left
        ((hfc_r ρ hρ).circleIntegrable hr.le) fun hsp ↦
          hfr_out z hz ρ hρ
            (sphere_subset_closedBall (abs_of_pos hr ▸ hsp))).continuousAt.continuousWithinAt
  have hsplit : Cycle.integral g (rectPolygon z₀ w₀).contourCycle =
      Cycle.integral f (rectPolygon z₀ w₀).contourCycle -
        ∑ ρ ∈ P, Cycle.integral (fun z ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w)
          (rectPolygon z₀ w₀).contourCycle := by
    rw [Cycle.integral_congr
        (g := fun z ↦ f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w)
        fun z hz ↦ hg_eq (by simpa [htrace] using hfr_out z (htrace ▸ hz)),
      Cycle.integral_sub (htrace ▸ hf_fr) (continuousOn_finsetSum P hext_fr),
      Cycle.integral_finsetSum hext_fr]
  rw [hg_zero, eq_comm, sub_eq_zero] at hsplit
  rw [hsplit]
  exact Finset.sum_congr rfl fun ρ hρ ↦
    integral_rectPolygon_exteriorCauchy hre him hr (hP ρ hρ) (hfc_r ρ hρ)

/-- **Rectangle boundary integral as a sum of circle integrals.** Four-edge corollary of
`integral_rectPolygon_eq_sum_circleIntegral`: for `σ₁ ≤ σ₂`, `t₁ ≤ t₂`, `r > 0`, and a finite set
`P` whose closed discs `closedBall ρ r` are pairwise disjoint and contained in
`(σ₁, σ₂) ×ℂ (t₁, t₂)`, if `f : ℂ → E` is continuous on `[σ₁, σ₂] ×ℂ [t₁, t₂] \ P` and complex
differentiable on `(σ₁, σ₂) ×ℂ (t₁, t₂) \ P`, then Mathlib's four-edge boundary expression equals
`∑ ρ ∈ P, ∮ z in C(ρ, r), f z`. -/
theorem rectangle_boundary_integral_eq_sum_circleIntegral
    {σ₁ σ₂ t₁ t₂ r : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂) (hr : 0 < r) {P : Finset ℂ}
    (hP : ∀ ρ ∈ P, closedBall ρ r ⊆ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    (hdisj : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r) (closedBall ρ' r))
    {f : ℂ → E}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P)) :
    (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) +
        I • (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) - I • (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) =
      ∑ ρ ∈ P, ∮ z in C(ρ, r), f z := by
  let z₀ : ℂ := σ₁ + t₁ * I
  let w₀ : ℂ := σ₂ + t₂ * I
  have hzre : z₀.re = σ₁ := by simp [z₀]
  have hzim : z₀.im = t₁ := by simp [z₀]
  have hwre : w₀.re = σ₂ := by simp [w₀]
  have hwim : w₀.im = t₂ := by simp [w₀]
  have hre : z₀.re ≤ w₀.re := hzre ▸ hwre ▸ hσ
  have him : z₀.im ≤ w₀.im := hzim ▸ hwim ▸ ht
  have hrect : Rectangle z₀ w₀ = Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ := by
    rw [Rectangle, hzre, hzim, hwre, hwim, uIcc_of_le hσ, uIcc_of_le ht]
  have hfr : ContinuousOn f (frontier (Rectangle z₀ w₀)) :=
    hc.mono fun z hz ↦ ⟨hrect ▸ (isClosed_rectangle z₀ w₀).frontier_subset hz, fun hzP ↦
      disjoint_left.1 disjoint_interior_frontier
        (by rw [interior_rectangle hre him, hzre, hwre, hzim, hwim]
            exact hP z hzP (mem_closedBall_self hr.le)) hz⟩
  have hcyc := integral_rectPolygon_eq_sum_circleIntegral (z₀ := z₀) (w₀ := w₀) hre him hr
    (by simpa [hzre, hzim, hwre, hwim] using hP) hdisj (hrect ▸ hc)
    (by simpa [hzre, hzim, hwre, hwim] using hd)
  rwa [integral_contourCycle_rectPolygon hfr, hzre, hzim, hwre, hwim] at hcyc

end CircleSum

section LShaped

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Finite-cutoff L-shaped contour shift.** Let `σ₁ ≤ w.re ≤ σ₂`, `t₁ ≤ w.im ≤ t₂`, `r > 0`, and
let `D` be the truncated strip `{σ₁ ≤ Re s ≤ σ₂, t₁ ≤ Im s ≤ t₂}` with the lower-left block
`{Re s < Re w, Im s < Im w}` removed. Let `P` be a finite set whose closed discs `closedBall ρ r`
are pairwise disjoint and lie in `(σ₁, σ₂) ×ℂ (Im w, t₂)`. If `f : ℂ → E` is continuous on `D \ P`
and complex differentiable on `interior D \ P`, then combining `[σ₁, σ₂] ×ℂ [Im w, t₂]` with
`[Re w, σ₂] ×ℂ [t₁, Im w]` cancels the shared segment `[Re w, σ₂] ×ℂ {Im w}` and expresses
`i ∫_{t₁}^{t₂} f(σ₂ + iy) dy` in terms of the truncated L-shaped boundary (including the left
vertical edge at `Re s = σ₁`), the top edge, and `∑ ρ ∈ P, ∮ z in C(ρ, r), f z`.

No holomorphy in the removed lower-left block and no decay at `-∞` are assumed, and the points
of `P` may be essential singularities. -/
theorem vertical_integral_eq_truncated_lShaped_add_sum_circleIntegral
    {σ₁ σ₂ t₁ t₂ r : ℝ} {w : ℂ} {P : Finset ℂ}
    (hr : 0 < r) (hσ₁ : σ₁ ≤ w.re) (hw : w.re ≤ σ₂)
    (ht₁ : t₁ ≤ w.im) (ht₂ : w.im ≤ t₂)
    (hP : ∀ ρ ∈ P, closedBall ρ r ⊆ Ioo σ₁ σ₂ ×ℂ Ioo w.im t₂)
    (hdisj : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r) (closedBall ρ' r))
    {f : ℂ → E}
    (hc : ContinuousOn f
      ({s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ ∧
        (w.re ≤ s.re ∨ w.im ≤ s.im)} \ P))
    (hd : DifferentiableOn ℂ f
      (interior {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ ∧
        (w.re ≤ s.re ∨ w.im ≤ s.im)} \ P)) :
    I • (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) =
      (∫ x : ℝ in σ₂..w.re, f (x + t₁ * I)) +
        I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
        (∫ x : ℝ in σ₁..w.re, f (x + w.im * I)) +
        (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) +
        I • (∫ y : ℝ in w.im..t₂, f (σ₁ + y * I)) +
        ∑ ρ ∈ P, ∮ z in C(ρ, r), f z := by
  let D : Set ℂ := {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂ ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ ∧
    (w.re ≤ s.re ∨ w.im ≤ s.im)}
  have htop_sub : Icc σ₁ σ₂ ×ℂ Icc w.im t₂ ⊆ D := fun s hs ↦
    ⟨hs.1.1, hs.1.2, ht₁.trans hs.2.1, hs.2.2, Or.inr hs.2.1⟩
  have hbot_sub : Icc w.re σ₂ ×ℂ Icc t₁ w.im ⊆ D \ P := fun s hs ↦
    ⟨⟨hσ₁.trans hs.1.1, hs.1.2, hs.2.1, hs.2.2.trans ht₂, Or.inl hs.1.1⟩, fun hsP ↦
      (hP s hsP (mem_closedBall_self hr.le)).2.1.not_ge hs.2.2⟩
  have hIoo_top : Ioo σ₁ σ₂ ×ℂ Ioo w.im t₂ ⊆ D := fun _ hs ↦
    htop_sub ⟨Ioo_subset_Icc_self hs.1, Ioo_subset_Icc_self hs.2⟩
  have hIoo_bot : Ioo w.re σ₂ ×ℂ Ioo t₁ w.im ⊆ D \ P := fun _ hs ↦
    hbot_sub ⟨Ioo_subset_Icc_self hs.1, Ioo_subset_Icc_self hs.2⟩
  have htop := rectangle_boundary_integral_eq_sum_circleIntegral (hσ₁.trans hw) ht₂ hr hP hdisj
    (hc.mono (sdiff_subset_sdiff_left htop_sub))
    (hd.mono (sdiff_subset_sdiff_left <|
      interior_maximal hIoo_top (isOpen_Ioo.reProdIm isOpen_Ioo)))
  have hbot := rectangle_boundary_integral_eq_sum_circleIntegral hw ht₁ one_pos (P := ∅)
    (by simp) (by simp) (by simpa using hc.mono hbot_sub)
    (by simpa using hd.mono fun s hs ↦
      ⟨interior_maximal (hIoo_bot.trans sdiff_subset) (isOpen_Ioo.reProdIm isOpen_Ioo) hs,
        (hIoo_bot hs).2⟩)
  -- Split the vertical right edge at `w.im` and the shared horizontal segment at `w.re`.
  have hright_cont : ContinuousOn (fun y : ℝ ↦ f (σ₂ + y * I)) (Icc t₁ t₂) :=
    hc.comp (continuousOn_const.add (continuous_ofReal.continuousOn.mul continuousOn_const))
      fun y hy ↦ ⟨⟨by simpa using hσ₁.trans hw, by simp, by simpa using hy.1,
        by simpa using hy.2, Or.inl (by simpa using hw)⟩,
        fun hP' ↦ (hP _ hP' (mem_closedBall_self hr.le)).1.2.ne (by simp)⟩
  have hright_split := intervalIntegral.integral_add_adjacent_intervals
    ((hright_cont.mono (by rw [uIcc_of_le ht₁]; exact Icc_subset_Icc_right ht₂)).intervalIntegrable
      (μ := volume))
    ((hright_cont.mono (by rw [uIcc_of_le ht₂]; exact Icc_subset_Icc_left ht₁)).intervalIntegrable
      (μ := volume))
  have hmid_cont : ContinuousOn (fun x : ℝ ↦ f (x + w.im * I)) (Icc σ₁ σ₂) :=
    hc.comp (continuous_ofReal.continuousOn.add continuousOn_const)
      fun x hx ↦ ⟨⟨by simpa using hx.1, by simpa using hx.2, by simpa using ht₁,
        by simpa using ht₂, Or.inr (by simp)⟩,
        fun hP' ↦ (hP _ hP' (mem_closedBall_self hr.le)).2.1.ne (by simp)⟩
  have hmid_split := intervalIntegral.integral_add_adjacent_intervals
    ((hmid_cont.mono (by rw [uIcc_of_le hσ₁]; exact Icc_subset_Icc_right hw)).intervalIntegrable
      (μ := volume))
    ((hmid_cont.mono (by rw [uIcc_of_le hw]; exact Icc_subset_Icc_left hσ₁)).intervalIntegrable
      (μ := volume))
  have hrev : ∫ x : ℝ in w.re..σ₂, f (x + t₁ * I) = -(∫ x : ℝ in σ₂..w.re, f (x + t₁ * I)) :=
    intervalIntegral.integral_symm σ₂ w.re
  have hcomb := congrArg₂ (· + ·) htop hbot
  simp only [Finset.sum_empty, add_zero] at hcomb
  rw [← hmid_split, hrev] at hcomb
  rw [← hright_split, smul_add]
  refine sub_eq_iff_eq_add'.1 ?_
  rw [← hcomb]
  abel

/-- **The L-shaped contour shift to `Re s = -∞`.** Let `w.re ≤ σ₂`, `t₁ ≤ w.im ≤ t₂`, `r > 0`,
and let `D` be the half-infinite strip `{Re s ≤ σ₂, t₁ ≤ Im s ≤ t₂}` with the lower-left block
`{Re s < Re w, Im s < Im w}` removed. Let `P` be a finite set whose closed discs `closedBall ρ r`
are pairwise disjoint and lie in `{Re s < σ₂, Im w < Im s < t₂}`. If `f : ℂ → E` is continuous on
`D \ P`, complex differentiable on `interior D \ P`, tends to `0` as `Re s → -∞` uniformly for
`Im w ≤ Im s ≤ t₂`, and is integrable along the left horizontal rays at heights `Im w` and `t₂`,
then `i ∫_{t₁}^{t₂} f(σ₂ + iy) dy` equals the integral along the L-shaped path
`σ₂ + it₁ → Re w + it₁ → w → -∞ + i Im w`, plus `∫_{-∞}^{σ₂} f(x + it₂) dx`, plus
`∑ ρ ∈ P, ∮ z in C(ρ, r), f z`.

No holomorphy or decay is assumed in the removed lower-left block, and the points of `P` may be
essential singularities. -/
theorem vertical_integral_eq_lShaped_add_sum_circleIntegral
    {σ₂ t₁ t₂ r : ℝ} {w : ℂ} {P : Finset ℂ}
    (hr : 0 < r) (hw : w.re ≤ σ₂) (ht₁ : t₁ ≤ w.im) (ht₂ : w.im ≤ t₂)
    (hP : ∀ ρ ∈ P, closedBall ρ r ⊆ {s : ℂ | s.re < σ₂ ∧ w.im < s.im ∧ s.im < t₂})
    (hdisj : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r) (closedBall ρ' r))
    {f : ℂ → E}
    (hc : ContinuousOn f
      ({s : ℂ | s.re ≤ σ₂ ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ ∧ (w.re ≤ s.re ∨ w.im ≤ s.im)} \ P))
    (hd : DifferentiableOn ℂ f
      (interior {s : ℂ | s.re ≤ σ₂ ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ ∧ (w.re ≤ s.re ∨ w.im ≤ s.im)} \ P))
    (hdecay : Tendsto f (comap Complex.re atBot ⊓ 𝓟 {s : ℂ | w.im ≤ s.im ∧ s.im ≤ t₂}) (𝓝 0))
    (hw_int : IntegrableOn (fun x : ℝ ↦ f (x + w.im * I)) (Iic w.re))
    (ht₂_int : IntegrableOn (fun x : ℝ ↦ f (x + t₂ * I)) (Iic σ₂)) :
    I • (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) =
      (∫ x : ℝ in σ₂..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
        (∫ x in Iic w.re, f (x + w.im * I)) + (∫ x in Iic σ₂, f (x + t₂ * I)) +
        ∑ ρ ∈ P, ∮ z in C(ρ, r), f z := by
  have hev : ∀ᶠ X : ℝ in atTop,
      I • (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) =
        (∫ x : ℝ in σ₂..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
          (∫ x : ℝ in (-X)..w.re, f (x + w.im * I)) + (∫ x : ℝ in (-X)..σ₂, f (x + t₂ * I)) +
          I • (∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) +
          ∑ ρ ∈ P, ∮ z in C(ρ, r), f z := by
    have hPev : ∀ᶠ X : ℝ in atTop, ∀ ρ ∈ P, closedBall ρ r ⊆ Ioo (-X) σ₂ ×ℂ Ioo w.im t₂ := by
      rw [Filter.eventually_all_finset]
      intro ρ hρ
      filter_upwards [eventually_gt_atTop (r - ρ.re)] with X hX s hs
      have hre : -X < s.re := by
        have h1 : |s.re - ρ.re| ≤ r :=
          (Complex.abs_re_le_norm (s - ρ)).trans (mem_closedBall_iff_norm.1 hs)
        linarith [(abs_le.1 h1).1]
      have h2 := hP ρ hρ hs
      exact ⟨⟨hre, h2.1⟩, h2.2.1, h2.2.2⟩
    filter_upwards [eventually_ge_atTop (-w.re), hPev] with X hX hPX
    exact vertical_integral_eq_truncated_lShaped_add_sum_circleIntegral hr (by linarith) hw ht₁ ht₂
      hPX hdisj (hc.mono (sdiff_subset_sdiff_left fun _ h ↦ h.2))
      (hd.mono (sdiff_subset_sdiff_left (interior_mono fun _ h ↦ h.2)))
  have h1 : Tendsto (fun X : ℝ ↦ ∫ x : ℝ in (-X)..w.re, f (x + w.im * I)) atTop
      (𝓝 (∫ x in Iic w.re, f (x + w.im * I))) :=
    intervalIntegral_tendsto_integral_Iic w.re hw_int tendsto_neg_atTop_atBot
  have h2 : Tendsto (fun X : ℝ ↦ ∫ x : ℝ in (-X)..σ₂, f (x + t₂ * I)) atTop
      (𝓝 (∫ x in Iic σ₂, f (x + t₂ * I))) :=
    intervalIntegral_tendsto_integral_Iic σ₂ ht₂_int tendsto_neg_atTop_atBot
  have h3 : Tendsto (fun X : ℝ ↦ I • ∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) atTop (𝓝 0) := by
    have hmap : Tendsto (fun q : ℝ × ℝ ↦ ((-q.1 : ℝ) + q.2 * I))
        (atTop ×ˢ 𝓟 (uIcc w.im t₂))
        (comap Complex.re atBot ⊓ 𝓟 {s : ℂ | w.im ≤ s.im ∧ s.im ≤ t₂}) := by
      refine tendsto_inf.2 ⟨?_, ?_⟩
      · rw [tendsto_comap_iff]
        have hfst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓟 (uIcc w.im t₂)) atTop :=
          tendsto_fst
        simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp hfst
      · rw [tendsto_principal, Filter.eventually_prod_iff]
        refine ⟨fun _ ↦ True, .of_forall fun _ ↦ trivial, fun y ↦ y ∈ uIcc w.im t₂,
          eventually_principal.2 fun _ h ↦ h, fun {_} _ {_} hy ↦ ?_⟩
        rw [uIcc_of_le ht₂] at hy
        simpa using hy
    have hprod : Tendsto (fun q : ℝ × ℝ ↦ f ((-q.1 : ℝ) + q.2 * I))
        (atTop ×ˢ 𝓟 (uIcc w.im t₂)) (𝓝 0) := hdecay.comp hmap
    have h0 : Tendsto (fun X : ℝ ↦ ∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) atTop (𝓝 0) :=
      TendstoUniformlyOn.tendsto_intervalIntegral_nhds_zero (tendsto_prod_principal_iff.mp hprod)
    simpa only [smul_zero] using h0.const_smul I
  have hrhs : Tendsto (fun X : ℝ ↦
        (∫ x : ℝ in σ₂..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
          (∫ x : ℝ in (-X)..w.re, f (x + w.im * I)) + (∫ x : ℝ in (-X)..σ₂, f (x + t₂ * I)) +
          I • (∫ y : ℝ in w.im..t₂, f ((-X : ℝ) + y * I)) +
          ∑ ρ ∈ P, ∮ z in C(ρ, r), f z) atTop
      (𝓝 ((∫ x : ℝ in σ₂..w.re, f (x + t₁ * I)) + I • (∫ y : ℝ in t₁..w.im, f (w.re + y * I)) -
          (∫ x in Iic w.re, f (x + w.im * I)) + (∫ x in Iic σ₂, f (x + t₂ * I)) +
          ∑ ρ ∈ P, ∮ z in C(ρ, r), f z)) := by
    simpa only [add_zero] using
      ((((tendsto_const_nhds.sub h1).add h2).add h3).add tendsto_const_nhds)
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hrhs

end LShaped

end TauCeti.Contour
