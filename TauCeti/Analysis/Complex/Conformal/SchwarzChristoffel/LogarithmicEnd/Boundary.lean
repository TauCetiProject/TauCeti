/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Ray

/-!
# The two boundary levels of a logarithmic Schwarz--Christoffel end

Near a real prevertex of total exponent `-1`, the two adjacent boundary sides lie on
distinct parallel lines. Dividing by the prevertex coefficient and translating by the
constant term of the logarithmic remainder puts the right side at height `0` and the
left side at height `π`. Both sides extend to negative real infinity in these coordinates.

The exact separation of the lines is needed to identify the strip between them as the
local image of the end. The results here concern the boundary; they assume neither global
univalence nor integrability at other prevertices, and allow coincident prevertices.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Filter Metric Set Topology
open UpperHalfPlane hiding I continuous_im continuous_re

namespace TauCeti

variable {ι : Type*} [Fintype ι]

private theorem boundary_eq_log_add (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (p : ℝ) {H : ℂ → ℂ} {r x : ℝ} (hH : AnalyticOnNhd ℂ H (ball (p : ℂ) r))
    (hF : ∀ z ∈ ball (p : ℂ) r ∩ upperHalfPlaneSet,
      schwarzChristoffelPrimitive a e z₀ z -
        schwarzChristoffelPrevertexCoefficient a e p * log (z - (p : ℂ)) = H z)
    (hx : (x : ℂ) ∈ ball (p : ℂ) r) (hxp : x ≠ p) :
    schwarzChristoffelBoundary a e z₀ x =
      schwarzChristoffelPrevertexCoefficient a e p * log ((x : ℂ) - (p : ℂ)) + H x := by
  have hshift : Tendsto (fun z : ℂ => z - (p : ℂ))
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] ((x : ℂ) - (p : ℂ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz.le
  have hlog : Tendsto (fun z : ℂ => log (z - (p : ℂ)))
      (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (log ((x : ℂ) - (p : ℂ)))) := by
    rcases lt_or_gt_of_ne hxp with h | h
    · exact (continuousWithinAt_log_of_re_neg_of_im_zero
        (by simpa using sub_neg.mpr h) (by simp)).tendsto.comp hshift
    · exact (continuousAt_clog (Or.inl (by simpa using sub_pos.mpr h))).tendsto.comp
        (tendsto_nhdsWithin_iff.mp hshift).1
  apply schwarzChristoffelBoundary_eq_of_tendsto
  refine ((tendsto_const_nhds.mul hlog).add
    ((hH _ hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hx)] with z hz hzr
  exact (sub_eq_iff_eq_add'.mp (hF z ⟨hzr, hz⟩)).symm

/-- At a logarithmic prevertex, the two adjacent boundary sides have exactly the normalized
heights `0` and `π`, for a common target translation. The boundary map is continuous on the
punctured interval, and its normalized real coordinate tends to negative infinity from either
side. -/
theorem exists_boundary_levels_schwarzChristoffel_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    ∃ (c : ℂ) (r : ℝ), 0 < r ∧
      ContinuousOn (schwarzChristoffelBoundary a e z₀) (Ioo (p - r) (p + r) \ {p}) ∧
      (∀ x ∈ Ioo p (p + r),
        ((schwarzChristoffelBoundary a e z₀ x - c) /
          schwarzChristoffelPrevertexCoefficient a e p).im = 0) ∧
      (∀ x ∈ Ioo (p - r) p,
        ((schwarzChristoffelBoundary a e z₀ x - c) /
          schwarzChristoffelPrevertexCoefficient a e p).im = Real.pi) ∧
      Tendsto (fun x => ((schwarzChristoffelBoundary a e z₀ x - c) /
        schwarzChristoffelPrevertexCoefficient a e p).re) (𝓝[≠] p) atBot := by
  classical
  -- Continue the logarithmic remainder, and isolate the singular prevertex.
  obtain ⟨H, R, hR, hH, _, hF⟩ :=
    exists_analyticOnNhd_eq_schwarzChristoffelPrimitive_sub_log_of_sum_eq_neg_one a e z₀ p he
  have hsep : ∀ᶠ x in 𝓝 p, ∀ i, a i ≠ p → a i ≠ x := by
    apply eventually_all.mpr
    intro i
    by_cases hi : a i = p
    · simp [hi]
    · exact (eventually_ne_nhds (Ne.symm hi)).mono fun x hx _ => hx.symm
  have hpR : p ∈ Ioo (p - R) (p + R) := by constructor <;> linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hsep.and (isOpen_Ioo.mem_nhds hpR))
  have hnear {x : ℝ} (hx : |x - p| < r) :
      (x : ℂ) ∈ ball (p : ℂ) R ∧ ∀ i, a i ≠ p → a i ≠ x := by
    have h := hball (by simpa [Real.dist_eq] using hx)
    refine ⟨?_, h.1⟩
    rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [h.2.1, h.2.2]
  have hfree {x : ℝ} (hx : |x - p| < r) (hxp : x ≠ p) : ∀ i, a i ≠ x := by
    intro i
    by_cases hi : a i = p
    · simpa [hi] using hxp.symm
    · exact (hnear hx).2 i hi
  have hB {x : ℝ} (hx : |x - p| < r) (hxp : x ≠ p) :=
    boundary_eq_log_add a e z₀ p hH hF (hnear hx).1 hxp
  let C := schwarzChristoffelPrevertexCoefficient a e p
  have hC : C ≠ 0 := schwarzChristoffelPrevertexCoefficient_ne_zero a e p
  let N : ℝ → ℂ := fun x => (schwarzChristoffelBoundary a e z₀ x - H p) / C
  have hN {x : ℝ} (hx : |x - p| < r) (hxp : x ≠ p) :
      N x = log ((x : ℂ) - (p : ℂ)) + (H x - H p) / C := by
    dsimp only [N]
    rw [hB hx hxp]
    dsimp only [C] at hC ⊢
    field_simp
    ring
  have hrem : Tendsto (fun x : ℝ => (H x - H p) / C) (𝓝 p) (𝓝 0) := by
    simpa using (((hH _ (mem_ball_self hR)).continuousAt.comp
      continuous_ofReal.continuousAt).sub_const (H p)).div_const C
  have hright : ∀ i, e i ≠ 0 → a i ∉ Ioo p (p + r) := by
    intro i _ hi
    exact hfree (by rw [abs_of_pos (sub_pos.mpr hi.1)]; linarith [hi.2]) hi.1.ne' i rfl
  have hleft : ∀ i, e i ≠ 0 → a i ∉ Ioo (p - r) p := by
    intro i _ hi
    exact hfree (by rw [abs_of_neg (sub_neg.mpr hi.2)]; linarith [hi.1]) hi.2.ne i rfl
  -- Division by the leading coefficient makes both edge increments real.
  have hphase : (exp (schwarzChristoffelEdgeAngle a e p * I) / C).im = 0 := by
    dsimp only [C]
    rw [schwarzChristoffelPrevertexCoefficient_def, div_mul_eq_div_mul_one_div,
      div_self (exp_ne_zero _)]
    rw [← ofReal_one, ← ofReal_div]
    simp only [ofReal_one, one_mul, ofReal_im]
  have hphaseleft : (exp (schwarzChristoffelEdgeAngle a e (p - r) * I) / C).im = 0 := by
    have hangle := schwarzChristoffelEdgeAngle_sub_eq_pi_mul_exponent_sum_of_adjacent
      a e (by linarith) hleft
    rw [he] at hangle
    have haeq : schwarzChristoffelEdgeAngle a e (p - r) =
        schwarzChristoffelEdgeAngle a e p - Real.pi := by linarith
    rw [haeq, ofReal_sub, sub_mul, exp_sub, exp_pi_mul_I]
    simpa only [div_neg, div_one, neg_div, neg_im, neg_eq_zero] using hphase
  have hheight {l u x y : ℝ} (hf : ∀ i, e i ≠ 0 → a i ∉ Ioo l u)
      (hx : x ∈ Ioo l u) (hy : y ∈ Ioo l u)
      (hph : (exp (schwarzChristoffelEdgeAngle a e l * I) / C).im = 0) :
      (N x).im = (N y).im := by
    have h := congrArg (fun z : ℂ => (z / C).im)
      (schwarzChristoffelBoundary_sub_eq a e z₀ hf hx hy)
    have hxy : (schwarzChristoffelBoundary a e z₀ x / C).im =
        (schwarzChristoffelBoundary a e z₀ y / C).im := by
      simpa [sub_div, mul_div_assoc, mul_im, hph, sub_eq_zero] using h
    simpa only [N, sub_div, sub_im] using congrArg (fun t : ℝ => t - (H p / C).im) hxy
  -- The upper boundary values of the logarithm distinguish the two constant heights.
  have hlimright : Tendsto (fun x => (N x).im) (𝓝[>] p) (𝓝 0) := by
    refine ((continuous_im.tendsto _).comp
      (hrem.mono_left nhdsWithin_le_nhds)).congr' ?_
    have hinterval : ∀ᶠ x : ℝ in 𝓝[>] p, x ∈ Ioo p (p + r) :=
      Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hinterval] with x hx
    rw [hN (by rw [abs_of_pos (sub_pos.mpr hx.1)]; linarith [hx.2]) hx.1.ne']
    simp [log_im, ← ofReal_sub, arg_ofReal_of_nonneg (sub_pos.mpr hx.1).le]
  have hlimleft : Tendsto (fun x => (N x).im) (𝓝[<] p) (𝓝 Real.pi) := by
    have hlim : Tendsto (fun x : ℝ => ((H x - H p) / C).im) (𝓝[<] p) (𝓝 0) :=
      by simpa [Function.comp_def] using
        (continuous_im.tendsto _).comp (hrem.mono_left nhdsWithin_le_nhds)
    have hlim' : Tendsto (fun x : ℝ => Real.pi + ((H x - H p) / C).im)
        (𝓝[<] p) (𝓝 Real.pi) := by simpa using hlim.const_add Real.pi
    refine hlim'.congr' ?_
    have hinterval : ∀ᶠ x : ℝ in 𝓝[<] p, x ∈ Ioo (p - r) p :=
      Ioo_mem_nhdsLT (by linarith)
    filter_upwards [hinterval] with x hx
    rw [hN (by rw [abs_of_neg (sub_neg.mpr hx.2)]; linarith [hx.1]) hx.2.ne]
    have harg : arg ((x : ℂ) - (p : ℂ)) = Real.pi :=
      arg_eq_pi_iff.mpr ⟨by simpa using sub_neg.mpr hx.2, by simp⟩
    simp [log_im, harg]
  -- A constant height equals its one-sided limit; the real logarithm gives escape.
  refine ⟨H p, r, hr, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one a e z₀
      (fun x hx => ?_)
    have hxabs : |x - p| < r := by rw [abs_lt]; constructor <;> linarith [hx.1.1, hx.1.2]
    have hxp : x ≠ p := by simpa using hx.2
    simp [Finset.filter_eq_empty_iff.mpr (fun i _ => hfree hxabs hxp i)]
  · intro x hx
    apply tendsto_nhds_unique (l := 𝓝[>] p) (f := fun _ : ℝ => (N x).im) tendsto_const_nhds
    have hinterval : ∀ᶠ y in 𝓝[>] p, y ∈ Ioo p (p + r) :=
      Ioo_mem_nhdsGT (by linarith)
    exact hlimright.congr' (hinterval.mono fun y hy => (hheight hright hx hy hphase).symm)
  · intro x hx
    apply tendsto_nhds_unique (l := 𝓝[<] p) (f := fun _ : ℝ => (N x).im) tendsto_const_nhds
    have hinterval : ∀ᶠ y in 𝓝[<] p, y ∈ Ioo (p - r) p :=
      Ioo_mem_nhdsLT (by linarith)
    exact hlimleft.congr' (hinterval.mono fun y hy => (hheight hleft hx hy hphaseleft).symm)
  · have hlog := Real.tendsto_log_nhdsGT_zero.comp
      (by simpa [Real.norm_eq_abs] using tendsto_norm_sub_self_nhdsNE p)
    have hremre : Tendsto (fun x : ℝ => ((H x - H p) / C).re) (𝓝[≠] p) (𝓝 0) :=
      by simpa [Function.comp_def] using
        (continuous_re.tendsto _).comp (hrem.mono_left nhdsWithin_le_nhds)
    have hbot : Tendsto (fun x => (N x).re) (𝓝[≠] p) atBot := by
      refine (hlog.atBot_add hremre).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hr)] with x hxp hxr
      rw [hN (by simpa [Real.dist_eq] using hxr) (by simpa using hxp)]
      simp [log_re, Complex.norm_real, ← ofReal_sub]
    exact hbot

/-- **The boundary of a logarithmic end is a pair of strip edges.** After a translation and
division by the nonzero prevertex coefficient, sufficiently far to the left the boundary values
on a punctured interval about the prevertex are exactly the two lines at heights `0` and `π`.
No conditions on the other exponents or on boundary simplicity are needed. -/
theorem exists_mem_image_normalized_schwarzChristoffelBoundary_iff_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    ∃ (c : ℂ) (r R : ℝ), 0 < r ∧ ∀ w : ℂ, w.re < R →
      (w ∈ (fun x => (schwarzChristoffelBoundary a e z₀ x - c) /
        schwarzChristoffelPrevertexCoefficient a e p) '' (Ioo (p - r) (p + r) \ {p}) ↔
          w.im = 0 ∨ w.im = Real.pi) := by
  classical
  obtain ⟨c, r, hr, _, hlo, hhi, _⟩ :=
    exists_boundary_levels_schwarzChristoffel_of_sum_eq_neg_one a e z₀ p he
  let N : ℝ → ℂ := fun x => (schwarzChristoffelBoundary a e z₀ x - c) /
    schwarzChristoffelPrevertexCoefficient a e p
  have hlevels {x : ℝ} (hx : x ∈ Ioo (p - r) (p + r) \ {p}) :
      (N x).im = 0 ∨ (N x).im = Real.pi := by
    have hxp : x ≠ p := by simpa using hx.2
    rcases lt_or_gt_of_ne hxp with h | h
    · exact Or.inr (hhi x ⟨hx.1.1, h⟩)
    · exact Or.inl (hlo x ⟨h, hx.1.2⟩)
  -- Choose finite endpoints away from all prevertices, so the existing ray API applies.
  have hsep : ∀ᶠ x in 𝓝 p, ∀ i, a i ≠ p → a i ≠ x := by
    apply eventually_all.mpr
    intro i
    by_cases hi : a i = p
    · simp [hi]
    · exact (eventually_ne_nhds (Ne.symm hi)).mono fun x hx _ => hx.symm
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hsep
  have hfree {x : ℝ} (hx : |x - p| < δ) (hxp : x ≠ p) : ∀ i, a i ≠ x := by
    intro i
    by_cases hi : a i = p
    · simpa [hi] using hxp.symm
    · exact hball (by simpa [Real.dist_eq] using hx) i hi
  let qRight := p + min r δ / 2
  let qLeft := p - min r δ / 2
  have hqRight : p < qRight ∧ qRight < p + r := by
    dsimp [qRight]
    constructor <;> linarith [lt_min hr hδ, min_le_left r δ]
  have hqLeft : p - r < qLeft ∧ qLeft < p := by
    dsimp [qLeft]
    constructor <;> linarith [lt_min hr hδ, min_le_left r δ]
  have hright : Ioc p qRight ⊆ Ioo (p - r) (p + r) \ {p} := by
    intro x hx
    exact ⟨⟨by linarith [hx.1], hx.2.trans_lt hqRight.2⟩, by simpa using hx.1.ne'⟩
  have hleft : Ico qLeft p ⊆ Ioo (p - r) (p + r) \ {p} := by
    intro x hx
    exact ⟨⟨hqLeft.1.trans_le hx.1, by linarith [hx.2]⟩, by simpa using hx.2.ne⟩
  have hrightfree : ∀ i, e i ≠ 0 → a i ∉ Ioo p qRight := by
    intro i _ hx
    exact hfree (by
      rw [abs_of_pos (sub_pos.mpr hx.1)]
      dsimp [qRight] at hx
      linarith [hx.2, min_le_right r δ, lt_min hr hδ]) hx.1.ne' i rfl
  have hleftfree : ∀ i, e i ≠ 0 → a i ∉ Ioo qLeft p := by
    intro i _ hx
    exact hfree (by
      rw [abs_of_neg (sub_neg.mpr hx.2)]
      dsimp [qLeft] at hx
      linarith [hx.1, min_le_right r δ, lt_min hr hδ]) hx.2.ne i rfl
  have hsum {x : ℝ} (hx : |x - p| < δ) (hxp : x ≠ p) :
      -1 < ∑ i with a i = x, e i := by
    simp [Finset.filter_eq_empty_iff.mpr (fun i _ => hfree hx hxp i)]
  have hrightsum : -1 < ∑ i with a i = qRight, e i :=
    hsum (by
      rw [abs_of_pos (sub_pos.mpr hqRight.1)]
      dsimp [qRight]
      linarith [min_le_right r δ, lt_min hr hδ]) hqRight.1.ne'
  have hleftsum : -1 < ∑ i with a i = qLeft, e i :=
    hsum (by
      rw [abs_of_neg (sub_neg.mpr hqLeft.2)]
      dsimp [qLeft]
      linarith [min_le_right r δ, lt_min hr hδ]) hqLeft.2.ne
  let C := schwarzChristoffelPrevertexCoefficient a e p
  have hC : 0 < ‖C‖ := norm_pos_iff.mpr (schwarzChristoffelPrevertexCoefficient_ne_zero a e p)
  have hphase : exp (schwarzChristoffelEdgeAngle a e p * I) / C = (1 / ‖C‖ : ℝ) := by
    dsimp [C]
    rw [norm_schwarzChristoffelPrevertexCoefficient, schwarzChristoffelPrevertexCoefficient_def,
      div_mul_eq_div_mul_one_div, div_self (exp_ne_zero _)]
    simp
  have hphaseleft : exp (schwarzChristoffelEdgeAngle a e qLeft * I) / C =
      -(1 / ‖C‖ : ℝ) := by
    have hangle := schwarzChristoffelEdgeAngle_sub_eq_pi_mul_exponent_sum_of_adjacent
      a e hqLeft.2 hleftfree
    rw [he] at hangle
    have haeq : schwarzChristoffelEdgeAngle a e qLeft =
        schwarzChristoffelEdgeAngle a e p - Real.pi := by linarith
    rw [haeq, ofReal_sub, sub_mul, exp_sub, exp_pi_mul_I]
    simpa only [div_neg, div_one, neg_div] using congrArg Neg.neg hphase
  -- Normalize the two existing closed-ray formulas to obtain the real-coordinate tails.
  have hrightimage : Iic (N qRight).re ⊆ (fun x => (N x).re) '' Ioc p qRight := by
    intro y hy
    have hray := schwarzChristoffelBoundary_image_Ioc_eq_ray_of_left_sum_eq_neg_one
      a e z₀ hqRight.1 hrightfree he hrightsum
    have hmem : schwarzChristoffelBoundary a e z₀ qRight -
        (((N qRight).re - y) * ‖C‖ : ℝ) * exp (schwarzChristoffelEdgeAngle a e p * I) ∈
        schwarzChristoffelBoundary a e z₀ '' Ioc p qRight := by
      rw [hray]
      exact ⟨((N qRight).re - y) * ‖C‖, mul_nonneg (sub_nonneg.mpr hy) hC.le, rfl⟩
    obtain ⟨x, hx, hBx⟩ := hmem
    refine ⟨x, hx, ?_⟩
    have h := congrArg (fun z : ℂ => ((z - c) / C).re) hBx
    rw [sub_right_comm, sub_div (schwarzChristoffelBoundary a e z₀ qRight - c),
      mul_div_assoc, hphase] at h
    have hNx : (N x).re = (N qRight).re -
        ((N qRight).re - y) * ‖C‖ * (1 / ‖C‖) := by
      simpa only [sub_re, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero] using h
    rw [mul_assoc, mul_one_div_cancel hC.ne', mul_one] at hNx
    linarith
  have hleftimage : Iic (N qLeft).re ⊆ (fun x => (N x).re) '' Ico qLeft p := by
    intro y hy
    have hray := schwarzChristoffelBoundary_image_Ico_eq_ray_of_right_sum_eq_neg_one
      a e z₀ hqLeft.2 hleftfree hleftsum he
    have hmem : schwarzChristoffelBoundary a e z₀ qLeft +
        (((N qLeft).re - y) * ‖C‖ : ℝ) * exp (schwarzChristoffelEdgeAngle a e qLeft * I) ∈
        schwarzChristoffelBoundary a e z₀ '' Ico qLeft p := by
      rw [hray]
      exact ⟨((N qLeft).re - y) * ‖C‖, mul_nonneg (sub_nonneg.mpr hy) hC.le, rfl⟩
    obtain ⟨x, hx, hBx⟩ := hmem
    refine ⟨x, hx, ?_⟩
    have h := congrArg (fun z : ℂ => ((z - c) / C).re) hBx
    rw [add_sub_right_comm, add_div, mul_div_assoc, hphaseleft] at h
    have hNx : (N x).re = (N qLeft).re -
        ((N qLeft).re - y) * ‖C‖ * (1 / ‖C‖) := by
      simpa only [add_re, sub_re, mul_re, ofReal_re, ofReal_im,
        neg_re, neg_im, neg_zero, mul_zero, sub_zero, mul_neg, ← sub_eq_add_neg] using h
    rw [mul_assoc, mul_one_div_cancel hC.ne', mul_one] at hNx
    linarith
  refine ⟨c, r, min (N qRight).re (N qLeft).re, hr, fun w hw => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact hlevels hx
  · rintro (hwim | hwim)
    · obtain ⟨x, hx, hxre⟩ := hrightimage ((hw.trans_le (min_le_left _ _)).le)
      refine ⟨x, hright hx, Complex.ext hxre ?_⟩
      exact (hlo x ⟨hx.1, hx.2.trans_lt hqRight.2⟩).trans hwim.symm
    · obtain ⟨x, hx, hxre⟩ := hleftimage ((hw.trans_le (min_le_right _ _)).le)
      refine ⟨x, hleft hx, Complex.ext hxre ?_⟩
      exact (hhi x ⟨hqLeft.1.trans_le hx.1, hx.2⟩).trans hwim.symm

end TauCeti
