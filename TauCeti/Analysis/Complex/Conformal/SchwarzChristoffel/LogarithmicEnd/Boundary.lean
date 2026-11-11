/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Basic

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
  obtain ⟨H, R, hR, hH, hsym, hF⟩ :=
    exists_analyticOnNhd_eq_schwarzChristoffelPrimitive_sub_log_of_sum_eq_neg_one a e z₀ p he
  have hsep : ∀ᶠ x in 𝓝 p, ∀ i, a i ≠ p → a i ≠ x := eventually_all.mpr fun i =>
    eventually_imp_distrib_left.mpr fun hi =>
      (eventually_ne_nhds (Ne.symm hi)).mono fun _ h => h.symm
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hsep.and (isOpen_Ioo.mem_nhds (show p ∈ Ioo (p - R) (p + R) by constructor <;> linarith)))
  have hnear {x : ℝ} (hx : |x - p| < r) :
      (x : ℂ) ∈ ball (p : ℂ) R ∧ ∀ i, a i ≠ p → a i ≠ x := by
    have h := hball (by simpa [Real.dist_eq] using hx)
    refine ⟨?_, h.1⟩
    rw [mem_ball, Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [h.2.1, h.2.2]
  let C := schwarzChristoffelPrevertexCoefficient a e p
  have hC : C ≠ 0 := schwarzChristoffelPrevertexCoefficient_ne_zero a e p
  let N : ℝ → ℂ := fun x => (schwarzChristoffelBoundary a e z₀ x - H p) / C
  have hN {x : ℝ} (hx : |x - p| < r) (hxp : x ≠ p) :
      N x = log ((x : ℂ) - (p : ℂ)) + (H x - H p) / C := by
    dsimp only [N]
    rw [boundary_eq_log_add a e z₀ p hH hF (hnear hx).1 hxp, add_sub_assoc, add_div,
      mul_div_cancel_left₀ _ hC]
  -- The remainder is real on the real axis, so the height of `N` is that of the logarithm.
  have hNim {x : ℝ} (hx : |x - p| < r) (hxp : x ≠ p) :
      (N x).im = arg ((x : ℂ) - (p : ℂ)) := by
    rw [hN hx hxp, add_im, log_im, Complex.conj_eq_iff_im.mp
      (by simpa only [Complex.conj_ofReal] using (hsym x (hnear hx).1).symm), add_zero]
  refine ⟨H p, r, hr, ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · refine continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one a e z₀
      fun x hx => ?_
    have h := (hnear (x := x) (by rw [abs_lt]; constructor <;> linarith [hx.1.1, hx.1.2])).2
    have hxp : x ≠ p := by simpa using hx.2
    simp [Finset.filter_eq_empty_iff.mpr fun i _ (hix : a i = x) =>
      h i (fun hip => hxp (hix.symm.trans hip)) hix]
  · refine (hNim (by rw [abs_of_pos (sub_pos.mpr hx.1)]; linarith [hx.2]) hx.1.ne').trans ?_
    rw [← ofReal_sub, arg_ofReal_of_nonneg (sub_pos.mpr hx.1).le]
  · refine (hNim (by rw [abs_of_neg (sub_neg.mpr hx.2)]; linarith [hx.1]) hx.2.ne).trans ?_
    exact arg_eq_pi_iff.mpr ⟨by simpa using sub_neg.mpr hx.2, by simp⟩
  · have hlog := Real.tendsto_log_nhdsGT_zero.comp
      (by simpa [Real.norm_eq_abs] using tendsto_norm_sub_self_nhdsNE p)
    have hremre : Tendsto (fun x : ℝ => ((H x - H p) / C).re) (𝓝[≠] p) (𝓝 0) := by
      simpa [Function.comp_def] using (continuous_re.tendsto _).comp
        ((((hH _ (mem_ball_self hR)).continuousAt.comp continuous_ofReal.continuousAt).sub_const
          (H p)).div_const C |>.mono_left nhdsWithin_le_nhds)
    -- restate the goal in terms of the local abbreviation `N` (a `let`, so definitionally equal)
    change Tendsto (fun x => (N x).re) _ atBot
    refine (hlog.atBot_add hremre).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hr)] with x hxp hxr
    rw [hN (by simpa [Real.dist_eq] using hxr) (by simpa using hxp)]
    simp [log_re, Complex.norm_real, ← ofReal_sub]

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
  obtain ⟨c, r, hr, hcont, hlo, hhi, hbot⟩ :=
    exists_boundary_levels_schwarzChristoffel_of_sum_eq_neg_one a e z₀ p he
  let N : ℝ → ℂ := fun x => (schwarzChristoffelBoundary a e z₀ x - c) /
    schwarzChristoffelPrevertexCoefficient a e p
  have hNcont : ContinuousOn (fun x => (N x).re) (Ioo (p - r) (p + r) \ {p}) :=
    continuous_re.comp_continuousOn ((hcont.sub continuousOn_const).div_const _)
  have hsub {l u : ℝ} (hl : p - r < l) (hu : u < p + r) (hp : p ∉ Icc l u) :
      Icc l u ⊆ Ioo (p - r) (p + r) \ {p} :=
    fun x hx => ⟨⟨hl.trans_le hx.1, hx.2.trans_lt hu⟩, fun h => hp (by rwa [← h])⟩
  -- The real coordinate tends to `-∞` at `p`, so the intermediate value theorem between a point
  -- near `p` and a fixed point on each side covers every real part below a threshold.
  refine ⟨c, r, min (N (p + r / 2)).re (N (p - r / 2)).re, hr, fun w hw => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    rcases lt_or_gt_of_ne (show x ≠ p by simpa using hx.2) with h | h
    · exact Or.inr (hhi x ⟨hx.1.1, h⟩)
    · exact Or.inl (hlo x ⟨h, hx.1.2⟩)
  · rintro (hwim | hwim)
    · obtain ⟨l, ⟨hpl, hlu⟩, hlw⟩ := (Filter.Eventually.and
        (Ioo_mem_nhdsGT (by linarith : p < p + r / 2))
        ((hbot.mono_left (nhdsGT_le_nhdsNE p)).eventually (eventually_lt_atBot w.re))).exists
      obtain ⟨x, hx, hxw⟩ := intermediate_value_Icc hlu.le
        (hNcont.mono (hsub (by linarith) (by linarith) fun h => hpl.not_ge h.1))
        ⟨hlw.le, (hw.trans_le (min_le_left _ _)).le⟩
      refine ⟨x, hsub (by linarith) (by linarith) (fun h => hpl.not_ge h.1) hx,
        Complex.ext hxw ((hlo x ⟨hpl.trans_le hx.1, by linarith [hx.2]⟩).trans hwim.symm)⟩
    · obtain ⟨u, ⟨hlu, hup⟩, huw⟩ := (Filter.Eventually.and
        (Ioo_mem_nhdsLT (by linarith : p - r / 2 < p))
        ((hbot.mono_left (nhdsLT_le_nhdsNE p)).eventually (eventually_lt_atBot w.re))).exists
      obtain ⟨x, hx, hxw⟩ := intermediate_value_Icc' hlu.le
        (hNcont.mono (hsub (by linarith) (by linarith) fun h => hup.not_ge h.2))
        ⟨huw.le, (hw.trans_le (min_le_right _ _)).le⟩
      refine ⟨x, hsub (by linarith) (by linarith) (fun h => hup.not_ge h.2) hx,
        Complex.ext hxw ((hhi x ⟨by linarith [hx.1], hx.2.trans_lt hup⟩).trans hwim.symm)⟩

end TauCeti
