/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Log

/-!
# Strip bounds near logarithmic Schwarz--Christoffel ends

At a finite prevertex with total exponent `-1`, translating and scaling the primitive by its
logarithmic coefficient makes its leading term `log (z - p)`. The imaginary part of this
logarithm lies between `0` and `π` in the upper half-plane. The holomorphic remainder tends to
zero after the corresponding target translation, so a sufficiently small upper half-disc maps
into any prescribed enlargement of that horizontal strip. This local estimate is useful when
identifying polygonal images with several ends.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Near a logarithmic prevertex, the normalized primitive lies in any prescribed enlargement
of the horizontal strip of height `π`, after a suitable target translation. -/
theorem exists_eventually_im_normalized_schwarzChristoffelPrimitive_mem_Ioo_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℂ, ∀ᶠ z in 𝓝[upperHalfPlaneSet] (p : ℂ),
      ((schwarzChristoffelPrimitive a e z₀ z - c) /
        schwarzChristoffelPrevertexCoefficient a e p).im ∈ Ioo (-ε) (Real.pi + ε) := by
  obtain ⟨H, r, hr, hH, _, hformula⟩ :=
    exists_analyticOnNhd_eq_schwarzChristoffelPrimitive_sub_log_of_sum_eq_neg_one
      a e z₀ p he
  let C := schwarzChristoffelPrevertexCoefficient a e p
  have hC : C ≠ 0 := schwarzChristoffelPrevertexCoefficient_ne_zero a e p
  have hrem : Tendsto (fun z : ℂ => ((H z - H (p : ℂ)) / C).im)
      (𝓝[upperHalfPlaneSet] (p : ℂ)) (𝓝 0) := by
    have hHcont := (hH _ (Metric.mem_ball_self hr)).continuousAt
    have hcont : ContinuousAt (fun z : ℂ => ((H z - H (p : ℂ)) / C).im) (p : ℂ) :=
      Complex.continuous_im.continuousAt.comp (hHcont.sub continuousAt_const |>.div_const C)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (p : ℂ),
      |((H z - H (p : ℂ)) / C).im| < ε :=
    by simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hrem) ε hε
  refine ⟨H (p : ℂ), ?_⟩
  filter_upwards [hsmall, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (p : ℂ) hr)] with z hsmall hzupper hzball
  have him : 0 < z.im := hzupper
  have hshift : z - (p : ℂ) ∈ upperHalfPlaneSet := by
    simpa using him
  have harg : (log (z - (p : ℂ))).im ∈ Ioo (0 : ℝ) Real.pi :=
    bijOn_log_upperHalfPlaneSet.1 hshift
  have hdecomp : (schwarzChristoffelPrimitive a e z₀ z - H (p : ℂ)) / C =
      log (z - (p : ℂ)) + (H z - H (p : ℂ)) / C := by
    rw [← hformula z ⟨hzball, hzupper⟩]
    field_simp [hC]
    ring
  rw [hdecomp, add_im]
  constructor
  · have := harg.1
    have := abs_lt.mp hsmall
    linarith
  · have := harg.2
    have := abs_lt.mp hsmall
    linarith

end TauCeti
