/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Asymptotic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex

/-!
# Corner asymptotics of the Schwarz--Christoffel map

At a prevertex `p` carrying total exponent `t > -1`, the Schwarz--Christoffel integrand is
asymptotic to `C * (z - p) ^ t`, where `C` is the nonzero prevertex coefficient.  This file
integrates that derivative asymptotic and identifies the first-order power law of the normalized
primitive:

`F z - F p ~ (C / (t + 1)) * (z - p) ^ (t + 1)`.

The limit is taken through the whole upper half-plane.  In particular, it records both the
vanishing order at the corner and its leading direction, information needed to identify the
boundary chain of a Schwarz--Christoffel map with a polygon.

## Main result

* `TauCeti.tendsto_schwarzChristoffelPrimitive_sub_vertex_div_cpow` -- the normalized primitive
  has the expected leading power at an integrable prevertex.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The error after subtracting the leading power from the Schwarz--Christoffel primitive at a
prevertex. -/
private def schwarzChristoffelCornerRemainder (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (j : ι) (z : ℂ) : ℂ :=
  schwarzChristoffelPrimitive a e z₀ z - schwarzChristoffelVertex a e z₀ j -
    schwarzChristoffelPrevertexCoefficient a e (a j) /
      ((∑ i with a i = a j, e i) + 1) *
        (z - (a j : ℂ)) ^ (((∑ i with a i = a j, e i) + 1 : ℝ) : ℂ)

/-- Inside the upper half-plane, the derivative of the corner remainder is the error in the
leading asymptotic of the integrand. -/
private theorem hasDerivAt_schwarzChristoffelCornerRemainder (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) {z : ℂ} (hz : z ∈ upperHalfPlaneSet)
    (he : -1 < ∑ i with a i = a j, e i) :
    HasDerivAt (schwarzChristoffelCornerRemainder a e z₀ j)
      (schwarzChristoffelIntegrand a e z - schwarzChristoffelPrevertexCoefficient a e (a j) *
        (z - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ)) z := by
  let T : ℝ := ∑ i with a i = a j, e i
  let C : ℂ := schwarzChristoffelPrevertexCoefficient a e (a j)
  have hT1 : (T : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by dsimp [T]; linarith : T + 1 ≠ 0)
  have hpow := ((hasDerivAt_id z).sub_const (a j : ℂ)).cpow_const
    (c := ((T + 1 : ℝ) : ℂ))
    (sub_ofReal_mem_slitPlane_of_im_pos hz (a j))
  have hpow' : HasDerivAt
      (fun z : ℂ => (z - (a j : ℂ)) ^ ((T : ℂ) + 1))
      (((T : ℂ) + 1) * (z - (a j : ℂ)) ^ (T : ℂ)) z := by
    simpa only [id_eq, ofReal_add, ofReal_one, add_sub_cancel_right, mul_one] using hpow
  have hmodel : HasDerivAt
      (fun z : ℂ => C / ((T : ℂ) + 1) * (z - (a j : ℂ)) ^ ((T : ℂ) + 1))
      (C * (z - (a j : ℂ)) ^ (T : ℂ)) z := by
    have hscaled := hpow'.const_mul (C / ((T : ℂ) + 1))
    apply hscaled.congr_deriv
    field_simp
  have hsub := ((hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).sub_const
    (schwarzChristoffelVertex a e z₀ j)).sub hmodel
  refine hsub.congr_of_eventuallyEq (.of_forall fun y => ?_)
  simp only [schwarzChristoffelCornerRemainder, Pi.sub_apply, T, C, ofReal_add, ofReal_one]

/-- The corner remainder tends to zero at its prevertex. -/
private theorem tendsto_schwarzChristoffelCornerRemainder (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) (he : -1 < ∑ i with a i = a j, e i) :
    Tendsto (schwarzChristoffelCornerRemainder a e z₀ j)
      (𝓝[upperHalfPlaneSet] (a j : ℂ)) (𝓝 0) := by
  let T : ℝ := ∑ i with a i = a j, e i
  have hT1 : (T : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (by dsimp [T]; linarith : T + 1 ≠ 0)
  have hpow : Tendsto
      (fun z : ℂ => (z - (a j : ℂ)) ^ (((∑ i with a i = a j, e i) + 1 : ℝ) : ℂ))
      (𝓝 (a j : ℂ)) (𝓝 0) := by
    have hcont := Complex.continuousAt_cpow_const_of_re_pos
      (z := (0 : ℂ)) (w := (T : ℂ) + 1) (by simp)
        (by simp only [add_re, ofReal_re, one_re]; dsimp [T]; linarith)
    have hsub : Tendsto (fun z : ℂ => z - (a j : ℂ)) (𝓝 (a j : ℂ)) (𝓝 0) := by
      have hid : Tendsto (fun z : ℂ => z) (𝓝 (a j : ℂ)) (𝓝 (a j : ℂ)) := tendsto_id
      have hc : Tendsto (fun _ : ℂ => (a j : ℂ)) (𝓝 (a j : ℂ)) (𝓝 (a j : ℂ)) :=
        tendsto_const_nhds
      simpa only [sub_self] using hid.sub hc
    have ht := hcont.tendsto.comp hsub
    rw [Complex.zero_cpow hT1] at ht
    have ht' : Tendsto (fun z : ℂ => (z - (a j : ℂ)) ^ ((T : ℂ) + 1))
        (𝓝 (a j : ℂ)) (𝓝 0) :=
      ht.congr' (.of_forall fun _ => rfl)
    simpa only [T, ofReal_add, ofReal_one] using ht'
  change Tendsto (fun z => schwarzChristoffelPrimitive a e z₀ z -
    schwarzChristoffelVertex a e z₀ j -
      schwarzChristoffelPrevertexCoefficient a e (a j) /
        ((∑ i with a i = a j, e i) + 1) *
          (z - (a j : ℂ)) ^ (((∑ i with a i = a j, e i) + 1 : ℝ) : ℂ))
    (𝓝[upperHalfPlaneSet] (a j : ℂ)) (𝓝 0)
  convert ((tendsto_schwarzChristoffelPrimitive a e z₀ j he).sub tendsto_const_nhds).sub
    ((tendsto_const_nhds.mul hpow).mono_left nhdsWithin_le_nhds) using 1
  all_goals simp

/-- The derivative of the corner remainder is little-o of the singular power. -/
private theorem tendsto_schwarzChristoffelCornerRemainder_deriv_div_cpow
    (a e : ι → ℝ) (j : ι) :
    Tendsto
      (fun z => (schwarzChristoffelIntegrand a e z -
          schwarzChristoffelPrevertexCoefficient a e (a j) *
            (z - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ)) /
        (z - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ))
      (𝓝[upperHalfPlaneSet] (a j : ℂ)) (𝓝 0) := by
  have h := (tendsto_schwarzChristoffelIntegrand_div_cpow a e (a j)).sub
    (tendsto_const_nhds : Tendsto
      (fun _ : ℂ => schwarzChristoffelPrevertexCoefficient a e (a j))
      (𝓝[upperHalfPlaneSet] (a j : ℂ))
      (𝓝 (schwarzChristoffelPrevertexCoefficient a e (a j))))
  have heq : (fun z => (schwarzChristoffelIntegrand a e z -
          schwarzChristoffelPrevertexCoefficient a e (a j) *
            (z - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ)) /
        (z - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ)) =ᶠ[
      𝓝[upperHalfPlaneSet] (a j : ℂ)]
      (fun z => schwarzChristoffelIntegrand a e z /
        (z - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ) -
          schwarzChristoffelPrevertexCoefficient a e (a j)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hpow := sub_cpow_ne_zero_of_im_pos hz (a j)
      (∑ i with a i = a j, e i)
    field_simp
  simpa only [sub_self] using h.congr' heq.symm

/-- A radial segment estimate for the corner remainder. -/
private theorem norm_schwarzChristoffelCornerRemainder_sub_le (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) {ε ρ : ℝ}
    (he : -1 < ∑ i with a i = a j, e i) (hε : 0 ≤ ε)
    (hbd : ∀ y ∈ Metric.ball (a j : ℂ) ρ ∩ upperHalfPlaneSet,
      ‖schwarzChristoffelIntegrand a e y -
        schwarzChristoffelPrevertexCoefficient a e (a j) *
          (y - (a j : ℂ)) ^ ((∑ i with a i = a j, e i : ℝ) : ℂ)‖
        ≤ ε * dist y (a j : ℂ) ^ ∑ i with a i = a j, e i)
    {z : ℂ} (hz : z ∈ Metric.ball (a j : ℂ) ρ ∩ upperHalfPlaneSet)
    {δ : ℝ} (hδ : δ ∈ Ioo 0 1) :
    ‖schwarzChristoffelCornerRemainder a e z₀ j z -
        schwarzChristoffelCornerRemainder a e z₀ j
          ((a j : ℂ) + (δ : ℂ) * (z - (a j : ℂ)))‖
      ≤ ε / ((∑ i with a i = a j, e i) + 1) *
        ‖z - (a j : ℂ)‖ ^ ((∑ i with a i = a j, e i) + 1) := by
  let p : ℂ := (a j : ℂ)
  let T : ℝ := ∑ i with a i = a j, e i
  let C : ℂ := schwarzChristoffelPrevertexCoefficient a e (a j)
  let R : ℂ → ℂ := schwarzChristoffelCornerRemainder a e z₀ j
  let γ : ℝ → ℂ := fun t => p + (t : ℂ) * (z - p)
  let B : ℝ → ℝ := fun t => ε * ‖z - p‖ ^ (T + 1) * t ^ T
  have hz_ne : z ≠ p := by
    intro h
    have := hz.2
    rw [h] at this
    simp [p] at this
  have hnorm : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne)
  have hT1 : 0 < T + 1 := by dsimp [T]; linarith
  have hγmem : ∀ t ∈ Icc δ 1, γ t ∈ Metric.ball p ρ ∩ upperHalfPlaneSet := by
    intro t ht
    have ht0 : 0 < t := hδ.1.trans_le ht.1
    constructor
    · simp only [Metric.mem_ball, γ, dist_eq_norm]
      have ht1 : t ≤ 1 := ht.2
      calc
        ‖p + (t : ℂ) * (z - p) - p‖ = t * ‖z - p‖ := by
          rw [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        _ ≤ ‖z - p‖ := by nlinarith
        _ < ρ := by simpa [p, dist_eq_norm] using Metric.mem_ball.mp hz.1
    · have hzim : 0 < z.im := hz.2
      simpa [γ, p] using mul_pos ht0 hzim
  have hγderiv : ∀ t ∈ Icc δ 1, HasDerivAt (fun t : ℝ => R (γ t))
      ((z - p) * (schwarzChristoffelIntegrand a e (γ t) - C *
        (γ t - p) ^ (T : ℂ))) t := by
    intro t ht
    have hinner : HasDerivAt γ (z - p) t := by
      simpa [γ] using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (z - p)).const_add p
    have houter := hasDerivAt_schwarzChristoffelCornerRemainder a e z₀ j (hγmem t ht).2 he
    simpa [R, p, T, C, Function.comp_def] using houter.scomp t hinner
  have hderiv_le : ∀ t ∈ Icc δ 1, ‖deriv (fun t : ℝ => R (γ t)) t‖ ≤ B t := by
    intro t ht
    rw [(hγderiv t ht).deriv, norm_mul]
    have ht0 : 0 < t := hδ.1.trans_le ht.1
    have hbound := hbd (γ t) (by simpa [p] using hγmem t ht)
    have hdist : dist (γ t) p = t * ‖z - p‖ := by
      simp only [γ, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real,
        Real.norm_eq_abs, abs_of_pos ht0]
    rw [hdist, Real.mul_rpow ht0.le hnorm.le] at hbound
    calc
      ‖z - p‖ * ‖schwarzChristoffelIntegrand a e (γ t) - C *
          (γ t - p) ^ (T : ℂ)‖
          ≤ ‖z - p‖ * (ε * (t ^ T * ‖z - p‖ ^ T)) :=
            mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ = B t := by
        simp only [B, Real.rpow_add hnorm, Real.rpow_one]
        ring
  have hcont : ContinuousOn (fun t : ℝ => R (γ t)) (Icc δ 1) :=
    fun t ht => (hγderiv t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => R (γ t)) (Ioo δ 1) :=
    fun t ht => (hγderiv t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  have hBi : IntervalIntegrable B volume δ 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδ.2.le]
    have htcont : ContinuousOn (fun t : ℝ => t ^ T) (Icc δ 1) :=
      continuousOn_id.rpow_const fun t ht => Or.inl
        (ne_of_gt (hδ.1.trans_le ht.1))
    exact (continuousOn_const.mul continuousOn_const).mul htcont
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le hδ.2.le hcont hdiff
    (.of_forall fun t ht => hderiv_le t (Ioo_subset_Icc_self ht)) hBi
  have hBint : (∫ t in δ..1, B t) ≤ ε / (T + 1) * ‖z - p‖ ^ (T + 1) := by
    simp only [B]
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by simpa [T] using he)), Real.one_rpow]
    have hδpow : 0 ≤ δ ^ (T + 1) := Real.rpow_nonneg hδ.1.le _
    have hden : 0 < T + 1 := hT1
    calc
      ε * ‖z - p‖ ^ (T + 1) * ((1 - δ ^ (T + 1)) / (T + 1))
          ≤ ε * ‖z - p‖ ^ (T + 1) * (1 / (T + 1)) := by
            gcongr
            linarith
      _ = ε / (T + 1) * ‖z - p‖ ^ (T + 1) := by ring
  simpa [γ, R, p, T] using hmain.trans hBint

/-- The corner remainder is bounded by an arbitrarily small multiple of the leading power. -/
private theorem eventually_norm_schwarzChristoffelCornerRemainder_le (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) (he : -1 < ∑ i with a i = a j, e i)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝[upperHalfPlaneSet] (a j : ℂ),
      ‖schwarzChristoffelCornerRemainder a e z₀ j z‖ ≤
        ε / ((∑ i with a i = a j, e i) + 1) *
          ‖z - (a j : ℂ)‖ ^ ((∑ i with a i = a j, e i) + 1) := by
  let p : ℂ := (a j : ℂ)
  let T : ℝ := ∑ i with a i = a j, e i
  let C : ℂ := schwarzChristoffelPrevertexCoefficient a e (a j)
  let R : ℂ → ℂ := schwarzChristoffelCornerRemainder a e z₀ j
  let Q : ℂ → ℂ := fun z =>
    (schwarzChristoffelIntegrand a e z - C * (z - p) ^ (T : ℂ)) /
      (z - p) ^ (T : ℂ)
  have hQ : Tendsto Q (𝓝[upperHalfPlaneSet] p) (𝓝 0) := by
    simpa [Q, p, T, C] using
      tendsto_schwarzChristoffelCornerRemainder_deriv_div_cpow a e j
  have hev : ∀ᶠ y in 𝓝[upperHalfPlaneSet] p, ‖Q y‖ < ε := by
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp hQ ε hε
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  have hbd : ∀ y ∈ Metric.ball p ρ ∩ upperHalfPlaneSet,
      ‖schwarzChristoffelIntegrand a e y - C * (y - p) ^ (T : ℂ)‖
        ≤ ε * dist y p ^ T := by
    intro y hy
    have hqy : ‖Q y‖ < ε := hρsub hy
    have hpow : (y - p) ^ (T : ℂ) ≠ 0 := by
      simpa [p] using sub_cpow_ne_zero_of_im_pos hy.2 (a j) T
    have herr : schwarzChristoffelIntegrand a e y - C * (y - p) ^ (T : ℂ) =
        Q y * (y - p) ^ (T : ℂ) := by
      simp only [Q]
      field_simp
    rw [herr, norm_mul, Complex.norm_cpow_real, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_right hqy.le (Real.rpow_nonneg dist_nonneg _)
  have hball : ∀ᶠ z in 𝓝[upperHalfPlaneSet] p, z ∈ Metric.ball p ρ :=
    mem_inf_of_left (Metric.ball_mem_nhds p hρ)
  filter_upwards [hball, self_mem_nhdsWithin] with z hzball hzU
  have hz : z ∈ Metric.ball p ρ ∩ upperHalfPlaneSet := ⟨hzball, hzU⟩
  let γ : ℝ → ℂ := fun δ => p + (δ : ℂ) * (z - p)
  have hγ : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[upperHalfPlaneSet] p) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt γ (0 : ℝ) := by fun_prop
      have ht := hcont.tendsto.mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from inf_le_left)
      simpa [γ] using ht
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hzim : 0 < z.im := hzU
      simpa [γ, p] using mul_pos hδ hzim
  have hRγ : Tendsto (fun δ => R (γ δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact (tendsto_schwarzChristoffelCornerRemainder a e z₀ j he).comp hγ
  have hnormlim : Tendsto (fun δ => ‖R z - R (γ δ)‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖R z‖) := by
    simpa using (tendsto_const_nhds.sub hRγ).norm
  have hle : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ‖R z - R (γ δ)‖ ≤ ε / (T + 1) * ‖z - p‖ ^ (T + 1) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds one_pos).filter_mono inf_le_left] with δ hδ0 hδ1
    simpa [R, γ, p, T, C] using
      norm_schwarzChristoffelCornerRemainder_sub_le a e z₀ j he hε.le hbd hz
        ⟨hδ0, hδ1⟩
  simpa [R, p, T] using le_of_tendsto hnormlim hle

/-- **Leading corner asymptotic of the Schwarz--Christoffel primitive.**  At a prevertex whose
total exponent `t` is greater than `-1`, subtracting its boundary vertex and dividing by
`(z - p) ^ (t + 1)` tends, through the whole upper half-plane, to the integrand's nonzero leading
coefficient divided by `t + 1`.  Coincident prevertices contribute through the sum of all their
exponents at `p`.

Thus the primitive has the expected power law
`F z - F p ~ (C / (t + 1)) * (z - p) ^ (t + 1)` at the corner. -/
theorem tendsto_schwarzChristoffelPrimitive_sub_vertex_div_cpow (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (j : ι) (he : -1 < ∑ i with a i = a j, e i) :
    Tendsto
      (fun z => (schwarzChristoffelPrimitive a e z₀ z -
          schwarzChristoffelVertex a e z₀ j) /
        (z - (a j : ℂ)) ^ (((∑ i with a i = a j, e i) + 1 : ℝ) : ℂ))
      (𝓝[upperHalfPlaneSet] (a j : ℂ))
      (𝓝 (schwarzChristoffelPrevertexCoefficient a e (a j) /
        ((∑ i with a i = a j, e i) + 1))) := by
  let p : ℂ := (a j : ℂ)
  let T : ℝ := ∑ i with a i = a j, e i
  let C : ℂ := schwarzChristoffelPrevertexCoefficient a e (a j)
  let R : ℂ → ℂ := schwarzChristoffelCornerRemainder a e z₀ j
  have hT1 : 0 < T + 1 := by dsimp [T]; linarith
  have hRdiv : Tendsto
      (fun z => R z / (z - p) ^ ((T + 1 : ℝ) : ℂ))
      (𝓝[upperHalfPlaneSet] p) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set ε : ℝ := η * (T + 1) / 2 with hεdef
    have hε : 0 < ε := by positivity
    have hev := eventually_norm_schwarzChristoffelCornerRemainder_le a e z₀ j he hε
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hzU
    have hz_ne : z ≠ p := by
      intro h
      rw [h] at hzU
      simp [p] at hzU
    have hnorm : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne)
    have hpow : 0 < ‖z - p‖ ^ (T + 1) := Real.rpow_pos_of_pos hnorm _
    rw [dist_zero_right, norm_div, Complex.norm_cpow_real]
    calc
      ‖R z‖ / ‖z - p‖ ^ (T + 1)
          ≤ (ε / (T + 1) * ‖z - p‖ ^ (T + 1)) /
              ‖z - p‖ ^ (T + 1) := by
            exact div_le_div_of_nonneg_right (by simpa [R, p, T] using hz) hpow.le
      _ = η / 2 := by
        rw [mul_div_cancel_right₀ _ hpow.ne']
        rw [hεdef]
        field_simp [hT1.ne']
      _ < η := half_lt_self hη
  have hlim := hRdiv.add (tendsto_const_nhds : Tendsto (fun _ : ℂ => C / (T + 1))
    (𝓝[upperHalfPlaneSet] p) (𝓝 (C / (T + 1))))
  have heq : (fun z => R z / (z - p) ^ ((T + 1 : ℝ) : ℂ) + C / (T + 1)) =ᶠ[
      𝓝[upperHalfPlaneSet] p]
      (fun z => (schwarzChristoffelPrimitive a e z₀ z -
          schwarzChristoffelVertex a e z₀ j) /
        (z - (a j : ℂ)) ^ (((∑ i with a i = a j, e i) + 1 : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hpow := sub_cpow_ne_zero_of_im_pos hz (a j) (T + 1)
    have hpow' : (z - (a j : ℂ)) ^ ((T : ℂ) + 1) ≠ 0 := by
      simpa only [ofReal_add, ofReal_one] using hpow
    simp only [R, schwarzChristoffelCornerRemainder, p, T, C, ofReal_add, ofReal_one]
    rw [sub_div, mul_div_cancel_right₀ _ hpow']
    ring
  simpa [p, T, C] using hlim.congr' heq

end TauCeti
