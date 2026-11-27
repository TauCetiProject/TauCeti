/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential

/-!
# Nontangential approach to the real axis

A function `u` on the upper half-plane has *nontangential limit* `L` at `x ∈ ℝ`, for the aperture
`α`, when `u z → L` as `z → x` inside the cone `Γ^α_∞(x) = {z : 0 < Im z, |Re z - x| < α Im z}`.
The filter of this approach is `TauCeti.nontangentialFilter α x = 𝓝[Γ^α_∞(x)] x`, so the
nontangential limit is `Tendsto u (nontangentialFilter α x) (𝓝 L)`.

The truncated cones `Γ^α_h(x)`, `0 < h`, form a basis of this filter
(`TauCeti.nontangentialFilter_hasBasis`). The filter grows with the aperture, so a nontangential
limit for one aperture is one for every smaller aperture (`TauCeti.nontangentialFilter_mono`).
A ray `(x + ct) + it`, `t → 0⁺`, with `|c| < α` is a nontangential approach
(`TauCeti.tendsto_ray_nontangentialFilter`). In particular, for a positive aperture the vertical
approach `x + it` is nontangential (`TauCeti.tendsto_vertical_nontangentialFilter`), so a
nontangential limit is also a vertical limit and the filter is nontrivial.

## Main definitions

* `TauCeti.nontangentialFilter`: the filter of nontangential approach to `x` with aperture `α`.

## Main results

* `TauCeti.nontangentialFilter_hasBasis`: the cones `Γ^α_h(x)`, `0 < h`, form a basis.
* `TauCeti.nontangentialFilter_mono`: the filter is monotone in the aperture.
* `TauCeti.nontangentialFilter_le_nhds`, `TauCeti.tendsto_im_nontangentialFilter`: nontangential
  approach to `x` is approach to `x`, so `Im z → 0`.
* `TauCeti.tendsto_ray_nontangentialFilter`: straight-line approach inside the cone is
  nontangential; in particular so is vertical approach
  (`TauCeti.tendsto_vertical_nontangentialFilter`).

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §4.
* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. **200**
  (2024), Section 2.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter Metric Set Topology

open scoped ENNReal

/-- The filter of **nontangential approach** to `x ∈ ℝ` with aperture `α`: the neighbourhood
filter of `x` within the cone `Γ^α_∞(x) = {z : 0 < Im z, |Re z - x| < α Im z}`. A function `u` has
nontangential limit `L` at `x` when `Tendsto u (nontangentialFilter α x) (𝓝 L)`. -/
def nontangentialFilter (α x : ℝ) : Filter ℂ :=
  𝓝[nontangentialCone α ⊤ x] (x : ℂ)

/-- The defining formula of `TauCeti.nontangentialFilter`. -/
theorem nontangentialFilter_def (α x : ℝ) :
    nontangentialFilter α x = 𝓝[nontangentialCone α ⊤ x] (x : ℂ) :=
  (rfl)

/-- **The truncated cones form a basis of the nontangential filter.** -/
theorem nontangentialFilter_hasBasis (α x : ℝ) :
    (nontangentialFilter α x).HasBasis (fun h : ℝ≥0∞ => 0 < h)
      (fun h => nontangentialCone α h x) := by
  rw [nontangentialFilter_def]
  refine (nhdsWithin_hasBasis nhds_basis_ball _).to_hasBasis (fun ε hε => ?_) (fun h hh => ?_)
  · refine ⟨ENNReal.ofReal (ε / (|α| + 1)), ENNReal.ofReal_pos.2 (by positivity),
      fun z hz => ⟨?_, ?_⟩⟩
    · rw [mem_ball]
      refine (dist_lt_of_mem_nontangentialCone hz).trans_le ?_
      have hz' := mem_nontangentialCone.1 hz
      have him : z.im ≤ ε / (|α| + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz'.1.le).1 hz'.2.2 |>.le
      calc (|α| + 1) * z.im ≤ (|α| + 1) * (ε / (|α| + 1)) := by gcongr
        _ = ε := by field_simp
    · exact nontangentialCone_mono le_rfl le_top x hz
  · obtain ⟨r, -, hr0, hrh⟩ := ENNReal.lt_iff_exists_real_btwn.1 hh
    refine ⟨r, ENNReal.ofReal_pos.1 hr0, fun z ⟨hzb, hz⟩ => ?_⟩
    have hz' := mem_nontangentialCone.1 hz
    refine mem_nontangentialCone.2 ⟨hz'.1, hz'.2.1, ?_⟩
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrh
    calc z.im = |(z - x).im| := by simp [abs_of_pos hz'.1]
      _ ≤ ‖z - x‖ := abs_im_le_norm _
      _ ≤ r := (mem_ball_iff_norm.1 hzb).le

/-- A truncated cone `Γ^α_h(x)` with positive height belongs to the nontangential filter. -/
theorem nontangentialCone_mem_nontangentialFilter (α x : ℝ) {h : ℝ≥0∞} (hh : 0 < h) :
    nontangentialCone α h x ∈ nontangentialFilter α x :=
  (nontangentialFilter_hasBasis α x).mem_of_mem hh

/-- The nontangential filter at `x` is finer than the neighbourhood filter of `x`. -/
theorem nontangentialFilter_le_nhds (α x : ℝ) : nontangentialFilter α x ≤ 𝓝 (x : ℂ) :=
  nhdsWithin_le_nhds

/-- Along a nontangential approach to the real axis, `Im z → 0`. -/
theorem tendsto_im_nontangentialFilter (α x : ℝ) :
    Tendsto Complex.im (nontangentialFilter α x) (𝓝 0) := by
  simpa using (continuous_im.tendsto (x : ℂ)).mono_left (nontangentialFilter_le_nhds α x)

/-- Along a nontangential approach to `x`, eventually `Im z > 0` and `|Re z - x| ≤ δ / 2`. -/
theorem eventually_nontangentialFilter_abs_re_sub_le (α x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in nontangentialFilter α x, 0 < z.im ∧ |z.re - x| ≤ δ / 2 := by
  have hη : 0 < δ / (2 * (|α| + 1)) := by positivity
  filter_upwards [nontangentialCone_mem_nontangentialFilter α x (ENNReal.ofReal_pos.2 hη)] with z hz
  obtain ⟨hz0, hzα, hzη⟩ := mem_nontangentialCone.1 hz
  have hzη' : z.im < δ / (2 * (|α| + 1)) := (ENNReal.ofReal_lt_ofReal_iff hη).1 hzη
  refine ⟨hz0, ?_⟩
  have h1 : α * z.im ≤ (|α| + 1) * z.im := by nlinarith [le_abs_self α]
  have h2 : (|α| + 1) * z.im ≤ (|α| + 1) * (δ / (2 * (|α| + 1))) := by gcongr
  have h3 : (|α| + 1) * (δ / (2 * (|α| + 1))) = δ / 2 := by field_simp
  linarith

/-- The nontangential filter grows with the aperture: a nontangential limit for cones of aperture
`β` is one for cones of every aperture `α ≤ β`. -/
theorem nontangentialFilter_mono {α β : ℝ} (hαβ : α ≤ β) (x : ℝ) :
    nontangentialFilter α x ≤ nontangentialFilter β x :=
  nhdsWithin_mono _ (nontangentialCone_mono hαβ le_rfl x)

/-- **Straight-line approach inside the cone is nontangential.** For `|c| < α`, the ray
`(x + ct) + it → x` nontangentially as `t → 0⁺`. -/
theorem tendsto_ray_nontangentialFilter {α c : ℝ} (hc : |c| < α) (x : ℝ) :
    Tendsto (fun t : ℝ => ((x + c * t : ℝ) : ℂ) + t * I) (𝓝[>] 0) (nontangentialFilter α x) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => ((x + c * t : ℝ) : ℂ) + t * I) (𝓝 0)
        (𝓝 (((x + c * 0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
      ((by fun_prop : Continuous fun t : ℝ => ((x + c * t : ℝ) : ℂ) + t * I).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine mem_nontangentialCone.2 ⟨by simpa using ht, ?_, by simp⟩
    simpa [abs_mul, abs_of_pos ht] using mul_lt_mul_of_pos_right hc ht

/-- **Vertical approach is nontangential.** For a positive aperture, `x + it → x` nontangentially
as `t → 0⁺`. -/
theorem tendsto_vertical_nontangentialFilter {α : ℝ} (hα : 0 < α) (x : ℝ) :
    Tendsto (fun t : ℝ => (x : ℂ) + t * I) (𝓝[>] 0) (nontangentialFilter α x) := by
  simpa using tendsto_ray_nontangentialFilter (c := 0) (by simpa using hα) x

/-- For a positive aperture the nontangential filter is nontrivial. -/
theorem nontangentialFilter_neBot {α : ℝ} (hα : 0 < α) (x : ℝ) :
    (nontangentialFilter α x).NeBot :=
  (tendsto_vertical_nontangentialFilter hα x).neBot

/-- **A nontangential limit is a vertical limit.** -/
theorem tendsto_vertical_of_tendsto_nontangentialFilter {E : Type*} [TopologicalSpace E]
    {α : ℝ} (hα : 0 < α) {x : ℝ} {u : ℂ → E} {L : E}
    (hu : Tendsto u (nontangentialFilter α x) (𝓝 L)) :
    Tendsto (fun t : ℝ => u ((x : ℂ) + t * I)) (𝓝[>] 0) (𝓝 L) :=
  hu.comp (tendsto_vertical_nontangentialFilter hα x)

/-- If `u` has nontangential limit `L` at `x` along cones of aperture `α`, then
`M^α_h u(x) ≤ ‖L‖ₑ + 1` for some height `h > 0`; in particular, the nontangential maximal
function of `u` over a short enough cone is finite at `x`. -/
theorem exists_nontangentialMaximalFunction_le_of_tendsto {E : Type*} [SeminormedAddCommGroup E]
    {α x : ℝ} {u : ℂ → E} {L : E} (hu : Tendsto u (nontangentialFilter α x) (𝓝 L)) :
    ∃ h : ℝ≥0∞, 0 < h ∧ nontangentialMaximalFunction α h u x ≤ ‖L‖ₑ + 1 := by
  have hball : ∀ᶠ z in nontangentialFilter α x, ‖u z‖ₑ ≤ ‖L‖ₑ + 1 := by
    filter_upwards [hu.eventually (ball_mem_nhds L one_pos)] with z hz
    rw [dist_eq_norm] at hz
    calc ‖u z‖ₑ = ‖L + (u z - L)‖ₑ := by rw [add_sub_cancel]
      _ ≤ ‖L‖ₑ + ‖u z - L‖ₑ := eNorm_add_le _ _
      _ ≤ ‖L‖ₑ + 1 := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.2 hz.le
  obtain ⟨h, hh, hsub⟩ := (nontangentialFilter_hasBasis α x).eventually_iff.1 hball
  exact ⟨h, hh, nontangentialMaximalFunction_le_iff.2 hsub⟩

end TauCeti
