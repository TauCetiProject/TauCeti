/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The trace of a curve near a point visited once lies in thin cones around the tangent

Near a point where a curve `γ : ℝ → ℂ` has derivative `v`, and which `γ` visits only once on a
compact parameter set, the trace of `γ` lies in arbitrarily thin double cones
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line: the derivative controls
the parameters close to `t₀`, and compactness keeps the others away from `γ t₀`.

## Main results

* `TauCeti.Contour.exists_pos_forall_abs_im_conj_mul_sub_le`: the trace near a point visited once
  lies in thin double cones around the tangent line.
-/

public section

open Complex ComplexConjugate Metric Set

namespace TauCeti.Contour

/-- **The trace near a point visited once lies in thin double cones around the tangent line.**
Let `γ` be continuous on a compact set `K` of parameters, with derivative `v` at `t₀` within `K`,
and assume that `γ` takes the value `γ t₀` on `K` only at `t₀`. Then for every `η > 0`, every point
of the trace `γ '' K` close enough to `γ t₀` lies in the double cone
`|Im (conj v * (z - γ t₀))| ≤ η * ‖z - γ t₀‖` around the tangent line. -/
theorem exists_pos_forall_abs_im_conj_mul_sub_le {γ : ℝ → ℂ} {K : Set ℝ} {t₀ : ℝ} {v : ℂ}
    (hK : IsCompact K) (hγ : ContinuousOn γ K) (huniq : ∀ t ∈ K, γ t = γ t₀ → t = t₀)
    (hd : HasDerivWithinAt γ v K t₀) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ s ∈ K, ‖γ s - γ t₀‖ < ρ →
      |(conj v * (γ s - γ t₀)).im| ≤ η * ‖γ s - γ t₀‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨1, one_pos, fun s _ _ ↦ by simpa using mul_nonneg hη.le (norm_nonneg (γ s - γ t₀))⟩
  set ε := min (‖v‖ / 2) (η / 2)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨σ, hσ, hloc⟩ : ∃ σ > 0, ∀ s ∈ K, |s - t₀| < σ →
      ‖γ s - γ t₀ - (s - t₀) • v‖ ≤ ε * |s - t₀| := by
    obtain ⟨σ, hσ, h⟩ := Metric.eventually_nhds_iff.mp
      (eventually_nhdsWithin_iff.mp ((hasDerivWithinAt_iff_isLittleO.mp hd).def hε))
    exact ⟨σ, hσ, fun s hs hsσ ↦ by
      simpa [Real.norm_eq_abs] using h (by rwa [Real.dist_eq]) hs⟩
  set L := K ∩ {s | σ ≤ |s - t₀|}
  have hL : IsCompact L :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hγL : γ t₀ ∉ γ '' L := by
    rintro ⟨s, ⟨hs, hsσ⟩, hst⟩
    exact hσ.not_ge (by simpa [huniq s hs hst] using hsσ)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
    (hL.image_of_continuousOn (hγ.mono inter_subset_left)).isClosed.isOpen_compl _ hγL
  refine ⟨ρ, hρ, fun s hs hsρ ↦ ?_⟩
  have hsσ : |s - t₀| < σ := by
    by_contra h
    exact hball (mem_ball.mpr (by rwa [dist_eq_norm])) (mem_image_of_mem γ ⟨hs, not_lt.mp h⟩)
  have he := hloc s hs hsσ
  set e := γ s - γ t₀ - (s - t₀) • v
  have him : (conj v * (γ s - γ t₀)).im = (conj v * e).im := by
    have hreal : (conj v * ((s - t₀) • v)).im = 0 := by
      simp only [mul_smul_comm, smul_im, mul_im, conj_re, conj_im, smul_eq_mul]
      ring
    rw [show γ s - γ t₀ = (s - t₀) • v + e by simp [e], mul_add, add_im, hreal, zero_add]
  have hime : |(conj v * e).im| ≤ ‖v‖ * ‖e‖ :=
    (abs_im_le_norm _).trans_eq (by rw [norm_mul, Complex.norm_conj])
  have hlow : ‖v‖ / 2 * |s - t₀| ≤ ‖γ s - γ t₀‖ := by
    have h1 := norm_sub_le (γ s - γ t₀) e
    rw [show γ s - γ t₀ - e = (s - t₀) • v by simp [e], norm_smul, Real.norm_eq_abs] at h1
    have : ε ≤ ‖v‖ / 2 := min_le_left _ _
    nlinarith [abs_nonneg (s - t₀)]
  have hεη : ε ≤ η / 2 := min_le_right _ _
  rw [him]
  calc |(conj v * e).im| ≤ ‖v‖ * (ε * |s - t₀|) :=
        hime.trans (mul_le_mul_of_nonneg_left he hvpos.le)
    _ = 2 * ε * (‖v‖ / 2 * |s - t₀|) := by ring
    _ ≤ 2 * ε * ‖γ s - γ t₀‖ := mul_le_mul_of_nonneg_left hlow (by positivity)
    _ ≤ η * ‖γ s - γ t₀‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end TauCeti.Contour
