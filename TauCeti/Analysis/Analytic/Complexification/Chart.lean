/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Complexification.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Complexification of analytic charts

A real analytic chart and its analytic inverse extend together to a holomorphic chart near each
real point of its source. The complex chart and its inverse agree with the original maps near
the corresponding real points and commute with conjugation. This allows changes to analytic
coordinates before applying holomorphic polynomial root theorems.

The identity theorem on real points transports the two inverse identities to complex
neighborhoods. Restricting those neighborhoods then gives an open partial homeomorphism; no
choice of a derivative or complex linear extension of a derivative is needed.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

open Filter Function Metric Set Topology

namespace AnalyticAt

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Complex analytic extensions of real maps that are inverse near a real point remain inverse
near that point in the complex domain. Only continuity of the inner real map is required. -/
theorem eventually_comp_eq_id_of_eventually_real
    {f : (ι → ℝ) → κ → ℝ} {g : (κ → ℝ) → ι → ℝ} {a : ι → ℝ}
    {F : (ι → ℂ) → κ → ℂ} {G : (κ → ℂ) → ι → ℂ}
    (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ)))
    (hG : AnalyticAt ℂ G (fun i ↦ (f a i : ℂ))) (hf : ContinuousAt f a)
    (hFr : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = fun i ↦ (f x i : ℂ))
    (hGr : ∀ᶠ y in 𝓝 (f a), G (fun i ↦ (y i : ℂ)) = fun i ↦ (g y i : ℂ))
    (hgf : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    ∀ᶠ z in 𝓝 (fun i ↦ (a i : ℂ)), G (F z) = z := by
  have hFa := hFr.self_of_nhds
  apply (hG.comp_of_eq hF hFa).eventuallyEq_of_eventually_real analyticAt_id
  filter_upwards [hFr, hf.eventually hGr, hgf] with x hFx hGx hgfx
  simp only [comp_apply, id_eq, hFx, hGx, hgfx]

end AnalyticAt

namespace OpenPartialHomeomorph

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A real chart analytic at a source point, with inverse analytic at its image, extends to a
complex chart analytic on its source with analytic inverse on its target. Both maps agree with
the original chart near the real points and commute with conjugation there. -/
theorem exists_complexification (e : OpenPartialHomeomorph (ι → ℝ) (κ → ℝ))
    {a : ι → ℝ} (ha : a ∈ e.source) (he : AnalyticAt ℝ e a)
    (he' : AnalyticAt ℝ e.symm (e a)) :
    ∃ E : OpenPartialHomeomorph (ι → ℂ) (κ → ℂ),
      (fun i ↦ (a i : ℂ)) ∈ E.source ∧
      AnalyticOnNhd ℂ E E.source ∧ AnalyticOnNhd ℂ E.symm E.target ∧
      (∀ᶠ x in 𝓝 a, E (fun i ↦ (x i : ℂ)) = fun i ↦ (e x i : ℂ)) ∧
      (∀ᶠ y in 𝓝 (e a), E.symm (fun i ↦ (y i : ℂ)) = fun i ↦ (e.symm y i : ℂ)) ∧
      (∀ z, E (star z) = star (E z)) ∧ (∀ z, E.symm (star z) = star (E.symm z)) := by
  obtain ⟨r, hr, F, hF, hFr, hFs⟩ := he.exists_complexification_pi
  obtain ⟨s, hs, G, hG, hGr, hGs⟩ := he'.exists_complexification_pi
  have hFr' : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = fun i ↦ (e x i : ℂ) := by
    filter_upwards [ball_mem_nhds a hr] with x hx using hFr x hx
  have hGr' : ∀ᶠ y in 𝓝 (e a),
      G (fun i ↦ (y i : ℂ)) = fun i ↦ (e.symm y i : ℂ) := by
    filter_upwards [ball_mem_nhds (e a) hs] with y hy using hGr y hy
  have hFa := hFr'.self_of_nhds
  have hGF := (hF _ (mem_ball_self hr)).eventually_comp_eq_id_of_eventually_real
    (hG _ (mem_ball_self hs)) (e.continuousAt ha) hFr' hGr'
    (e.eventually_left_inverse ha)
  have hFG : ∀ᶠ z in 𝓝 (fun i ↦ (e a i : ℂ)), F (G z) = z := by
    have h := (hG _ (mem_ball_self hs)).eventually_comp_eq_id_of_eventually_real
      (by simpa only [e.left_inv ha] using hF _ (mem_ball_self hr))
      (e.symm.continuousAt (e.map_source ha)) hGr'
      (by simpa only [e.left_inv ha] using hFr')
      (e.eventually_right_inverse' ha)
    exact h
  obtain ⟨U, hUinv, hUopen, haU⟩ := _root_.eventually_nhds_iff.1 hGF
  obtain ⟨V, hVinv, hVopen, haV⟩ := _root_.eventually_nhds_iff.1 hFG
  let U' := U ∩ ball (fun i ↦ (a i : ℂ)) r
  let V' := V ∩ ball (fun i ↦ (e a i : ℂ)) s
  have hFU : AnalyticOnNhd ℂ F U' := hF.mono inter_subset_right
  have hGV : AnalyticOnNhd ℂ G V' := hG.mono inter_subset_right
  obtain ⟨E, hEF, hEG, hsource, htarget⟩ :=
    hFU.continuousOn.exists_openPartialHomeomorph_of_invOn hGV.continuousOn
      (hUopen.inter isOpen_ball) (hVopen.inter isOpen_ball)
      (fun x hx ↦ hUinv x hx.1) (fun y hy ↦ hVinv y hy.1)
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsource, mem_inter_iff, mem_preimage, hFa]
    exact ⟨⟨haU, mem_ball_self hr⟩, ⟨haV, mem_ball_self hs⟩⟩
  · rw [hEF]
    exact hFU.mono (hsource ▸ inter_subset_left)
  · rw [hEG]
    exact hGV.mono (htarget ▸ inter_subset_left)
  · simpa only [hEF] using hFr'
  · simpa only [hEG] using hGr'
  · simpa only [hEF] using hFs
  · simpa only [hEG] using hGs

end OpenPartialHomeomorph
