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

namespace OpenPartialHomeomorph

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A real chart analytic at a source point, with inverse analytic at its image, extends to a
complex chart analytic on its source with analytic inverse on its target. Both maps agree with
the original chart near the real points and commute with conjugation at every complex point. -/
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
    (hG _ (mem_ball_self hs)) hFr' hGr'
    (e.eventually_left_inverse ha)
  have hFG : ∀ᶠ z in 𝓝 (fun i ↦ (e a i : ℂ)), F (G z) = z := by
    have h := (hG _ (mem_ball_self hs)).eventually_comp_eq_id_of_eventually_real
      (by simpa only [e.left_inv ha] using hF _ (mem_ball_self hr))
      hGr'
      (by simpa only [e.left_inv ha] using hFr')
      (e.eventually_right_inverse' ha)
    exact h
  obtain ⟨U, hUinv, hUopen, haU⟩ := _root_.eventually_nhds_iff.1 hGF
  obtain ⟨V, hVinv, hVopen, haV⟩ := _root_.eventually_nhds_iff.1 hFG
  let U' := U ∩ ball (fun i ↦ (a i : ℂ)) r
  let V' := V ∩ ball (fun i ↦ (e a i : ℂ)) s
  have hFU : AnalyticOnNhd ℂ F U' := hF.mono inter_subset_right
  have hGV : AnalyticOnNhd ℂ G V' := hG.mono inter_subset_right
  have hgf : LeftInvOn G F (U' ∩ F ⁻¹' V') := fun x hx ↦ hUinv x hx.1.1
  have hfg : RightInvOn G F (V' ∩ G ⁻¹' U') := fun y hy ↦ hVinv y hy.1.1
  let E := hFU.continuousOn.toOpenPartialHomeomorph hGV.continuousOn
    (hUopen.inter isOpen_ball) (hVopen.inter isOpen_ball) hgf hfg
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [E]
    rw [ContinuousOn.toOpenPartialHomeomorph_source, mem_inter_iff, mem_preimage, hFa]
    exact ⟨⟨haU, mem_ball_self hr⟩, ⟨haV, mem_ball_self hs⟩⟩
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph,
      ContinuousOn.toOpenPartialHomeomorph_source] using hFU.mono inter_subset_left
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm,
      ContinuousOn.toOpenPartialHomeomorph_target] using hGV.mono inter_subset_left
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph] using hFr'
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm] using hGr'
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph] using hFs
  · simpa only [E, ContinuousOn.coe_toOpenPartialHomeomorph_symm] using hGs

end OpenPartialHomeomorph
