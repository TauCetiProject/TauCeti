/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Topology of the upper half-plane

Every real point lies in the closure of the open upper half-plane, so limits taken along the
half-plane at a real point are well posed.  The half-plane is also unbounded, so the filter along
which it approaches infinity is nontrivial and limits taken along it are unique.

For a function conjugation-symmetric near infinity, decay along the upper half-plane implies
decay along the whole plane, provided it is continuous at sufficiently distant real points.

A continuous injection of the closed upper half-plane sends every real point to the frontier of
the image of the open half-plane.  The inversion `w ↦ -w⁻¹` preserves the closed upper
half-plane.

A function on the upper half-plane, extended to `ℂ` by `ofComplex`, is periodic with a real
period exactly when the original function is invariant under the corresponding translation.

## Main declarations

* `Real.nhdsWithin_upperHalfPlaneSet_neBot`.
* `TauCeti.cobounded_inf_principal_upperHalfPlaneSet_neBot`.
* `TauCeti.tendsto_zero_cobounded_of_tendsto_upperHalfPlaneSet`.
* `TauCeti.mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero`.
* `TauCeti.not_mem_image_upperHalfPlaneSet_of_im_eq_zero`.
* `TauCeti.im_neg_inv_nonneg`.
* `TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft the periodicity criterion ports onto the current
  Mathlib pin.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace Real

/-- Every real point is in the closure of the open upper half-plane, so limits along the
half-plane at a real point are well posed. -/
theorem nhdsWithin_upperHalfPlaneSet_neBot (x : ℝ) :
    (𝓝[upperHalfPlaneSet] ((x : ℂ))).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by simp [upperHalfPlaneSet])

end Real

namespace TauCeti

/-- The upper half-plane is unbounded, so the filter along which it approaches infinity is
nontrivial and limits taken along it are unique. -/
instance cobounded_inf_principal_upperHalfPlaneSet_neBot :
    (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet).NeBot := by
  -- The imaginary axis runs off to infinity inside the half-plane, so the filter it pushes
  -- forward from `atTop` is below both factors.
  have hcob : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa using tendsto_abs_atTop_atTop
  refine Filter.neBot_of_le (f := map (fun t : ℝ => (t : ℂ) * Complex.I) atTop)
    (le_inf hcob ?_)
  rw [le_principal_iff, mem_map]
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Set.mem_preimage, upperHalfPlaneSet, Set.mem_ofPred_eq]
  simpa using ht

/-- For a function conjugation-symmetric near infinity and continuous at all sufficiently distant
real points, decay along the upper half-plane implies decay along the whole plane. -/
theorem tendsto_zero_cobounded_of_tendsto_upperHalfPlaneSet {φ : ℂ → ℂ}
    (hcont : ∀ᶠ z in cobounded ℂ, z.im = 0 → ContinuousAt φ z)
    (hconj : ∀ᶠ z in cobounded ℂ, φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hlim : Tendsto φ (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 0)) :
    Tendsto φ (cobounded ℂ) (𝓝 0) := by
  rw [Metric.tendsto_nhds] at hlim ⊢
  intro ε hε
  have hbound := eventually_inf_principal.mp (hlim (ε / 2) (half_pos hε))
  obtain ⟨R, _, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).mem_iff.mp
    (hcont.and hbound)
  have hupper : ∀ z : ℂ, R < ‖z‖ → 0 ≤ z.im → ‖φ z‖ ≤ ε / 2 := by
    intro z hz hzim
    have hzR : z ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by simpa using hz
    rcases hzim.eq_or_lt with hreal | hpos
    · have hzre : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [hreal.symm]
      have : (𝓝[upperHalfPlaneSet] z).NeBot := by
        rw [← hzre]
        exact Real.nhdsWithin_upperHalfPlaneSet_neBot _
      apply le_of_tendsto (x := 𝓝[upperHalfPlaneSet] z)
        (((hR hzR).1 hreal.symm).norm.tendsto.mono_left nhdsWithin_le_nhds)
      filter_upwards [nhdsWithin_le_nhds
        (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hzR), self_mem_nhdsWithin] with w hw hwim
      exact (by simpa using (hR hw).2 hwim : ‖φ w‖ < ε / 2).le
    · exact (by simpa using (hR hzR).2 hpos : ‖φ z‖ < ε / 2).le
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R), hconj]
    with z hz hzconj
  rw [dist_zero_right]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rcases le_or_gt 0 z.im with hi | hi
  · exact hupper z hz hi
  · have h := hupper ((starRingEnd ℂ) z) (by simpa using hz) (by simpa using hi.le)
    simpa only [hzconj, norm_conj] using h

/-- A boundary point of the closed upper half-plane whose image avoids the open half-plane image
maps to the frontier when the map is continuous there. -/
theorem mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero {f : ℂ → ℂ}
    {z : ℂ} (hfc : ContinuousWithinAt f {z : ℂ | 0 ≤ z.im} z)
    (hz : z.im = 0) (hnot : f z ∉ f '' upperHalfPlaneSet) :
    f z ∈ frontier (f '' upperHalfPlaneSet) := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  refine ⟨(hfc.mono hH0).mem_closure_image ?_, fun h => hnot (interior_subset h)⟩
  · simp [upperHalfPlaneSet, hz]

/-- An injection on the closed upper half-plane cannot send a real point into the image of the
open upper half-plane. -/
theorem not_mem_image_upperHalfPlaneSet_of_im_eq_zero {f : ℂ → ℂ}
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) {z : ℂ} (hz : z.im = 0) :
    f z ∉ f '' upperHalfPlaneSet := by
  rintro ⟨y, hy, heq⟩
  have hypos : 0 < y.im := by simpa only [upperHalfPlaneSet, Set.mem_ofPred_eq] using hy
  have hyz : y = z := hfi hypos.le hz.symm.le heq
  simp [upperHalfPlaneSet, hyz, hz] at hy

/-- The inversion `w ↦ -w⁻¹` sends `w` into the closed upper half-plane exactly when `w` lies in
it. -/
theorem im_neg_inv_nonneg {w : ℂ} : 0 ≤ (-w⁻¹).im ↔ 0 ≤ w.im := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · have him : (-w⁻¹).im = w.im / normSq w := by simp [neg_div]
    rw [him, le_div_iff₀ (normSq_pos.mpr hw), zero_mul]

end TauCeti

namespace TauCeti.UpperHalfPlane

/-- A function `ℍ → α`, extended to `ℂ` via `ofComplex`, is periodic with real period `c` iff
the original function is invariant under translation by `c`. -/
lemma periodic_comp_ofComplex_iff {α : Type*} {f : ℍ → α} {c : ℝ} :
    Function.Periodic (f ∘ ofComplex) c ↔ ∀ τ : ℍ, f (c +ᵥ τ) = f τ := by
  constructor
  · intro h τ
    have := h ↑τ
    simp only [Function.comp_apply] at this
    -- Identify the translated coercion with the coercion of the translate, so both
    -- `ofComplex` applications land back on `ℍ`.
    rwa [show (τ : ℂ) + ↑c = ↑(c +ᵥ τ) by rw [coe_vadd]; ring, ofComplex_apply,
      ofComplex_apply] at this
  · intro h w
    rcases le_or_gt w.im 0 with hw | hw
    · exact congrArg f (ofComplex_apply_eq_of_im_nonpos (by simpa using hw) hw)
    · have hw' : 0 < (w + ↑c).im := by simpa using hw
      simp only [Function.comp_apply]
      -- Both points have positive imaginary part; identify the shifted point with the
      -- vector translate so the hypothesis applies.
      rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw,
        show (⟨w + ↑c, hw'⟩ : ℍ) = c +ᵥ (⟨w, hw⟩ : ℍ) from _root_.UpperHalfPlane.ext
          (by simp [add_comm])]
      exact h _

end TauCeti.UpperHalfPlane

end
