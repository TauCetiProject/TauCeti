/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Rescale

/-!
# Small-disk rescaling of Morse coordinate transitions

Suppose a coordinate transition `T`, fixing the origin, preserves the split expression
`Q(u,v) = -‖u‖² + ‖v‖²` near the origin. Its rescaling `T(s • y) / s` extends jointly
continuously at `s = 0` by `DT(0) y`, and preserves `Q` throughout the deformation.
One sufficiently small closed ball works for every `s ∈ [0,1]`: all rescaled images lie in
one controlled closed ball contained in any prescribed target neighborhood.

On the negative disk `y = (u,0)`, the equation is exactly `Q = -‖u‖²`. Thus the boundary
of a disk of radius `δ` remains at level `-δ²`, including the derivative endpoint. Composing
with the inverse of a second Morse chart gives the small-disk part of a comparison of
characteristic maps; no overlap of the original whole characteristic disks is required.

Only homogeneity of the squared norms is used, so the estimates work for arbitrary real
normed spaces. For Morse charts the spaces are the negative and positive Euclidean factors.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§2–3.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {T : E × F → E × F} {A : (E × F) →L[ℝ] E × F} {U : Set (E × F)}

private theorem rescale_neg_norm_fst_sq_add_norm_snd_sq_eq_of_ne_zero (hT0 : T 0 = 0)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {s : ℝ} (hs : s ≠ 0) {y : E × F} (hy : s • y ∈ U) :
    -‖(derivativeRescale T A s y).1‖ ^ 2 + ‖(derivativeRescale T A s y).2‖ ^ 2 =
      -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  have h := hQ (s • y) hy
  rw [derivativeRescale_of_ne_zero T A hs, hT0, sub_zero]
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, norm_inv, mul_pow] at h ⊢
  have hnorm : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  field_simp
  nlinarith [h]

/-- Rescaling a transition that fixes the origin and preserves the split squared norm preserves
that expression even at scale zero. The input is required to stay in the original coordinate
domain only along its segment to the origin. -/
theorem _root_.HasFDerivAt.derivativeRescale_neg_norm_fst_sq_add_norm_snd_sq_eq
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {y : E × F} (hy : ∀ s ∈ Icc (0 : ℝ) 1, s • y ∈ U) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    -‖(derivativeRescale T A s y).1‖ ^ 2 + ‖(derivativeRescale T A s y).2‖ ^ 2 =
      -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  by_cases hs0 : s = 0
  · subst s
    -- Joint continuity supplies the missing endpoint; positive scales have the exact equation.
    have hc : ContinuousAt (fun t : ℝ ↦ derivativeRescale T A t y) 0 :=
      (hT.continuousAt_derivativeRescale_zero y).comp' (f := fun t : ℝ ↦ (t, y))
        (continuousAt_id.prodMk continuousAt_const)
    have hlim : Tendsto (fun t : ℝ ↦
        -‖(derivativeRescale T A t y).1‖ ^ 2 + ‖(derivativeRescale T A t y).2‖ ^ 2)
        (𝓝[>] 0) (𝓝 (-‖(derivativeRescale T A 0 y).1‖ ^ 2 +
          ‖(derivativeRescale T A 0 y).2‖ ^ 2)) :=
      ((hc.fst.norm.pow 2).neg.add (hc.snd.norm.pow 2)).tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    exact (rescale_neg_norm_fst_sq_add_norm_snd_sq_eq_of_ne_zero hT0 hQ ht.ne'
      (hy t ⟨ht.le, ht1.le⟩)).symm
  · exact rescale_neg_norm_fst_sq_add_norm_snd_sq_eq_of_ne_zero hT0 hQ hs0 (hy s hs)

/-- A single small disk admits the entire rescaling deformation of a split-quadratic coordinate
transition to its derivative. Both the original disk and the controlled image ball lie in the
prescribed coordinate neighborhoods. The norm bound and exact level equation hold uniformly
throughout, including at scale zero. -/
theorem _root_.HasFDerivAt.exists_small_disk_derivativeRescale
    (hT : HasFDerivAt T A 0) (hT0 : T 0 = 0)
    (hU : IsOpen U) (h0U : (0 : E × F) ∈ U) (hc : ContinuousOn T U)
    (hQ : ∀ y ∈ U, -‖(T y).1‖ ^ 2 + ‖(T y).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2)
    {V : Set (E × F)} (hV : V ∈ 𝓝 0) :
    ∃ L > 0, ‖A‖ ≤ L ∧ ∃ δ > 0,
      Metric.closedBall 0 δ ⊆ U ∧ Metric.closedBall 0 (L * δ) ⊆ V ∧
      ContinuousOn (fun p : ℝ × (E × F) ↦ derivativeRescale T A p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 δ) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : E × F) δ,
        ‖derivativeRescale T A s y‖ ≤ L * ‖y‖ ∧
        derivativeRescale T A s y ∈ V ∧
        -‖(derivativeRescale T A s y).1‖ ^ 2 + ‖(derivativeRescale T A s y).2‖ ^ 2 =
          -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
  obtain ⟨L, hL, hA, δ, hδ, hδU, hδV, hb⟩ :=
    hT.exists_derivativeRescale_closedBall_subset (hU.mem_nhds h0U) hV
  have hscale {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {y : E × F}
      (hy : y ∈ Metric.closedBall 0 δ) : s • y ∈ Metric.closedBall 0 δ := by
    exact (convex_closedBall (0 : E × F) δ).smul_mem_of_zero_mem
      (Metric.mem_closedBall_self hδ.le) hy hs
  refine ⟨L, hL, hA, δ, hδ, hδU, hδV, ?_, fun s hs y hy ↦ ?_⟩
  · rintro ⟨s, y⟩ ⟨hs, hy⟩
    by_cases hs0 : s = 0
    · subst s
      exact (hT.continuousAt_derivativeRescale_zero y).continuousWithinAt
    · exact (continuousAt_derivativeRescale hs0
        (hc.continuousAt (hU.mem_nhds (hδU (hscale hs hy))))).continuousWithinAt
  · have hsnorm : ‖s‖ ≤ 1 := by simpa [Real.norm_of_nonneg hs.1] using hs.2
    have hynorm : ‖y‖ ≤ δ := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hbound := hb s hsnorm y hynorm
    refine ⟨hbound, hδV ?_, hT.derivativeRescale_neg_norm_fst_sq_add_norm_snd_sq_eq hT0 hQ
      (fun t ht ↦ hδU (hscale ht hy)) hs⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hbound.trans (mul_le_mul_of_nonneg_left hynorm hL.le)

end TauCeti
