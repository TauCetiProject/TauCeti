/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation

/-!
# Metric variation of a continuously differentiable curve

For a continuously differentiable curve in a real normed space, its
metric total variation equals the integral of the norm of its derivative.

The upper bound applies the generic integral-density variation bound to the fundamental
theorem of calculus on subintervals. Equality follows from the metric derivative identity
for absolutely continuous curves and identification of the derivative at interior points.

## Main result

* `TauCeti.eVariationOn_eq_lintegral_enorm_derivWithin`: metric variation
  equals the integral of the derivative norm.

## Roadmap alignment

This module advances the `Regular reparametrization and limits` target under
`Layer 0: the reconciled Riemannian distance` in
`roadmap/HopfRinow/README.md`. It supplies the vector metric-variation
identity used as an analytic prerequisite by the lower-semicontinuity
comparison; this file does not claim the broader
Hopf--Rinow dependency path.

## Provenance

The partition-comparison architecture follows
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean` in the
Apache-2.0 `frenzymath/Poincare-Conjecture` source at revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. That source proves the forward
comparison with Riemannian path length. The derivative-integral equality follows from the
generic absolutely continuous metric-speed identity. This reverse comparison is a Tau Ceti
proof and is not asserted to be present in that source.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* The source-first Lean snapshot above, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`, supplies the partition architecture
  via `eVariationOn_le_pathELength`; the reverse inequality is original to this
  module.
-/

public section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a `C¹` curve in a real normed space, metric total variation is bounded
by the integral of the norm of its derivative. -/
theorem eVariationOn_le_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := by
  have hcontrol {s u : ℝ} (hs : s ∈ Icc a b) (hu : u ∈ Icc a b) (hsu : s ≤ u) :
      edist (f s) (f u) ≤ ∫⁻ t in uIoc s u, ‖derivWithin f (Icc a b) t‖ₑ := by
    calc
      edist (f s) (f u) = ‖f u - f s‖ₑ := by rw [edist_eq_enorm_sub, enorm_sub_rev]
      _ ≤ ∫⁻ t in Icc s u, ‖derivWithin f (Icc s u) t‖ₑ :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
          (hf.mono (Icc_subset_Icc hs.1 hu.2)) hsu
      _ = ∫⁻ t in uIoc s u, ‖derivWithin f (Icc a b) t‖ₑ := by
        rw [uIoc_of_le hsu, restrict_Ioc_eq_restrict_Icc,
          ← restrict_Ioo_eq_restrict_Icc]
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only
        rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
          derivWithin_of_mem_nhds (Icc_mem_nhds (hs.1.trans_lt ht.1) (ht.2.trans_le hu.2))]
  calc
    eVariationOn f (Icc a b) ≤ ∫⁻ t in Ioc a b, ‖derivWithin f (Icc a b) t‖ₑ := by
      apply eVariationOn.le_lintegral_of_edist_le_lintegral
      intro s hs u hu
      rcases le_total s u with hsu | hus
      · exact hcontrol hs hu hsu
      · rw [edist_comm, uIoc_comm]
        exact hcontrol hu hs hus
    _ = _ := by rw [restrict_Ioc_eq_restrict_Icc]

/-- The metric total variation of a `C¹` curve in a real normed space equals the integral
of the norm of its derivative. Completeness of the target is not needed. -/
theorem eVariationOn_eq_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) = ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := by
  by_cases hab : a ≤ b
  swap
  · rw [Icc_eq_empty hab]
    simp
  have hf' : ContDiffOn ℝ 1 f (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hf
  have hAC := hf'.absolutelyContinuousOnInterval
  rw [← uIcc_of_le hab, hAC.eVariationOn_eq_lintegral_metricDerivative,
    uIoc_of_le hab, restrict_Ioc_eq_restrict_Icc, uIcc_of_le hab]
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  have hd : DifferentiableAt ℝ f t :=
    (hf t (Ioo_subset_Icc_self ht)).contDiffAt (Icc_mem_nhds ht.1 ht.2)
      |>.differentiableAt one_ne_zero
  rw [hd.hasDerivAt.metricDerivative_eq,
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

end

end TauCeti
