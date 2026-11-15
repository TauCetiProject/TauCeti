/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.Topology.MetricSpace.RayCutTime

/-!
# Measurability of cut times of rays

For a family of rays `Γ : P → ℝ → X` from a set `S`, the cut time
`TauCeti.rayCutTime (Γ p) S (T p) R` is measurable in the parameter `p` as soon as the
minimizing condition is measurable at every rational time. When the time domain is the set of
times spent in a closed set and the rays depend continuously on the parameter, the cut time is
upper semicontinuous, hence measurable.

## Main results

* `TauCeti.measurable_rayCutTime`: measurability of the cut time of a family of rays.
* `TauCeti.measurable_rayCutTime_preimage`: measurability of the cut time of a continuous family
  of rays, with time domain the times spent in a closed set `D`.
-/

public section

open Set

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X] {S : Set X} {R : ℝ}

/-- The cut time of a family of rays is measurable in the parameter as soon as, at every rational
time, the set of parameters for which that time is minimizing is measurable. -/
theorem measurable_rayCutTime {P : Type*} [MeasurableSpace P] {Γ : P → ℝ → X}
    {T : P → Set ℝ} (hΓ : ∀ p, ∀ u ≤ R, Icc 0 u ⊆ T p → LipschitzOnWith 1 (Γ p) (Icc 0 u))
    (hR : 0 ≤ R) (h0T : ∀ p, 0 ∈ T p) (h0S : ∀ p, Γ p 0 ∈ S)
    (hmin : ∀ q : ℚ, MeasurableSet {p | (q : ℝ) ∈ rayMinimizingTimes (Γ p) S (T p) R}) :
    Measurable fun p ↦ rayCutTime (Γ p) S (T p) R := by
  refine measurable_of_Ioi fun a ↦ ?_
  have heq : (fun p ↦ rayCutTime (Γ p) S (T p) R) ⁻¹' Ioi a =
      ⋃ q : {q : ℚ // a < q}, {p | (q : ℝ) ∈ rayMinimizingTimes (Γ p) S (T p) R} := by
    ext p
    simp only [mem_preimage, mem_Ioi, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hcut
      rcases lt_or_ge a 0 with ha | ha
      · exact ⟨0, by exact_mod_cast ha,
          by exact_mod_cast zero_mem_rayMinimizingTimes hR (h0T p) (h0S p)⟩
      · obtain ⟨q, haq, hqc⟩ := exists_rat_btwn hcut
        exact ⟨q, haq, mem_rayMinimizingTimes_of_lt_rayCutTime (hΓ p) hR (h0T p) (h0S p)
          (ha.trans haq.le) hqc⟩
    · rintro ⟨q, haq, hq⟩
      exact haq.trans_le (le_rayCutTime hq)
  rw [heq]
  exact MeasurableSet.iUnion fun q ↦ hmin q

/-- The cut time of a continuous family of rays, with time domain the times spent in a closed set
`D`, is measurable in the parameter. -/
theorem measurable_rayCutTime_preimage {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] {D : Set X} {Γ : P → ℝ → X} (hD : IsClosed D) (hR : 0 ≤ R)
    (hΓ : ∀ p, LipschitzOnWith 1 (Γ p) (Icc 0 R)) (h0S : ∀ p, Γ p 0 ∈ S)
    (h0D : ∀ p, Γ p 0 ∈ D) (hc : ∀ t ∈ Icc 0 R, Continuous fun p ↦ Γ p t) :
    Measurable fun p ↦ rayCutTime (Γ p) S (Γ p ⁻¹' D) R :=
  (upperSemicontinuous_rayCutTime_preimage hD hR hΓ h0S h0D hc).measurable

end TauCeti
