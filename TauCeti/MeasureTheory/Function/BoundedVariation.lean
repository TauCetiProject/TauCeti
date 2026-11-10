/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of path variation

A family of continuous paths with measurable evaluations has measurable total variation.
This includes infinite variation and therefore also makes the event of bounded variation
measurable. Restriction to a compact time interval gives the finite-horizon form used for
variation processes of adapted continuous paths.

The path-space step uses Mathlib's evaluation-generated Borel sigma algebra on continuous maps;
lower semicontinuity of variation then supplies measurability without choosing partitions.
-/

public section

open MeasureTheory Set

namespace Measurable

variable {Ω α E : Type*} [MeasurableSpace Ω] [LinearOrder α] [TopologicalSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]
  [PseudoMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {X : α → Ω → E}

/-- Total variation of a continuous random path is measurable, even when it is infinite. -/
theorem eVariationOn (hX : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (s : Set α) :
    Measurable (fun ω => eVariationOn (fun t => X t ω) s) := by
  let F : Ω → C(α, E) := fun ω => ⟨fun t => X t ω, hc ω⟩
  have hF : Measurable F := ContinuousMap.measurable_iff_eval.mpr hX
  exact (ContinuousMap.lowerSemicontinuous_eVariationOn s).measurable.comp hF

/-- Variation on a closed interval is measurable when evaluations are measurable and paths
are continuous on that interval. No bounded-variation assumption is needed. -/
theorem eVariationOn_Icc [OrderClosedTopology α] {a b : α}
    (hX : ∀ t ∈ Icc a b, Measurable (X t))
    (hc : ∀ ω, ContinuousOn (fun t => X t ω) (Icc a b)) :
    Measurable (fun ω => _root_.eVariationOn (fun t => X t ω) (Icc a b)) := by
  let : LocallyCompactSpace (Icc a b) := isClosed_Icc.locallyCompactSpace
  have hm := Measurable.eVariationOn (X := fun t : Icc a b => X t)
    (fun t => hX t t.2) (fun ω => (hc ω).domRestrict) univ
  have he (ω : Ω) :
      _root_.eVariationOn (fun t : Icc a b => X t ω) univ =
        _root_.eVariationOn (fun t => X t ω) (Icc a b) := by
    convert _root_.eVariationOn.comp_eq_of_monotoneOn (t := univ) (fun t => X t ω)
      (Subtype.val : Icc a b → α) (fun _ _ _ _ h => h) using 1
    · rfl
    · congr 1
      exact (Subtype.coe_image_univ _).symm
  simpa only [he] using hm

end Measurable
