/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue

/-!
# Images of real half-intervals under monotone maps

The image of a half-infinite real interval under a continuous strictly monotone map is determined
by its value at the finite endpoint and its limit at infinity.  The endpoint at infinity is omitted
when the limit is finite.

## Main result

* `ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto` — a continuous strictly
  increasing map
  on `Ici p` with a finite limit at `+∞` maps that interval to the half-open interval between its
  endpoint value and its limit.
* `ContinuousOn.image_Iic_of_strictAntiOn_of_tendsto` — the corresponding statement for a
  continuous strictly decreasing map on `Iic p` with a finite limit at `-∞`.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- **A continuous strictly increasing map sends a half-line to a half-open interval.** The finite
limit at `+∞` is approached but is not attained. -/
theorem _root_.ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto
    {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {d : α → β} {p : α} {D : β}
    (hdcont : ContinuousOn d (Ici p))
    (hdmono : StrictMonoOn d (Ici p)) (hdl : Tendsto d atTop (𝓝 D)) :
    d '' Ici p = Ico (d p) D := by
  have hle : ∀ x ∈ Ici p, d x ≤ D := by
    intro x hx
    apply ge_of_tendsto hdl
    filter_upwards [eventually_ge_atTop x] with y hxy
    have hy : y ∈ Ici p := hx.trans hxy
    exact hdmono.monotoneOn hx hy hxy
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxp : p ≤ x := hx
    obtain ⟨x1, hx1⟩ := exists_gt x
    have hx1' : x1 ∈ Ici p := hx.trans hx1.le
    have hlt : d x < D := lt_of_lt_of_le
      (hdmono hx hx1' hx1) (hle x1 hx1')
    exact ⟨hdmono.monotoneOn self_mem_Ici hx hxp, hlt⟩
  · exact isPreconnected_Ici.intermediate_value_Ico self_mem_Ici
      (le_principal_iff.mpr (Ici_mem_atTop p)) hdcont hdl

/-- **A continuous strictly decreasing map sends a left half-line to a half-open interval.** The
finite limit at `-∞` is approached but is not attained. -/
theorem _root_.ContinuousOn.image_Iic_of_strictAntiOn_of_tendsto
    {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMinOrder α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {d : α → β} {p : α} {D : β}
    (hdcont : ContinuousOn d (Iic p))
    (hdanti : StrictAntiOn d (Iic p)) (hdl : Tendsto d atBot (nhds D)) :
    d '' Iic p = Ico (d p) D := by
  have hle : ∀ x ∈ Iic p, d x ≤ D := by
    intro x hx
    apply ge_of_tendsto hdl
    filter_upwards [eventually_le_atBot x] with y hyx
    have hy : y ∈ Iic p := hyx.trans hx
    exact hdanti.antitoneOn hy hx hyx
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x1, hx1⟩ := exists_lt x
    have hx1' : x1 ∈ Iic p := hx1.le.trans hx
    have hlt : d x < D := lt_of_lt_of_le
      (hdanti hx1' hx hx1) (hle x1 hx1')
    exact ⟨hdanti.antitoneOn hx self_mem_Iic hx, hlt⟩
  · exact isPreconnected_Iic.intermediate_value_Ico self_mem_Iic
      (le_principal_iff.mpr (Iic_mem_atBot p)) hdcont hdl

end TauCeti
