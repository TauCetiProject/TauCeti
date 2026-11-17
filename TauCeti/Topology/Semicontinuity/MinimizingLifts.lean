/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity from compact minimizing lifts

Suppose nearby points admit lifts to a fixed compact parameter set, with cost at most the
value of a given function. If every lift of the center costs at least the value there, the
function is lower semicontinuous at the center. The endpoint map is continuous on the compact
set, while the cost need only be lower semicontinuous. The ordered cost space needs no topology
or completeness assumption.

The fibers of the endpoint map vary with the endpoint. This criterion applies to reduced
length represented by minimizing initial vectors and terminal times.


## References

* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open scoped Topology

/-- Compact minimizing lifts detect lower semicontinuity at a point. It suffices to realize
nearby values from below; all lifts over the center must satisfy the reverse inequality. -/
theorem IsCompact.lowerSemicontinuousAt_of_minimizing_lifts
    {X Y β : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [LinearOrder β]
    {l : X → β} {x : X} {Q : Set X} {K : Set Y} (hK : IsCompact K) (hQ : Q ∈ 𝓝 x)
    {endpoint : Y → X} {cost : Y → β} (hendpoint : ContinuousOn endpoint K)
    (hcost : LowerSemicontinuousOn cost K)
    (hrealizes : ∀ z ∈ Q, ∃ w ∈ K, endpoint w = z ∧ cost w ≤ l z)
    (hcomparison : ∀ w ∈ K, endpoint w = x → l x ≤ cost w) :
    LowerSemicontinuousAt l x := by
  intro c hc
  have hsub := hcost.isCompact_inter_preimage_Iic hK c
  have hclosed : IsClosed (endpoint '' (K ∩ cost ⁻¹' Set.Iic c)) :=
    (hsub.image_of_continuousOn (hendpoint.mono Set.inter_subset_left)).isClosed
  have hx : x ∈ (endpoint '' (K ∩ cost ⁻¹' Set.Iic c))ᶜ := by
    rintro ⟨w, ⟨hwK, hwc⟩, hwx⟩
    exact (not_le_of_gt hc) ((hcomparison w hwK hwx).trans hwc)
  filter_upwards [hQ, hclosed.isOpen_compl.mem_nhds hx] with z hz hzoutside
  by_contra hzle
  obtain ⟨w, hw, hwz, hwl⟩ := hrealizes z hz
  exact hzoutside ⟨w, ⟨hw, hwl.trans (le_of_not_gt hzle)⟩, hwz⟩
