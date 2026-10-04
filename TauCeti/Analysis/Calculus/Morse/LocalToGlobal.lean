/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.LocalInvariantManifold

/-!
# From local invariant disks to global stable sets

Near a nondegenerate critical point, the Lyapunov--Perron construction identifies the initial
conditions of confined forward and backward trajectories with disks tangent to the positive and
negative Hessian subspaces. This file relates those local disks to the global stable and unstable
sets of a negative-gradient flow.

When the gradient is globally Lipschitz, uniqueness identifies every confined local trajectory
with an orbit of the global flow. Conversely, a trajectory converging to the critical point
eventually enters, and thereafter remains in, each sufficiently small ball. Consequently the
global stable or unstable set is exactly the union of the complete flow orbits through its local
disk. This is the local-to-global step used when the stable and unstable sets are given their
manifold structures and intersected to form Morse trajectory spaces.

## Main declarations

* `mem_localInvariantSet_iff_negativeGradientFlow`: characterizes a local invariant set over an
  order-connected time set using the global flow.
* `stableSet_eq_biUnion_orbit_localInvariantSet_Ici`: a convergent forward local invariant set
  generates the global stable set under the flow.
* `unstableSet_eq_biUnion_orbit_localInvariantSet_Iic`: the backward-time counterpart.
* `IsNondegenerateCriticalPoint.stableSet_eq_biUnion_orbit_localStableSet` and
  `IsNondegenerateCriticalPoint.unstableSet_eq_biUnion_orbit_localUnstableSet`: the corresponding
  statements for the local Lyapunov--Perron sets.
* `IsNondegenerateCriticalPoint.exists_stableSet_eq_biUnion_orbit_localStableSet` and
  `IsNondegenerateCriticalPoint.exists_unstableSet_eq_biUnion_orbit_localUnstableSet`: positive
  radii for which the local sets generate the global stable and unstable sets.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter InnerProductSpace Metric Set Topology
open scoped Gradient NNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E} {K : ℝ≥0}

/-- Membership in a local invariant set over an order-connected time set containing zero can be
witnessed by the global negative-gradient orbit: the orbit stays in the chosen ball throughout
the time set and its initial projection obeys the cutoff. -/
theorem mem_localInvariantSet_iff_negativeGradientFlow (hf : LipschitzWith K (∇ f))
    (Q : E →L[ℝ] E) {s : Set ℝ} (hs : s.OrdConnected) (h0 : 0 ∈ s)
    {r rho : ℝ} {z : E} :
    z ∈ localInvariantSet f x s Q r rho ↔
      (∀ t ∈ s, negativeGradientFlow f hf t (x + z) - x ∈ closedBall 0 r) ∧
        ‖Q z‖ ≤ rho := by
  constructor
  · rw [mem_localInvariantSet]
    rintro ⟨⟨y, hy, hy0, hmaps⟩, hQ⟩
    refine ⟨fun t ht ↦ ?_, hQ⟩
    rw [← eq_centeredNegativeGradientFlow_of_isIntegralCurveOn hf hy hy0
      (hs.uIcc_subset h0 ht)]
    exact hmaps ht
  · rintro ⟨hball, hQ⟩
    rw [mem_localInvariantSet]
    refine ⟨⟨fun t ↦ negativeGradientFlow f hf t (x + z) - x,
      (isIntegralCurve_centeredNegativeGradientFlow hf x z).isIntegralCurveOn s, ?_, ?_⟩, hQ⟩
    · simp only [_root_.Flow.map_zero_apply, add_sub_cancel_left]
    · exact hball

/-- Membership in a forward local invariant set can be witnessed by the global negative-gradient
orbit, with the confinement condition imposed at nonnegative times. -/
theorem mem_localInvariantSet_Ici_iff_negativeGradientFlow (hf : LipschitzWith K (∇ f))
    (Q : E →L[ℝ] E) {r rho : ℝ} {z : E} :
    z ∈ localInvariantSet f x (Ici 0) Q r rho ↔
      (∀ t, 0 ≤ t → negativeGradientFlow f hf t (x + z) - x ∈ closedBall 0 r) ∧
        ‖Q z‖ ≤ rho :=
  mem_localInvariantSet_iff_negativeGradientFlow hf Q ordConnected_Ici (by simp)

/-- Membership in a backward local invariant set can be witnessed by the global negative-gradient
orbit, with the confinement condition imposed at nonpositive times. -/
theorem mem_localInvariantSet_Iic_iff_negativeGradientFlow (hf : LipschitzWith K (∇ f))
    (Q : E →L[ℝ] E) {r rho : ℝ} {z : E} :
    z ∈ localInvariantSet f x (Iic 0) Q r rho ↔
      (∀ t, t ≤ 0 → negativeGradientFlow f hf t (x + z) - x ∈ closedBall 0 r) ∧
        ‖Q z‖ ≤ rho :=
  mem_localInvariantSet_iff_negativeGradientFlow hf Q ordConnected_Iic (by simp)

/-- Translating a forward local invariant set back to the base point gives points in the global
stable set, provided every trajectory confined to the chosen ball converges. -/
theorem image_add_localInvariantSet_Ici_subset_stableSet
    (hf : LipschitzWith K (∇ f)) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) →
      MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (nhds 0)) :
    (fun z ↦ x + z) '' localInvariantSet f x (Ici 0) Q r rho ⊆
      Flow.stableSet (negativeGradientFlow f hf) x := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Flow.mem_stableSet, ← tendsto_sub_nhds_zero_iff]
  exact hconv _ ((isIntegralCurve_centeredNegativeGradientFlow hf x z).isIntegralCurveOn (Ici 0))
    fun t ht ↦ ((mem_localInvariantSet_Ici_iff_negativeGradientFlow hf Q).1 hz).1 t ht

/-- Translating a backward local invariant set back to the base point gives points in the global
unstable set, provided every trajectory confined to the chosen ball converges backward. -/
theorem image_add_localInvariantSet_Iic_subset_unstableSet
    (hf : LipschitzWith K (∇ f)) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) →
      MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (nhds 0)) :
    (fun z ↦ x + z) '' localInvariantSet f x (Iic 0) Q r rho ⊆
      Flow.unstableSet (negativeGradientFlow f hf) x := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Flow.mem_unstableSet, ← tendsto_sub_nhds_zero_iff]
  exact hconv _ ((isIntegralCurve_centeredNegativeGradientFlow hf x z).isIntegralCurveOn (Iic 0))
    fun t ht ↦ ((mem_localInvariantSet_Iic_iff_negativeGradientFlow hf Q).1 hz).1 t ht

/-- Every point in the global stable set has a time translate whose displacement belongs to a
given forward local invariant set with positive cutoffs. -/
theorem exists_negativeGradientFlow_sub_mem_localInvariantSet_Ici_of_mem_stableSet
    (hf : LipschitzWith K (∇ f)) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho) {p : E}
    (hp : p ∈ Flow.stableSet (negativeGradientFlow f hf) x) :
    ∃ T, negativeGradientFlow f hf T p - x ∈ localInvariantSet f x (Ici 0) Q r rho := by
  let φ := negativeGradientFlow f hf
  have hp' : Tendsto (fun t ↦ φ t p) atTop (nhds x) := by
    simpa only [φ] using Flow.mem_stableSet.mp hp
  have hcentered : Tendsto (fun t ↦ φ t p - x) atTop (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr hp'
  have hball : ∀ᶠ t in atTop, φ t p - x ∈ closedBall 0 r :=
    hcentered.eventually (closedBall_mem_nhds 0 hr)
  have hproj : Tendsto (fun t ↦ Q (φ t p - x)) atTop (nhds 0) :=
    (Q.continuous.tendsto' 0 0 (map_zero Q)).comp hcentered
  have hprojBall : ∀ᶠ t in atTop, Q (φ t p - x) ∈ closedBall 0 rho :=
    hproj.eventually (closedBall_mem_nhds 0 hrho)
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hball.and hprojBall)
  refine ⟨T, (mem_localInvariantSet_Ici_iff_negativeGradientFlow hf Q).2 ⟨?_, ?_⟩⟩
  · intro s hs
    have hxz : x + (φ T p - x) = φ T p := by abel
    simpa only [φ, hxz, ← _root_.Flow.map_add, add_comm s T] using
      (hT (T + s) (le_add_of_nonneg_right hs)).1
  · simpa only [mem_closedBall, dist_zero_right] using (hT T le_rfl).2

/-- Every point in the global unstable set has a time translate whose displacement belongs to a
given backward local invariant set with positive cutoffs. -/
theorem exists_negativeGradientFlow_sub_mem_localInvariantSet_Iic_of_mem_unstableSet
    (hf : LipschitzWith K (∇ f)) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho) {p : E}
    (hp : p ∈ Flow.unstableSet (negativeGradientFlow f hf) x) :
    ∃ T, negativeGradientFlow f hf T p - x ∈ localInvariantSet f x (Iic 0) Q r rho := by
  let φ := negativeGradientFlow f hf
  have hp' : Tendsto (fun t ↦ φ t p) atBot (nhds x) := by
    simpa only [φ] using Flow.mem_unstableSet.mp hp
  have hcentered : Tendsto (fun t ↦ φ t p - x) atBot (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr hp'
  have hball : ∀ᶠ t in atBot, φ t p - x ∈ closedBall 0 r :=
    hcentered.eventually (closedBall_mem_nhds 0 hr)
  have hproj : Tendsto (fun t ↦ Q (φ t p - x)) atBot (nhds 0) :=
    (Q.continuous.tendsto' 0 0 (map_zero Q)).comp hcentered
  have hprojBall : ∀ᶠ t in atBot, Q (φ t p - x) ∈ closedBall 0 rho :=
    hproj.eventually (closedBall_mem_nhds 0 hrho)
  obtain ⟨T, hT⟩ := eventually_atBot.1 (hball.and hprojBall)
  refine ⟨T, (mem_localInvariantSet_Iic_iff_negativeGradientFlow hf Q).2 ⟨?_, ?_⟩⟩
  · intro s hs
    have hxz : x + (φ T p - x) = φ T p := by abel
    simpa only [φ, hxz, ← _root_.Flow.map_add, add_comm s T] using
      (hT (T + s) (add_le_of_nonpos_right hs)).1
  · simpa only [mem_closedBall, dist_zero_right] using (hT T le_rfl).2

/-- A forward local invariant set whose confined trajectories converge generates the whole global
stable set under the negative-gradient flow. -/
theorem stableSet_eq_biUnion_orbit_localInvariantSet_Ici
    (hf : LipschitzWith K (∇ f)) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho)
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) →
      MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (nhds 0)) :
    Flow.stableSet (negativeGradientFlow f hf) x =
      ⋃ z ∈ localInvariantSet f x (Ici 0) Q r rho,
        (negativeGradientFlow f hf).orbit (x + z) := by
  let φ := negativeGradientFlow f hf
  apply Subset.antisymm
  · intro p hp
    obtain ⟨T, hT⟩ :=
      exists_negativeGradientFlow_sub_mem_localInvariantSet_Ici_of_mem_stableSet
        hf Q hr hrho hp
    refine mem_iUnion.2 ⟨φ T p - x, mem_iUnion.2 ⟨?_, ?_⟩⟩
    · simpa only [φ] using hT
    · have hxz : x + (φ T p - x) = φ T p := by abel
      rw [hxz]
      exact φ.toAddAction.mem_orbit_vadd T p
  · intro p hp
    obtain ⟨z, hp⟩ := mem_iUnion.1 hp
    obtain ⟨hz, hp⟩ := mem_iUnion.1 hp
    rw [_root_.Flow.mem_orbit_iff] at hp
    obtain ⟨t, rfl⟩ := hp
    exact Flow.isInvariant_stableSet φ x t
      (image_add_localInvariantSet_Ici_subset_stableSet hf Q hconv ⟨z, hz, rfl⟩)

/-- A backward local invariant set whose confined trajectories converge generates the whole global
unstable set under the negative-gradient flow. -/
theorem unstableSet_eq_biUnion_orbit_localInvariantSet_Iic
    (hf : LipschitzWith K (∇ f)) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho)
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) →
      MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (nhds 0)) :
    Flow.unstableSet (negativeGradientFlow f hf) x =
      ⋃ z ∈ localInvariantSet f x (Iic 0) Q r rho,
        (negativeGradientFlow f hf).orbit (x + z) := by
  let φ := negativeGradientFlow f hf
  apply Subset.antisymm
  · intro p hp
    obtain ⟨T, hT⟩ :=
      exists_negativeGradientFlow_sub_mem_localInvariantSet_Iic_of_mem_unstableSet
        hf Q hr hrho hp
    refine mem_iUnion.2 ⟨φ T p - x, mem_iUnion.2 ⟨?_, ?_⟩⟩
    · simpa only [φ] using hT
    · have hxz : x + (φ T p - x) = φ T p := by abel
      rw [hxz]
      exact φ.toAddAction.mem_orbit_vadd T p
  · intro p hp
    obtain ⟨z, hp⟩ := mem_iUnion.1 hp
    obtain ⟨hz, hp⟩ := mem_iUnion.1 hp
    rw [_root_.Flow.mem_orbit_iff] at hp
    obtain ⟨t, rfl⟩ := hp
    exact Flow.isInvariant_unstableSet φ x t
      (image_add_localInvariantSet_Iic_subset_unstableSet hf Q hconv ⟨z, hz, rfl⟩)

variable [FiniteDimensional ℝ E]

namespace IsNondegenerateCriticalPoint

/-- Membership in the local stable set is equivalent to confinement of the global
negative-gradient orbit together with the stable-projection cutoff. -/
theorem mem_localStableSet_iff_negativeGradientFlow
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ} {z : E} :
    z ∈ h.localStableSet r rho ↔
      (∀ t, 0 ≤ t → negativeGradientFlow f hf t (x + z) - x ∈ closedBall 0 r) ∧
        ‖h.stableProjection z‖ ≤ rho := by
  rw [localStableSet_eq_localInvariantSet]
  exact mem_localInvariantSet_Ici_iff_negativeGradientFlow hf h.stableProjection

/-- Membership in the local unstable set is equivalent to confinement of the global
negative-gradient orbit together with the unstable-projection cutoff. -/
theorem mem_localUnstableSet_iff_negativeGradientFlow
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ} {z : E} :
    z ∈ h.localUnstableSet r rho ↔
      (∀ t, t ≤ 0 → negativeGradientFlow f hf t (x + z) - x ∈ closedBall 0 r) ∧
        ‖h.unstableProjection z‖ ≤ rho := by
  rw [localUnstableSet_eq_localInvariantSet]
  exact mem_localInvariantSet_Iic_iff_negativeGradientFlow hf h.unstableProjection

/-- A local stable set whose confined trajectories converge generates the whole global stable set
under the negative-gradient flow. -/
theorem stableSet_eq_biUnion_orbit_localStableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho)
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) →
      MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (nhds 0)) :
    Flow.stableSet (negativeGradientFlow f hf) x =
      ⋃ z ∈ h.localStableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  rw [localStableSet_eq_localInvariantSet]
  exact stableSet_eq_biUnion_orbit_localInvariantSet_Ici
    hf h.stableProjection hr hrho hconv

/-- A local unstable set whose confined trajectories converge backward generates the whole global
unstable set under the negative-gradient flow. -/
theorem unstableSet_eq_biUnion_orbit_localUnstableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho)
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) →
      MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (nhds 0)) :
    Flow.unstableSet (negativeGradientFlow f hf) x =
      ⋃ z ∈ h.localUnstableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  rw [localUnstableSet_eq_localInvariantSet]
  exact unstableSet_eq_biUnion_orbit_localInvariantSet_Iic
    hf h.unstableProjection hr hrho hconv

/-- There are positive radii for which the local stable set generates the whole global stable set
under the negative-gradient flow. -/
theorem exists_stableSet_eq_biUnion_orbit_localStableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) :
    ∃ r > 0, ∃ rho > 0,
      Flow.stableSet (negativeGradientFlow f hf) x =
        ⋃ z ∈ h.localStableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  obtain ⟨r, hr, rho, hrho, _, _, _, _, _, _, _, _, hconv⟩ :=
    h.exists_localStableSet_eq_lipschitzGraph 1 one_pos
  exact ⟨r, hr, rho, hrho, h.stableSet_eq_biUnion_orbit_localStableSet hf hr hrho hconv⟩

/-- There are positive radii for which the local unstable set generates the whole global unstable
set under the negative-gradient flow. -/
theorem exists_unstableSet_eq_biUnion_orbit_localUnstableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) :
    ∃ r > 0, ∃ rho > 0,
      Flow.unstableSet (negativeGradientFlow f hf) x =
        ⋃ z ∈ h.localUnstableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  obtain ⟨r, hr, rho, hrho, _, _, _, _, _, _, _, _, hconv⟩ :=
    h.exists_localUnstableSet_eq_lipschitzGraph 1 one_pos
  exact ⟨r, hr, rho, hrho, h.unstableSet_eq_biUnion_orbit_localUnstableSet hf hr hrho hconv⟩

end IsNondegenerateCriticalPoint

end TauCeti

end
