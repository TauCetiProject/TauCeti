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

* `IsNondegenerateCriticalPoint.stableSet_eq_iUnion_orbit_localStableSet`: a local stable set
  whose confined trajectories converge generates the global stable set under the flow.
* `IsNondegenerateCriticalPoint.unstableSet_eq_iUnion_orbit_localUnstableSet`: the backward-time
  counterpart.
* `IsNondegenerateCriticalPoint.exists_stableSet_eq_iUnion_orbit_lipschitzGraph` and
  `IsNondegenerateCriticalPoint.exists_unstableSet_eq_iUnion_orbit_lipschitzGraph`: choose the
  disks from the local Lyapunov--Perron graph theorem.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter InnerProductSpace Metric Set Topology
open scoped Gradient NNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {x : E} {K : ℝ≥0}

namespace IsNondegenerateCriticalPoint

private theorem lipschitzWith_centeredNegativeGradient (hf : LipschitzWith K (∇ f)) :
    LipschitzWith K (fun z ↦ (-∇ f) (x + z)) := by
  intro z w
  simpa only [edist_dist, dist_add_left] using hf.neg (x + z) (x + w)

private theorem isIntegralCurve_centeredNegativeGradientFlow (hf : LipschitzWith K (∇ f))
    (z : E) :
    IsIntegralCurve
      (fun t ↦ negativeGradientFlow f hf t (x + z) - x)
      (fun _ w ↦ (-∇ f) (x + w)) := by
  intro t
  have ht := (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve (x + z) t
  have harg : x + (negativeGradientFlow f hf t (x + z) - x) =
      negativeGradientFlow f hf t (x + z) := by abel
  simpa only [harg, Pi.neg_apply] using ht.sub_const x

private theorem eq_centeredNegativeGradientFlow_of_isIntegralCurveOn_Ici
    (hf : LipschitzWith K (∇ f)) {z : E} {y : ℝ → E}
    (hy : IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0))
    (hy0 : y 0 = z) {t : ℝ} (ht : 0 ≤ t) :
    y t = negativeGradientFlow f hf t (x + z) - x := by
  let γ : ℝ → E := fun s ↦ negativeGradientFlow f hf s (x + z) - x
  have hγ : IsIntegralCurve γ (fun _ w ↦ (-∇ f) (x + w)) :=
    isIntegralCurve_centeredNegativeGradientFlow hf z
  have hinit : y 0 = γ 0 := by
    simp only [γ, hy0, _root_.Flow.map_zero_apply, add_sub_cancel_left]
  have heq := ODE_solution_unique (a := 0) (b := t)
      (v := fun _ w ↦ (-∇ f) (x + w))
      (fun _ ↦ lipschitzWith_centeredNegativeGradient hf)
      (hy.continuousOn.mono fun _ hs ↦ hs.1)
      (fun s hs ↦ (hy s (by exact hs.1)).mono fun u hu ↦ le_trans hs.1 hu)
      (hγ.continuous.continuousOn)
      (fun s _ ↦ (hγ s).hasDerivWithinAt) hinit
  exact heq ⟨ht, le_rfl⟩

private theorem eq_centeredNegativeGradientFlow_of_isIntegralCurveOn_Iic
    (hf : LipschitzWith K (∇ f)) {z : E} {y : ℝ → E}
    (hy : IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0))
    (hy0 : y 0 = z) {t : ℝ} (ht : t ≤ 0) :
    y t = negativeGradientFlow f hf t (x + z) - x := by
  let γ : ℝ → E := fun s ↦ negativeGradientFlow f hf s (x + z) - x
  have hγ : IsIntegralCurve γ (fun _ w ↦ (-∇ f) (x + w)) :=
    isIntegralCurve_centeredNegativeGradientFlow hf z
  have hinit : y 0 = γ 0 := by
    simp only [γ, hy0, _root_.Flow.map_zero_apply, add_sub_cancel_left]
  have heq := ODE_solution_unique_of_mem_Icc_left (a := t) (b := 0)
      (v := fun _ w ↦ (-∇ f) (x + w)) (s := fun _ ↦ univ)
      (K := K) (fun _ _ ↦ (lipschitzWith_centeredNegativeGradient hf).lipschitzOnWith)
      (hy.continuousOn.mono fun _ hs ↦ hs.2)
      (fun s hs ↦ (hy s (by exact hs.2)).mono fun u hu ↦ le_trans hu hs.2)
      (fun _ _ ↦ mem_univ _) (hγ.continuous.continuousOn)
      (fun s _ ↦ (hγ s).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) hinit
  exact heq ⟨le_rfl, ht⟩

/-- Translating a local stable set back to the critical point gives points in the global stable
set, provided every trajectory confined to the chosen ball converges to the critical point. -/
theorem image_add_localStableSet_subset_stableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ}
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) →
      MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (nhds 0)) :
    (fun z ↦ x + z) '' h.localStableSet r rho ⊆
      Flow.stableSet (negativeGradientFlow f hf) x := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Flow.mem_stableSet, ← tendsto_sub_nhds_zero_iff]
  rw [mem_localStableSet] at hz
  obtain ⟨⟨y, hy, hy0, hmaps⟩, -⟩ := hz
  apply (hconv y hy hmaps).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact eq_centeredNegativeGradientFlow_of_isIntegralCurveOn_Ici (x := x) hf hy hy0 ht

/-- Translating a local unstable set back to the critical point gives points in the global
unstable set, provided every trajectory confined to the chosen ball converges backward to the
critical point. -/
theorem image_add_localUnstableSet_subset_unstableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ}
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) →
      MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (nhds 0)) :
    (fun z ↦ x + z) '' h.localUnstableSet r rho ⊆
      Flow.unstableSet (negativeGradientFlow f hf) x := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Flow.mem_unstableSet, ← tendsto_sub_nhds_zero_iff]
  rw [mem_localUnstableSet] at hz
  obtain ⟨⟨y, hy, hy0, hmaps⟩, -⟩ := hz
  apply (hconv y hy hmaps).congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  exact eq_centeredNegativeGradientFlow_of_isIntegralCurveOn_Iic (x := x) hf hy hy0 ht

/-- A local stable set whose confined trajectories converge generates the whole global stable
set under the negative-gradient flow. Every globally convergent orbit eventually enters the local
set, while uniqueness shows that every point of the local set is globally convergent. -/
theorem stableSet_eq_iUnion_orbit_localStableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho)
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) →
      MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (nhds 0)) :
    Flow.stableSet (negativeGradientFlow f hf) x =
      ⋃ z ∈ h.localStableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  let φ := negativeGradientFlow f hf
  apply Subset.antisymm
  · intro p hp
    have hp' : Tendsto (fun t ↦ φ t p) atTop (nhds x) := by
      simpa only [φ] using Flow.mem_stableSet.mp hp
    -- A convergent orbit eventually satisfies both bounds defining the local stable set.
    have hcentered : Tendsto (fun t ↦ φ t p - x) atTop (nhds 0) :=
      tendsto_sub_nhds_zero_iff.mpr hp'
    have hball : ∀ᶠ t in atTop, φ t p - x ∈ closedBall 0 r :=
      hcentered.eventually (closedBall_mem_nhds 0 hr)
    have hproj : Tendsto (fun t ↦ h.stableProjection (φ t p - x)) atTop (nhds 0) := by
      have hpmap := h.stableProjection.continuous.continuousAt.tendsto.comp hcentered
      rw [map_zero] at hpmap
      have hcomp : (fun t ↦ h.stableProjection (φ t p - x)) =
          (h.stableProjection : E → E) ∘ fun t ↦ φ t p - x := rfl
      rw [hcomp]
      exact hpmap
    have hprojBall : ∀ᶠ t in atTop, h.stableProjection (φ t p - x) ∈ closedBall 0 rho :=
      hproj.eventually (closedBall_mem_nhds 0 hrho)
    obtain ⟨T, hT⟩ := (eventually_atTop.1 (hball.and hprojBall))
    let z := φ T p - x
    -- The orbit shifted by `T` is the confined trajectory witnessing local membership.
    have hz : z ∈ h.localStableSet r rho := by
      rw [mem_localStableSet]
      refine ⟨⟨fun s ↦ φ s (φ T p) - x, ?_, ?_, ?_⟩, ?_⟩
      · have hxz : x + (φ T p - x) = φ T p := by abel
        simpa only [φ, hxz] using
          (isIntegralCurve_centeredNegativeGradientFlow (x := x) hf
            (φ T p - x)).isIntegralCurveOn
            (Ici 0)
      · simp only [_root_.Flow.map_zero_apply, z]
      · intro s hs
        simpa only [φ, ← _root_.Flow.map_add, add_comm s T] using
          (hT (T + s) (le_add_of_nonneg_right hs)).1
      · simpa only [z, mem_closedBall, dist_zero_right] using (hT T le_rfl).2
    refine mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨hz, ?_⟩⟩
    rw [_root_.Flow.mem_orbit_iff]
    refine ⟨-T, ?_⟩
    have hxz : x + z = φ T p := by dsimp only [z]; abel
    rw [hxz, ← (negativeGradientFlow f hf).map_add]
    simp
  · intro p hp
    obtain ⟨z, hp⟩ := mem_iUnion.1 hp
    obtain ⟨hz, hp⟩ := mem_iUnion.1 hp
    rw [_root_.Flow.mem_orbit_iff] at hp
    obtain ⟨t, rfl⟩ := hp
    exact Flow.isInvariant_stableSet φ x t
      (h.image_add_localStableSet_subset_stableSet hf hconv ⟨z, hz, rfl⟩)

/-- A local unstable set whose confined trajectories converge backward generates the whole
global unstable set under the negative-gradient flow. -/
theorem unstableSet_eq_iUnion_orbit_localUnstableSet
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) {r rho : ℝ}
    (hr : 0 < r) (hrho : 0 < rho)
    (hconv : ∀ y : ℝ → E,
      IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) →
      MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (nhds 0)) :
    Flow.unstableSet (negativeGradientFlow f hf) x =
      ⋃ z ∈ h.localUnstableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  let φ := negativeGradientFlow f hf
  apply Subset.antisymm
  · intro p hp
    have hp' : Tendsto (fun t ↦ φ t p) atBot (nhds x) := by
      simpa only [φ] using Flow.mem_unstableSet.mp hp
    -- A backward-convergent orbit eventually satisfies both local unstable-set bounds.
    have hcentered : Tendsto (fun t ↦ φ t p - x) atBot (nhds 0) :=
      tendsto_sub_nhds_zero_iff.mpr hp'
    have hball : ∀ᶠ t in atBot, φ t p - x ∈ closedBall 0 r :=
      hcentered.eventually (closedBall_mem_nhds 0 hr)
    have hproj : Tendsto (fun t ↦ h.unstableProjection (φ t p - x)) atBot (nhds 0) := by
      have hpmap := h.unstableProjection.continuous.continuousAt.tendsto.comp hcentered
      rw [map_zero] at hpmap
      have hcomp : (fun t ↦ h.unstableProjection (φ t p - x)) =
          (h.unstableProjection : E → E) ∘ fun t ↦ φ t p - x := rfl
      rw [hcomp]
      exact hpmap
    have hprojBall : ∀ᶠ t in atBot, h.unstableProjection (φ t p - x) ∈ closedBall 0 rho :=
      hproj.eventually (closedBall_mem_nhds 0 hrho)
    obtain ⟨T, hT⟩ := (eventually_atBot.1 (hball.and hprojBall))
    let z := φ T p - x
    -- The orbit shifted by `T` is the confined backward trajectory witnessing membership.
    have hz : z ∈ h.localUnstableSet r rho := by
      rw [mem_localUnstableSet]
      refine ⟨⟨fun s ↦ φ s (φ T p) - x, ?_, ?_, ?_⟩, ?_⟩
      · have hxz : x + (φ T p - x) = φ T p := by abel
        simpa only [φ, hxz] using
          (isIntegralCurve_centeredNegativeGradientFlow (x := x) hf
            (φ T p - x)).isIntegralCurveOn
            (Iic 0)
      · simp only [_root_.Flow.map_zero_apply, z]
      · intro s hs
        simpa only [φ, ← _root_.Flow.map_add, add_comm s T] using
          (hT (T + s) (add_le_of_nonpos_right hs)).1
      · simpa only [z, mem_closedBall, dist_zero_right] using (hT T le_rfl).2
    refine mem_iUnion.2 ⟨z, mem_iUnion.2 ⟨hz, ?_⟩⟩
    rw [_root_.Flow.mem_orbit_iff]
    refine ⟨-T, ?_⟩
    have hxz : x + z = φ T p := by dsimp only [z]; abel
    rw [hxz, ← (negativeGradientFlow f hf).map_add]
    simp
  · intro p hp
    obtain ⟨z, hp⟩ := mem_iUnion.1 hp
    obtain ⟨hz, hp⟩ := mem_iUnion.1 hp
    rw [_root_.Flow.mem_orbit_iff] at hp
    obtain ⟨t, rfl⟩ := hp
    exact Flow.isInvariant_unstableSet φ x t
      (h.image_add_localUnstableSet_subset_unstableSet hf hconv ⟨z, hz, rfl⟩)

/-- The global stable set is generated by the flow orbits through a local Lipschitz graph tangent
to the stable Hessian subspace. -/
theorem exists_stableSet_eq_iUnion_orbit_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) (C : ℝ≥0) (hC : 0 < C) :
    ∃ r > 0, ∃ rho > 0, ∃ g : E → E,
      LipschitzWith C g ∧ g 0 = 0 ∧
      HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ v, h.stableProjection (g v) = 0) ∧
      (∀ v, g (h.stableProjection v) = g v) ∧
      h.localStableSet r rho =
        (fun v ↦ v + g v) '' ((h.contDiffAt.stableLinearSubspace : Set E) ∩ closedBall 0 rho) ∧
      Flow.stableSet (negativeGradientFlow f hf) x =
        ⋃ z ∈ h.localStableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  obtain ⟨r, hr, rho, hrho, g, hg, hg0, hgd, hgker, hgmap, hgraph, hconv⟩ :=
    h.exists_localStableSet_eq_lipschitzGraph C hC
  refine ⟨r, hr, rho, hrho, g, hg, hg0, hgd, hgker, hgmap, hgraph, ?_⟩
  exact h.stableSet_eq_iUnion_orbit_localStableSet hf hr hrho hconv

/-- The global unstable set is generated by the flow orbits through a local Lipschitz graph tangent
to the unstable Hessian subspace. -/
theorem exists_unstableSet_eq_iUnion_orbit_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) (hf : LipschitzWith K (∇ f)) (C : ℝ≥0) (hC : 0 < C) :
    ∃ r > 0, ∃ rho > 0, ∃ g : E → E,
      LipschitzWith C g ∧ g 0 = 0 ∧
      HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ v, h.unstableProjection (g v) = 0) ∧
      (∀ v, g (h.unstableProjection v) = g v) ∧
      h.localUnstableSet r rho =
        (fun v ↦ v + g v) '' ((h.contDiffAt.unstableLinearSubspace : Set E) ∩ closedBall 0 rho) ∧
      Flow.unstableSet (negativeGradientFlow f hf) x =
        ⋃ z ∈ h.localUnstableSet r rho, (negativeGradientFlow f hf).orbit (x + z) := by
  obtain ⟨r, hr, rho, hrho, g, hg, hg0, hgd, hgker, hgmap, hgraph, hconv⟩ :=
    h.exists_localUnstableSet_eq_lipschitzGraph C hC
  refine ⟨r, hr, rho, hrho, g, hg, hg0, hgd, hgker, hgmap, hgraph, ?_⟩
  exact h.unstableSet_eq_iUnion_orbit_localUnstableSet hf hr hrho hconv

end IsNondegenerateCriticalPoint

end TauCeti

end
