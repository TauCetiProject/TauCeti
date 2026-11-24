/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Countability of separated families in separable pseudometric spaces

Any family of points mapping into a separable subset of a pseudometric space whose distinct images
are uniformly separated by a positive distance has a countable domain
(`TopologicalSpace.IsSeparable.countable_of_mapsTo_of_le_dist`).
-/

public section

open Metric Set TopologicalSpace

namespace TauCeti

/-- Any family of points mapping into a separable subset of a pseudometric space whose distinct
images are separated by at least `r > 0` has a countable domain. -/
theorem _root_.TopologicalSpace.IsSeparable.countable_of_mapsTo_of_le_dist
    {ι Y : Type*} [PseudoMetricSpace Y] {t : Set Y} (ht : TopologicalSpace.IsSeparable t)
    {s : Set ι} {u : ι → Y} (hmaps : Set.MapsTo u s t) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r ≤ dist (u i) (u j)) :
    s.Countable := by
  have : SeparableSpace t := ht.separableSpace
  have : SecondCountableTopology t := UniformSpace.secondCountable_of_separable t
  let A : Set t := {y : t | ∃ i ∈ s, u i = y.val}
  have hA_lindelof : IsLindelof A := HereditarilyLindelofSpace.isLindelof A
  have hA_discrete : IsDiscrete A := isDiscrete_iff_nhdsWithin.2 fun y hy => by
    obtain ⟨i, hi, hiy⟩ := hy
    refine le_antisymm (Filter.le_pure_iff.2 (mem_nhdsWithin.2 ⟨Subtype.val ⁻¹' ball y.val r,
      isOpen_ball.preimage continuous_subtypeVal, mem_ball_self hr, fun z hz => ?_⟩))
      (pure_le_nhdsWithin ⟨i, hi, hiy⟩)
    obtain ⟨j, hj, hjz⟩ := hz.2
    by_cases hij : i = j
    · exact Subtype.ext (hjz.symm.trans (hij ▸ hiy))
    · exfalso
      have h1 := hdist i hi j hj hij
      have h2 : dist (u i) (u j) < r := by
        simpa only [hiy, hjz, dist_comm] using mem_ball.1 hz.1
      exact h2.not_ge h1
  have hA_count : A.Countable := hA_lindelof.countable_of_isDiscrete hA_discrete
  have himg : (u '' s).Countable := by
    refine (hA_count.image Subtype.val).mono ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨⟨u i, hmaps hi⟩, ⟨i, hi, rfl⟩, rfl⟩
  have hinj : InjOn u s := fun i hi j hj hij => by
    by_contra hne
    have h1 := hdist i hi j hj hne
    rw [hij, dist_self] at h1
    exact hr.not_ge h1
  exact (mapsTo_image u s).countable_of_injOn hinj himg

end TauCeti
