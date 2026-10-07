/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Topology.Connected.TotallyDisconnected
import TauCeti.Topology.OmegaLimit

/-!
# Convergence of the orbits of a flow with a Lyapunov function

Let `φ` be a flow of `ℝ` on a compact Hausdorff space and `g` a continuous function that is
antitone along every orbit. Suppose that the points along whose orbit `g` is constant are contained
in a finite set `C`. Then every orbit converges, forward in time, to a point of `C`.

This is the topological core of the convergence of gradient-like flows: for the flow of a
pseudo-gradient field adapted to a Morse function `f`, the function is `f` and `C` is the finite
set of critical points.

## Main declarations

* `Flow.exists_tendsto_atTop_of_antitone`: every orbit converges forward in time to a
  point of `C`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α] [CompactSpace α] [T2Space α]

/-- **The orbits of a flow with a Lyapunov function converge.** Let `g` be a continuous function,
antitone along every orbit of a flow `φ` of `ℝ` on a compact Hausdorff space. If the points along
whose orbit `g` is constant are contained in a finite set `C`, every orbit converges forward in time
to a point of `C`. -/
theorem exists_tendsto_atTop_of_antitone (φ : Flow ℝ α) {g : α → ℝ} (hg : Continuous g)
    (hanti : ∀ y, Antitone fun t ↦ g (φ t y)) {C : Set α} (hC : C.Finite)
    (hrest : ∀ z, (∀ t, g (φ t z) = g z) → z ∈ C) (y : α) :
    ∃ x ∈ C, Tendsto (fun t ↦ φ t y) atTop (𝓝 x) := by
  set γ : ℝ → α := fun t ↦ φ t y with hγdef
  have hγc : Continuous γ := φ.continuous continuous_id continuous_const
  -- The values of `g` along the orbit converge.
  have hbdd : BddBelow (range fun t ↦ g (γ t)) := by
    have : Nonempty α := ⟨y⟩
    obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn univ_nonempty hg.continuousOn
    exact ⟨g m, by rintro _ ⟨t, rfl⟩; exact hm (mem_univ _)⟩
  have hlim : Tendsto (fun t ↦ g (γ t)) atTop (𝓝 (⨅ t, g (γ t))) :=
    tendsto_atTop_ciInf (hanti y) hbdd
  set c := ⨅ t, g (γ t)
  -- `g` takes the value `c` at every cluster point of the orbit.
  have hval : ∀ z, MapClusterPt z atTop γ → g z = c := by
    intro z hz
    have hcl : MapClusterPt (g z) atTop (g ∘ γ) := hz.continuousAt_comp hg.continuousAt
    have hne : NeBot (𝓝 (g z) ⊓ 𝓝 c) :=
      NeBot.mono hcl (inf_le_inf_left _ hlim)
    exact eq_of_nhds_neBot hne
  -- The cluster points of the orbit form its ω-limit set, which is invariant under the flow;
  -- hence every cluster point lies in `C`.
  have hsub : {z | MapClusterPt z atTop γ} ⊆ C := fun z hz ↦
    hrest z fun t ↦ (hval _ (mapClusterPt_atTop_flow hz t)).trans (hval z hz).symm
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_mapClusterPt (f := atTop) (u := γ)
    (by simp)
  have hconn : IsPreconnected {z | MapClusterPt z atTop γ} :=
    TauCeti.isPreconnected_setOf_mapClusterPt_atTop (a := 0) isCompact_univ hγc.continuousOn
      (mapsTo_univ _ _)
  -- A finite preconnected set is a single point.
  have hone : ∀ z ∈ univ, MapClusterPt z atTop γ → z = p := fun z _ hz ↦
    (hC.subset hsub).isTotallyDisconnected _ subset_rfl hconn hz hp
  exact ⟨p, hsub hp, isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun _ ↦ mem_univ _) hone⟩

end Flow
