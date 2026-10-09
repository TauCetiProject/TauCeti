/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Dynamics.Flow.Stable
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

Along an orbit converging to `x`, a function antitone along orbits stays above its value at `x`
in forward time and below it in backward time. Hence a strict maximum of the function is a fixed
point with trivial stable set, and a strict minimum is a fixed point with trivial unstable set.

## Main declarations

* `Flow.exists_tendsto_atTop_of_antitone`: every orbit converges forward in time to a
  point of `C`.
* `Flow.le_of_mem_stableSet_of_antitone` and `Flow.le_of_mem_unstableSet_of_antitone`: the value
  at the limit bounds the values along the orbit.
* `Flow.fixed_of_antitone_of_strictMax` and `Flow.fixed_of_antitone_of_strictMin`: a strict
  maximum or minimum of a function antitone along orbits is a fixed point.
* `Flow.stableSet_eq_singleton_of_antitone` and `Flow.unstableSet_eq_singleton_of_antitone`:
  the stable set of a strict maximum, and the unstable set of a strict minimum, is a point.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

section Limit

variable {φ : Flow ℝ α} {g : α → ℝ} {x y : α}

/-- If the orbit of `y` converges to `x` in forward time, a function antitone along the orbit and
continuous at `x` takes at `y` a value at least its value at `x`. -/
theorem le_of_mem_stableSet_of_antitone (hy : y ∈ φ.stableSet x) (hg : ContinuousAt g x)
    (hanti : Antitone fun t ↦ g (φ t y)) : g x ≤ g y := by
  simpa only [map_zero_apply] using hanti.le_of_tendsto (hg.tendsto.comp (mem_stableSet.1 hy)) 0

/-- If the orbit of `y` converges to `x` in backward time, a function antitone along the orbit and
continuous at `x` takes at `y` a value at most its value at `x`. -/
theorem le_of_mem_unstableSet_of_antitone (hy : y ∈ φ.unstableSet x) (hg : ContinuousAt g x)
    (hanti : Antitone fun t ↦ g (φ t y)) : g y ≤ g x := by
  simpa only [map_zero_apply] using hanti.ge_of_tendsto (hg.tendsto.comp (mem_unstableSet.1 hy)) 0

/-- **A strict maximum is a fixed point.** A strict global maximum of a function antitone along
its orbit is fixed by the flow. -/
theorem fixed_of_antitone_of_strictMax (hanti : Antitone fun t ↦ g (φ t x))
    (hmax : ∀ y, y ≠ x → g y < g x) (t : ℝ) : φ t x = x := by
  -- In backward time the orbit cannot go below the maximum, and in forward time it is the inverse
  -- of a backward orbit.
  have hneg : ∀ s ≤ 0, φ s x = x := fun s hs ↦ by
    by_contra hne
    have h : g x ≤ g (φ s x) := by simpa only [map_zero_apply] using hanti hs
    exact (hmax _ hne).not_ge h
  rcases le_total t 0 with ht | ht
  · exact hneg t ht
  · calc φ t x = φ t (φ (-t) x) := by rw [hneg (-t) (neg_nonpos.2 ht)]
      _ = x := by rw [← map_add, add_neg_cancel, map_zero_apply]

/-- Reversing the flow and negating the function preserves antitonicity along an orbit. -/
private theorem antitone_reverse_neg (hanti : Antitone fun t ↦ g (φ t y)) :
    Antitone fun t ↦ (-g) (φ.reverse t y) := fun s t hst ↦ by
  simp only [reverse_apply, Pi.neg_apply]
  exact neg_le_neg (hanti (neg_le_neg hst))

/-- **A strict minimum is a fixed point.** A strict global minimum of a function antitone along
its orbit is fixed by the flow. -/
theorem fixed_of_antitone_of_strictMin (hanti : Antitone fun t ↦ g (φ t x))
    (hmin : ∀ y, y ≠ x → g x < g y) (t : ℝ) : φ t x = x := by
  have h := fixed_of_antitone_of_strictMax (antitone_reverse_neg hanti)
    (fun y hy ↦ neg_lt_neg (hmin y hy)) (-t)
  rwa [reverse_apply, neg_neg] at h

/-- **The stable set of a strict maximum is a point.** Let `g` be antitone along every orbit and
continuous at a point `x` at which it has a strict global maximum. Then no other orbit converges
to `x` in forward time. -/
theorem stableSet_eq_singleton_of_antitone (hg : ContinuousAt g x)
    (hanti : ∀ y, Antitone fun t ↦ g (φ t y)) (hmax : ∀ y, y ≠ x → g y < g x) :
    φ.stableSet x = {x} := by
  have hx := fixed_of_antitone_of_strictMax (hanti x) hmax
  refine eq_singleton_iff_unique_mem.2 ⟨mem_stableSet.2 ?_, fun y hy ↦ ?_⟩
  · simpa only [hx] using tendsto_const_nhds
  · by_contra hyx
    exact (hmax y hyx).not_ge (le_of_mem_stableSet_of_antitone hy hg (hanti y))

/-- **The unstable set of a strict minimum is a point.** Let `g` be antitone along every orbit and
continuous at a point `x` at which it has a strict global minimum. Then no other orbit converges
to `x` in backward time. -/
theorem unstableSet_eq_singleton_of_antitone (hg : ContinuousAt g x)
    (hanti : ∀ y, Antitone fun t ↦ g (φ t y)) (hmin : ∀ y, y ≠ x → g x < g y) :
    φ.unstableSet x = {x} := by
  rw [← stableSet_reverse]
  exact stableSet_eq_singleton_of_antitone hg.neg (fun y ↦ antitone_reverse_neg (hanti y))
    fun y hy ↦ neg_lt_neg (hmin y hy)

end Limit

variable [CompactSpace α] [T2Space α]

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
