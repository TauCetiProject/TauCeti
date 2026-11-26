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
import TauCeti.Topology.OmegaLimit

/-!
# Convergence of the orbits of a flow with a Lyapunov function

Let `φ` be a flow of `ℝ` on a compact Hausdorff space and `g` a continuous function that is
antitone along an orbit. Suppose that the cluster points of this orbit along whose own orbit `g` is
constant are contained in a finite set `C`. Then the orbit converges, forward in time, to a point of
`C`; the same holds backward in time.

This is the topological core of the convergence of gradient-like flows: for the flow of a
pseudo-gradient field adapted to a Morse function `f`, the function is `f` and `C` is the finite
set of critical points.

Along an orbit converging to `x`, a function antitone along orbits stays above its value at `x`
in forward time and below it in backward time. Hence a strict maximum of the function is a fixed
point with trivial stable set, and a strict minimum is a fixed point with trivial unstable set.

## Main declarations

* `Flow.exists_tendsto_atTop_of_antitone` and `Flow.exists_tendsto_atBot_of_antitone`: an orbit
  converges forward, and backward, in time to a point of `C`.
* `Flow.isGLB_of_mapClusterPt_of_antitone` and `Flow.apply_flow_eq_of_mapClusterPt_of_antitone`:
  at a cluster point of the forward orbit, the function takes the infimum of its values along the
  orbit, and it is constant along the orbit of this cluster point.
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

/-- **A Lyapunov function attains its infimum along an orbit at the cluster points.** If `g` is
antitone along the orbit of `y` and continuous at a cluster point `x` of the forward orbit, then
`g x` is the greatest lower bound of the values of `g` along the orbit. -/
theorem isGLB_of_mapClusterPt_of_antitone (hanti : Antitone fun t ↦ g (φ t y))
    (hg : ContinuousAt g x) (hx : MapClusterPt x atTop fun t ↦ φ t y) :
    IsGLB (range fun t ↦ g (φ t y)) (g x) := by
  -- `g x` is a cluster value of `g` along the orbit, hence lies in every closed set that eventually
  -- contains these values.
  have hcl : MapClusterPt (g x) atTop fun t ↦ g (φ t y) := hx.continuousAt_comp hg
  refine ⟨?_, fun b hb ↦ ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact isClosed_Iic.mem_of_mapClusterPt hcl ((eventually_ge_atTop t).mono fun s hs ↦ hanti hs)
  · exact isClosed_Ici.mem_of_mapClusterPt hcl (.of_forall fun s ↦ hb ⟨s, rfl⟩)

/-- **A Lyapunov function is constant along the orbit of a cluster point.** If `g` is continuous
and antitone along the orbit of `y`, it is constant along the orbit of every cluster point `x` of
the forward orbit of `y`, as that orbit consists of cluster points. -/
theorem apply_flow_eq_of_mapClusterPt_of_antitone (hanti : Antitone fun t ↦ g (φ t y))
    (hg : Continuous g) (hx : MapClusterPt x atTop fun t ↦ φ t y) (t : ℝ) : g (φ t x) = g x :=
  (isGLB_of_mapClusterPt_of_antitone hanti hg.continuousAt (mapClusterPt_atTop_flow hx t)).unique
    (isGLB_of_mapClusterPt_of_antitone hanti hg.continuousAt hx)

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

/-- **The orbits of a flow with a Lyapunov function converge.** Let `g` be a continuous function
on a compact Hausdorff space, antitone along the orbit of `y` under a flow `φ` of `ℝ`. If the
cluster points of the forward orbit of `y` along whose own orbit `g` is constant are contained in a
finite set `C`, the orbit of `y` converges forward in time to a point of `C`. -/
theorem exists_tendsto_atTop_of_antitone (φ : Flow ℝ α) {g : α → ℝ} (hg : Continuous g) (y : α)
    (hanti : Antitone fun t ↦ g (φ t y)) {C : Set α} (hC : C.Finite)
    (hrest : ∀ z, MapClusterPt z atTop (fun t ↦ φ t y) → (∀ t, g (φ t z) = g z) → z ∈ C) :
    ∃ x ∈ C, Tendsto (fun t ↦ φ t y) atTop (𝓝 x) := by
  have hγc : Continuous fun t ↦ φ t y := φ.continuous continuous_id continuous_const
  -- The cluster points of the orbit form its ω-limit set, which is invariant under the flow;
  -- `g` is constant along it, so every cluster point lies in `C`.
  have hsub : {z | MapClusterPt z atTop fun t ↦ φ t y} ⊆ C := fun z hz ↦
    hrest z hz (apply_flow_eq_of_mapClusterPt_of_antitone hanti hg hz)
  exact TauCeti.exists_tendsto_atTop_of_setOf_mapClusterPt_subset (a := 0) isCompact_univ
    hγc.continuousOn (mapsTo_univ _ _) hC hsub

/-- **The orbits of a flow with a Lyapunov function converge backward in time.** Let `g` be a
continuous function on a compact Hausdorff space, antitone along the orbit of `y` under a flow `φ`
of `ℝ`. If the cluster points of the backward orbit of `y` along whose own orbit `g` is constant are
contained in a finite set `C`, the orbit of `y` converges backward in time to a point of `C`. -/
theorem exists_tendsto_atBot_of_antitone (φ : Flow ℝ α) {g : α → ℝ} (hg : Continuous g) (y : α)
    (hanti : Antitone fun t ↦ g (φ t y)) {C : Set α} (hC : C.Finite)
    (hrest : ∀ z, MapClusterPt z atBot (fun t ↦ φ t y) → (∀ t, g (φ t z) = g z) → z ∈ C) :
    ∃ x ∈ C, Tendsto (fun t ↦ φ t y) atBot (𝓝 x) := by
  -- Apply the forward convergence to the reversed flow, along which `-g` is antitone.
  obtain ⟨x, hx, hlim⟩ := exists_tendsto_atTop_of_antitone φ.reverse hg.neg y
    (antitone_reverse_neg hanti) hC fun z hz hconst ↦ hrest z
      (by
        rw [← map_neg_atTop, ← mapClusterPt_comp]
        simpa only [Function.comp_def, _root_.Flow.reverse_apply] using hz) fun t ↦ by
        simpa only [_root_.Flow.reverse_apply, neg_neg, Pi.neg_apply, neg_inj] using hconst (-t)
  refine ⟨x, hx, ?_⟩
  simpa only [Function.comp_def, _root_.Flow.reverse_apply, neg_neg] using
    hlim.comp tendsto_neg_atBot_atTop

end Flow
