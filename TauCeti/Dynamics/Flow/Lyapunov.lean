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
antitone along every orbit. Suppose that the points along whose orbit `g` is constant are contained
in a finite set `C`. Then every orbit converges, forward in time, to a point of `C`.

This is the topological core of the convergence of gradient-like flows: for the flow of a
pseudo-gradient field adapted to a Morse function `f`, the function is `f` and `C` is the finite
set of critical points.

Along an orbit converging to `x`, a function antitone along orbits stays above its value at `x`
in forward time and below it in backward time. Crossing times of levels are continuous: near a
point along whose orbit the function strictly decreases, nearby orbits cross its level at nearby
times. Hence a strict maximum of the function is a fixed
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
* `Flow.tendsto_zero_of_apply_eq_of_antitone` and `Flow.tendsto_apply_of_apply_eq_of_antitone`:
  if `u i → w` and `g` is strictly antitone along the orbit of `w`, the times and points at which
  the orbits of the `u i` cross the level of `w` converge to `0` and to `w`.

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

section Crossing

variable {φ : Flow ℝ α} {g : α → ℝ} {w : α} {ι : Type*} {l : Filter ι} {u : ι → α} {s : ι → ℝ}

/-- **Crossing times of a level converge.** Let `g` be continuous and antitone along every orbit
of `φ`, and strictly antitone along the orbit of `w`. If `u i → w` and the orbit of `u i` meets the
level of `w` at time `s i`, then `s i → 0`. No smoothness is needed, and the times `s i` are not
assumed to be close to anything in advance, unlike the local implicit-function hitting time
`TauCeti.flowHittingTime`: monotonicity along the orbits forces them to `0`. -/
theorem tendsto_zero_of_apply_eq_of_antitone (hg : Continuous g)
    (hanti : ∀ y, Antitone fun t ↦ g (φ t y)) (hw : StrictAnti fun t ↦ g (φ t w))
    (hu : Tendsto u l (𝓝 w)) (hs : ∀ᶠ i in l, g (φ (s i) (u i)) = g w) :
    Tendsto s l (𝓝 0) := by
  have hval (t : ℝ) : Tendsto (fun i ↦ g (φ t (u i))) l (𝓝 (g (φ t w))) :=
    ((hg.comp (φ.continuous_toFun t)).tendsto w).comp hu
  refine tendsto_order.2 ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · -- Before time `t < 0` the orbit of `u i` is still above the level of `w`.
    have hlt : g w < g (φ t w) := by simpa only [map_zero_apply] using hw ht
    filter_upwards [hs, (hval t).eventually (eventually_gt_nhds hlt)] with i hi hti
    by_contra! hle
    have := hanti (u i) hle
    simp only [hi] at this
    exact this.not_gt hti
  · -- After time `t > 0` it is already below.
    have hlt : g (φ t w) < g w := by simpa only [map_zero_apply] using hw ht
    filter_upwards [hs, (hval t).eventually (eventually_lt_nhds hlt)] with i hi hti
    by_contra! hle
    have := hanti (u i) hle
    simp only [hi] at this
    exact this.not_gt hti

/-- **Crossing points of a level converge.** Under the hypotheses of
`Flow.tendsto_zero_of_apply_eq_of_antitone`, the points `φ (s i) (u i)` where the orbits of the
`u i` meet the level of `w` converge to `w`. -/
theorem tendsto_apply_of_apply_eq_of_antitone (hg : Continuous g)
    (hanti : ∀ y, Antitone fun t ↦ g (φ t y)) (hw : StrictAnti fun t ↦ g (φ t w))
    (hu : Tendsto u l (𝓝 w)) (hs : ∀ᶠ i in l, g (φ (s i) (u i)) = g w) :
    Tendsto (fun i ↦ φ (s i) (u i)) l (𝓝 w) := by
  have h := (φ.cont'.tendsto (0, w)).comp
    ((tendsto_zero_of_apply_eq_of_antitone hg hanti hw hu hs).prodMk_nhds hu)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, map_zero_apply] using h

end Crossing

variable [CompactSpace α] [T2Space α]

/-- **The orbits of a flow with a Lyapunov function converge.** Let `g` be a continuous function,
antitone along every orbit of a flow `φ` of `ℝ` on a compact Hausdorff space. If the points along
whose orbit `g` is constant are contained in a finite set `C`, every orbit converges forward in time
to a point of `C`. -/
theorem exists_tendsto_atTop_of_antitone (φ : Flow ℝ α) {g : α → ℝ} (hg : Continuous g)
    (hanti : ∀ y, Antitone fun t ↦ g (φ t y)) {C : Set α} (hC : C.Finite)
    (hrest : ∀ z, (∀ t, g (φ t z) = g z) → z ∈ C) (y : α) :
    ∃ x ∈ C, Tendsto (fun t ↦ φ t y) atTop (𝓝 x) := by
  set γ : ℝ → α := fun t ↦ φ t y
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
  exact TauCeti.exists_tendsto_atTop_of_setOf_mapClusterPt_subset (a := 0) isCompact_univ
    hγc.continuousOn (mapsTo_univ _ _) hC hsub

end Flow
