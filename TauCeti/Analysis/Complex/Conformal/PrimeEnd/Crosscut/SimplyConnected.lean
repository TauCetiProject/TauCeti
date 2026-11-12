/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Basic
public import TauCeti.Analysis.Complex.ContinuousLog.Basic
public import TauCeti.Topology.Path.Separation
import Mathlib.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.ContinuousLog.Complement
import TauCeti.Analysis.Complex.PlaneSeparation.Basic

/-!
# A crosscut disconnects a simply connected domain

If `γ` is a crosscut of an open set `U ⊆ ℂ` that is simply connected, then removing the range of
`γ` from `U` leaves a set that is not preconnected: some two points of `U` are separated by `γ`.
This is the existence half of the statement that a crosscut of a simply connected domain cuts it
into exactly two pieces. It is what makes the sides of a crosscut, and hence the nested domains of
a prime-end chain, meaningful.

Simple connectivity is essential. A radial segment across an annulus is a crosscut that leaves the
annulus connected.

## The argument

Let `x` and `y` be the endpoints of `γ`. They lie outside the open set `U`, so on a simply
connected `U` the Borsuk map `h z = (z - x) / (z - y)` has a continuous logarithm. It also has a
continuous logarithm off the range of `γ`, because `γ` joins `x` to `y`
(`Path.hasContinuousLogOn_sub_div_sub_compl_range`). If `U \ range γ` were preconnected, then
the two logarithms would glue along it to a continuous logarithm of `h` on `U ∪ (range γ)ᶜ`
(`TauCeti.HasContinuousLogOn.union_of_isOpen`). The range of a crosscut meets the complement of
`U` only at `x` and `y`, so `U ∪ (range γ)ᶜ` contains a small circle about `x`. By Borsuk's
criterion (`TauCeti.mem_connectedComponentIn_of_hasContinuousLogOn`) that circle would then fail
to separate `x` from `y`, which is absurd.

The proof uses simple connectivity only through the logarithm of `h` on `U`, and
`Path.IsCrosscut.not_isPreconnected_sdiff_range_of_hasContinuousLogOn` records this sharper
form.

## Main results

* `Path.IsCrosscut.not_isPreconnected_sdiff_range_of_hasContinuousLogOn` — a crosscut whose
  endpoint Borsuk map has a continuous logarithm on `U` disconnects `U`.
* `Path.IsCrosscut.not_isPreconnected_sdiff_range` — a crosscut of a simply connected open set
  disconnects it.
* `Path.IsCrosscut.exists_separatesIn` — the same statement in terms of `Path.SeparatesIn`.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Chapter 2.
* M. H. A. Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V.
-/

public section

open Complex Metric Set TauCeti

namespace Path

variable {x y : ℂ} {γ : Path x y} {U : Set ℂ}

/-- **A crosscut disconnects a domain carrying a logarithm of its endpoint Borsuk map.** Let `γ` be
a crosscut from `x` to `y` of an open set `U`, and suppose `z ↦ (z - x) / (z - y)` has a continuous
logarithm on `U`. Then `U \ range γ` is not preconnected. -/
theorem IsCrosscut.not_isPreconnected_sdiff_range_of_hasContinuousLogOn (hγ : IsCrosscut γ U)
    (hU : IsOpen U) (hlog : HasContinuousLogOn (fun z => (z - x) / (z - y)) U) :
    ¬ IsPreconnected (U \ range γ) := by
  intro hpre
  have hS : IsClosed (range γ) := (isCompact_range γ.continuous).isClosed
  -- the logarithms on `U` and off `range γ` glue along the preconnected overlap `U \ range γ`
  have hglue : HasContinuousLogOn (fun z => (z - x) / (z - y)) (U ∪ (range γ)ᶜ) :=
    hlog.union_of_isOpen hU hS.isOpen_compl (by rwa [← sdiff_eq])
      γ.hasContinuousLogOn_sub_div_sub_compl_range
  -- a small circle about `x` lies in `U ∪ (range γ)ᶜ` and separates `x` from `y`
  set r := dist y x / 2 with hrdef
  have hr : 0 < r := half_pos (dist_pos.mpr hγ.source_ne_target.symm)
  have hsph : sphere x r ⊆ U ∪ (range γ)ᶜ := by
    intro z hz
    by_contra hzc
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hzc
    have hzfr : z ∈ frontier U := hU.frontier_eq ▸ ⟨hγ.range_subset_closure hzc.2, hzc.1⟩
    rcases (hγ.range_inter_frontier hU).subset ⟨hzc.2, hzfr⟩ with rfl | rfl
    · rw [mem_sphere, dist_self] at hz
      exact hr.ne hz
    · rw [mem_sphere] at hz
      linarith [hz, hrdef]
  have hyx := mem_connectedComponentIn_of_hasContinuousLogOn isClosed_sphere isBounded_sphere
    (hglue.mono hsph)
  have hxx : x ∈ connectedComponentIn (sphere x r)ᶜ x :=
    mem_connectedComponentIn (by simpa [mem_sphere, eq_comm] using hr.ne)
  obtain ⟨z, hz, hzr⟩ := isPreconnected_connectedComponentIn.intermediate_value hxx hyx
    (continuous_id.dist continuous_const).continuousOn
    (⟨by rw [dist_self]; exact hr.le, by linarith [hrdef]⟩ : r ∈ Icc (dist x x) (dist y x))
  exact connectedComponentIn_subset _ _ hz (mem_sphere.mpr hzr)

/-- **A crosscut disconnects a simply connected domain.** If `γ` is a crosscut of a simply
connected open set `U ⊆ ℂ`, then `U \ range γ` is not preconnected. -/
theorem IsCrosscut.not_isPreconnected_sdiff_range (hγ : IsCrosscut γ U) (hUo : IsOpen U)
    (hUs : IsSimplyConnected U) : ¬ IsPreconnected (U \ range γ) := by
  have hxU : x ∉ U := fun hx => (hUo.frontier_eq ▸ hγ.source_mem_frontier).2 hx
  have hyU : y ∉ U := fun hy => (hUo.frontier_eq ▸ hγ.target_mem_frontier).2 hy
  have hy : ∀ z ∈ U, z - y ≠ 0 := fun z hz h0 => hyU (sub_eq_zero.mp h0 ▸ hz)
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (g := fun z => (z - x) / (z - y)) hUs hUo
    ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const) hy)
    (by
      rintro ⟨z, hz, h0⟩
      have hx : z - x ≠ 0 := sub_ne_zero.mpr fun h => hxU (h ▸ hz)
      exact div_ne_zero hx (hy z hz) h0)
  exact hγ.not_isPreconnected_sdiff_range_of_hasContinuousLogOn hUo
    (hasContinuousLogOn_iff.mpr ⟨L, hLc, fun z hz => hL hz⟩)

/-- **A crosscut of a simply connected domain separates two of its points.** -/
theorem IsCrosscut.exists_separatesIn (hγ : IsCrosscut γ U) (hUo : IsOpen U)
    (hUs : IsSimplyConnected U) : ∃ z w, γ.SeparatesIn U z w :=
  (exists_separatesIn_iff_not_isPreconnected γ U).mpr
    (hγ.not_isPreconnected_sdiff_range hUo hUs)

end Path
