/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Basic
public import TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Topology.JordanCurve.SmallArc
public import TauCeti.Topology.JordanCurve.Subcontinuum
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Complex.ContinuousLog.Path
import TauCeti.Topology.ConnectedComponents

/-!
# Arcs do not separate the plane, and a Jordan curve bounds each of its complementary components

Borsuk's criterion `TauCeti.mem_connectedComponentIn_of_hasContinuousLogOn` turns the continuous
logarithm of the Borsuk map on a simple arc
(`TauCeti.hasContinuousLogOn_sub_div_sub_range_of_injective_path`) into the classical fact that
**a simple arc does not separate the plane**. Since a proper subcontinuum of a Jordan curve is a
point or an arc, no such subcontinuum separates the plane either.

This is what shows that a Jordan curve `C ⊆ ℂ` is **adherent to every component of its
complement**, as soon as the complement has two components at all: given a point `q ∈ C` and
`r > 0`, cut out of `C` a closed arc `S` whose complement in the curve lies in `ball q r`. Two
points `x`, `y` in different components of `Cᶜ` lie in one component `D` of `Sᶜ`, so `D` must meet
`C \ S ⊆ ball q r`; walking inside `D` from the component `E` of `Cᶜ` containing `x`, one meets
the frontier of `E` in `C \ S`. Hence `E` comes within `r` of `q`. Thus the frontier of every
complementary component is the whole curve. This is the half of the Jordan curve theorem that
needs no construction of an inside. Together with the empty interior of a Jordan curve
(`TauCeti.IsJordanCurve.interior_eq_empty`) it shows that an open set contained in the filled hull
of a Jordan curve does not meet the curve: such a set, if it met the curve, would contain a point
off the curve in a bounded component, so the curve would separate the plane and the open set would
also meet the unbounded component.

## Main results

* `Path.isConnected_compl_range_of_injective` — the complement of a simple arc in the plane
  is connected.
* `TauCeti.IsJordanCurve.isConnected_compl_of_ne` — the complement of a proper subcontinuum of a
  Jordan curve in the plane is connected.
* `TauCeti.IsJordanCurve.subset_closure_connectedComponentIn` — if a Jordan curve separates two
  points, it lies in the closure of each of their complementary components.
* `TauCeti.IsJordanCurve.frontier_connectedComponentIn` — the frontier of such a component is the
  whole curve.
* `TauCeti.IsJordanCurve.disjoint_of_isOpen_of_subset_filledHull` — an open set contained in the
  filled hull of a Jordan curve misses the curve.

## References

* J. R. Munkres, *Topology*, §61–63.
* S. Janiszewski, *Sur les coupures du plan faites par les continus*, Prace Mat.-Fiz. **26**
  (1913).
-/

public section

namespace TauCeti

open Metric Set

/-- **A simple arc does not separate the plane.** The complement of the range of an injective
path in `ℂ` is connected. -/
theorem _root_.Path.isConnected_compl_range_of_injective {p q : ℂ} (γ : Path p q)
    (hγ : Function.Injective γ) : IsConnected (range γ)ᶜ := by
  have hK : IsCompact (range γ) := isCompact_range γ.continuous
  refine ⟨nonempty_compl.mpr fun h => NormedSpace.unbounded_univ ℝ ℂ (h ▸ hK.isBounded),
    isPreconnected_of_forall_pair fun a ha b hb => ?_⟩
  exact ⟨connectedComponentIn (range γ)ᶜ a, connectedComponentIn_subset _ _,
    mem_connectedComponentIn ha,
    mem_connectedComponentIn_of_hasContinuousLogOn hK.isClosed hK.isBounded
      (hasContinuousLogOn_sub_div_sub_range_of_injective_path γ hγ ha hb),
    isPreconnected_connectedComponentIn⟩

/-- **A proper subcontinuum of a Jordan curve does not separate the plane.** If `S` is a compact
preconnected subset of a Jordan curve `C ⊆ ℂ` with `S ≠ C`, then `Sᶜ` is connected. -/
theorem IsJordanCurve.isConnected_compl_of_ne {C S : Set ℂ} (h : IsJordanCurve C) (hSC : S ⊆ C)
    (hS : IsCompact S) (hpre : IsPreconnected S) (hSne : S ≠ C) : IsConnected Sᶜ := by
  -- such a subcontinuum is a point or a simple arc, and neither separates `ℂ`
  rcases h.subsingleton_or_exists_injective_path hSC hS hpre hSne with
    hsub | ⟨p, q, γ, hγ, rfl⟩
  · refine hsub.countable.isConnected_compl_of_one_lt_rank ?_
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  · exact γ.isConnected_compl_range_of_injective hγ

/-- **A Jordan curve lies in the closure of each of its complementary components.** If the Jordan
curve `C ⊆ ℂ` separates `x` from `y`, then every point of `C` is adherent to the component of `Cᶜ`
containing `x`. -/
theorem IsJordanCurve.subset_closure_connectedComponentIn {C : Set ℂ} (h : IsJordanCurve C)
    {x y : ℂ} (hx : x ∉ C) (hy : y ∉ C) (hxy : y ∉ connectedComponentIn Cᶜ x) :
    C ⊆ closure (connectedComponentIn Cᶜ x) := by
  intro q hq
  rw [Metric.mem_closure_iff]
  intro r hr
  -- cut out of `C` a closed arc `S` whose complement in the curve lies in `ball q r`
  obtain ⟨S, hSC, hS, hpre, hqS, hCS⟩ :=
    h.exists_isCompact_isPreconnected_notMem_sdiff_subset_ball hq hr
  have hxS : x ∈ Sᶜ := fun hxS => hx (hSC hxS)
  -- `S` does not separate `x` from `y`
  have hyD : y ∈ connectedComponentIn Sᶜ x :=
    (h.isConnected_compl_of_ne hSC hS hpre fun hSC' => hqS (hSC' ▸ hq)).isPreconnected
      |>.subset_connectedComponentIn hxS subset_rfl fun hyS => hy (hSC hyS)
  have hED : connectedComponentIn Cᶜ x ⊆ connectedComponentIn Sᶜ x :=
    connectedComponentIn_mono x (compl_subset_compl.mpr hSC)
  have hEo : IsOpen (connectedComponentIn Cᶜ x) :=
    h.isClosed.isOpen_compl.connectedComponentIn
  -- the component of `Sᶜ` through `x` is not contained in that of `Cᶜ`, so it meets its frontier
  obtain ⟨w, hwE, hwD, hwE'⟩ : ∃ w ∈ closure (connectedComponentIn Cᶜ x),
      w ∈ connectedComponentIn Sᶜ x ∧ w ∉ connectedComponentIn Cᶜ x := by
    by_contra! hcon
    exact hxy <| isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hEo
      ⟨x, hED (mem_connectedComponentIn hx), mem_connectedComponentIn hx⟩
      (fun w ⟨hw, hwD⟩ => hcon w hw hwD) hyD
  -- that frontier point lies on `C` but off `S`, hence in `ball q r`
  have hwC : w ∈ C := by
    have := frontier_connectedComponentIn_subset_compl h.isClosed.isOpen_compl x
      ⟨hwE, by rwa [hEo.interior_eq]⟩
    rwa [compl_compl] at this
  have hwq : w ∈ ball q r := hCS ⟨hwC, connectedComponentIn_subset _ _ hwD⟩
  obtain ⟨u, huq, huE⟩ := _root_.mem_closure_iff.mp hwE _ isOpen_ball hwq
  exact ⟨u, huE, by rw [dist_comm]; exact huq⟩

/-- **The frontier of a complementary component of a Jordan curve is the whole curve**, provided
the curve separates the plane: if `C` separates `x` from `y`, the component of `Cᶜ` containing
`x` has frontier `C`. -/
theorem IsJordanCurve.frontier_connectedComponentIn {C : Set ℂ} (h : IsJordanCurve C) {x y : ℂ}
    (hx : x ∉ C) (hy : y ∉ C) (hxy : y ∉ connectedComponentIn Cᶜ x) :
    frontier (connectedComponentIn Cᶜ x) = C := by
  have hEo : IsOpen (connectedComponentIn Cᶜ x) :=
    h.isClosed.isOpen_compl.connectedComponentIn
  refine subset_antisymm (fun w hw => ?_) fun q hq =>
    ⟨h.subset_closure_connectedComponentIn hx hy hxy hq, ?_⟩
  · simpa using frontier_connectedComponentIn_subset_compl h.isClosed.isOpen_compl x hw
  · rw [hEo.interior_eq]
    exact fun hqE => connectedComponentIn_subset _ _ hqE hq

/-- **An open set in the filled hull of a Jordan curve misses the curve.** If `U` is open and
contained in `filledHull C` for a Jordan curve `C ⊆ ℂ`, then `U` does not meet `C`. -/
theorem IsJordanCurve.disjoint_of_isOpen_of_subset_filledHull {C U : Set ℂ} (h : IsJordanCurve C)
    (hU : IsOpen U) (hUC : U ⊆ filledHull C) : Disjoint U C := by
  refine disjoint_left.mpr fun z hzU hzC => ?_
  -- `C` has empty interior, so `U` has a point `w` off `C`, in a bounded component
  obtain ⟨w, hwU, hwC⟩ : ∃ w ∈ U, w ∉ C := by
    by_contra! hcon
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    have := interior_maximal hcon hU
    rw [h.interior_eq_empty hrank] at this
    exact this hzU
  -- a point outside the bounded filled hull lies in an unbounded component, other than `w`'s
  obtain ⟨x, hx⟩ : ∃ x, x ∉ filledHull C := by
    by_contra! hcon
    exact NormedSpace.unbounded_univ ℝ ℂ
      ((isBounded_filledHull.mpr h.isCompact.isBounded).subset fun z _ => hcon z)
  have hxw : w ∉ connectedComponentIn Cᶜ x := fun hw => hx <| by
    rw [mem_filledHull_iff, connectedComponentIn_eq hw]
    exact mem_filledHull_iff.mp (hUC hwU)
  -- `z ∈ C` is adherent to the unbounded component, which `U` therefore meets
  obtain ⟨u, huU, hux⟩ := _root_.mem_closure_iff.mp
    (h.subset_closure_connectedComponentIn (fun hxC => hx (subset_filledHull hxC)) hwC hxw hzC)
    _ hU hzU
  refine hx ?_
  rw [mem_filledHull_iff, connectedComponentIn_eq hux]
  exact mem_filledHull_iff.mp (hUC huU)

end TauCeti
