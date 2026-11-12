/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Nested intersections of continua

A **continuum** is a nonempty compact connected set. This file proves the standard structural
theorem about them: the intersection of a family of compact connected sets that is *downward
directed* — any two members contain a third — is again compact and connected. Mathlib has the union
counterpart, `IsPreconnected.sUnion_directed`, and Cantor's intersection theorem
`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`, but not the preservation of
connectedness under a directed intersection; this file supplies it.

Boundary cluster sets, ω-limit sets and prime-end impressions are such intersections under
suitable hypotheses — a continuous map or curve with values in a compact set, approached through
connected regions or along a half-line, or a null chain in a bounded domain — and are then
preconnected or continua: see `TauCeti.isConnected_clusterSetOn`,
`TauCeti.isPreconnected_setOf_mapClusterPt_atTop` and
`TauCeti.IsNullChain.isConnected_nullChainImpression`. Without such hypotheses these sets need not
be connected, or even nonempty.

Both hypotheses on the family are essential. Without directedness a circle and a secant line are
two continua meeting in two points, a disconnected intersection. Without compactness the theorem
fails even for a *decreasing sequence*: in `ℝ × ℝ` the closed connected sets
`(ℝ ×ˢ {0}) ∪ (ℝ ×ˢ {1}) ∪ (Ici n ×ˢ Icc 0 1)` — two parallel lines bridged by a strip that
recedes to infinity — intersect in the two lines, which are disconnected.

## The argument

The intersection `C` is compact, hence closed, so it suffices to show that whenever `C` is
covered by two disjoint closed sets `u` and `v`, it lies in one of them. The pieces `C ∩ u` and
`C ∩ v` are disjoint compact sets, so in a Hausdorff space they have disjoint open neighbourhoods
`U` and `V`, and `C ⊆ U ∪ V`. So `U ∪ V` is a neighbourhood of `C`, and
`exists_subset_nhds_of_isCompact` — any neighbourhood of the intersection of a directed family of
compacts already contains one member — supplies a single `t i ⊆ U ∪ V`. Being preconnected, `t i`
lies in `U` or in `V`, and so does `C`; then `C` misses `v` or `u` respectively.

## Main results

* `TauCeti.isPreconnected_iInter_of_directed` — a directed intersection of compact preconnected
  sets is preconnected.
* `TauCeti.isConnected_iInter_of_directed` — the continuum form: a directed intersection of
  continua is a continuum.

## References

* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* K. Kuratowski, *Topology II*, §47.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {t : ι → Set X}

/-- **A directed intersection of compact preconnected sets is preconnected.** The family `t` is
indexed by a nonempty type and directed downwards: any two members contain a third.

Both hypotheses on the family are needed; see the module docstring for the two counterexamples. -/
theorem isPreconnected_iInter_of_directed [T2Space X] [Nonempty ι] (htd : Directed (· ⊇ ·) t)
    (htc : ∀ i, IsCompact (t i)) (htp : ∀ i, IsPreconnected (t i)) :
    IsPreconnected (⋂ i, t i) := by
  have hCcl : IsClosed (⋂ i, t i) := isClosed_iInter fun i => (htc i).isClosed
  have hCco : IsCompact (⋂ i, t i) :=
    (htc (Classical.arbitrary ι)).of_isClosed_subset hCcl (iInter_subset _ _)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hCcl]
  intro u v hu hv hCuv huv
  -- Separate the two compact halves `C ∩ u` and `C ∩ v` by disjoint open sets `U` and `V`.
  obtain ⟨U, V, hU, hV, hCU, hCV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hCco.inter_right hu) (hCco.inter_right hv)
      (huv.mono inter_subset_right inter_subset_right)
  have hCUV : (⋂ i, t i) ⊆ U ∪ V := fun x hx =>
    (hCuv hx).imp (fun hxu => hCU ⟨hx, hxu⟩) fun hxv => hCV ⟨hx, hxv⟩
  -- One member `t i` is already covered by `U ∪ V`; being preconnected, it lies in `U` or in `V`,
  -- and then so does the intersection, which therefore misses `v` or `u` respectively.
  obtain ⟨i, hi⟩ :=
    exists_subset_nhds_of_isCompact htd htc ((hU.union hV).mem_nhdsSet.mpr hCUV)
  rcases (htp i).subset_or_subset hU hV hUV hi with h | h
  · exact .inl fun x hx => (hCuv hx).resolve_right fun hxv =>
      disjoint_left.mp hUV (h (iInter_subset t i hx)) (hCV ⟨hx, hxv⟩)
  · exact .inr fun x hx => (hCuv hx).resolve_left fun hxu =>
      disjoint_left.mp hUV (hCU ⟨hx, hxu⟩) (h (iInter_subset t i hx))

/-- **A directed intersection of continua is a continuum.** The family `t` of nonempty compact
preconnected sets is indexed by a nonempty type and directed downwards. -/
theorem isConnected_iInter_of_directed [T2Space X] [Nonempty ι] (htd : Directed (· ⊇ ·) t)
    (htn : ∀ i, (t i).Nonempty) (htc : ∀ i, IsCompact (t i)) (htp : ∀ i, IsPreconnected (t i)) :
    IsConnected (⋂ i, t i) :=
  ⟨IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc
      fun i => (htc i).isClosed,
    isPreconnected_iInter_of_directed htd htc htp⟩

end TauCeti
