/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuity of a tail and Cauchy loci of equicontinuous families

Equicontinuity at a point is insensitive to finitely many members of a family, provided each of
them is continuous there (`equicontinuousAt_finite`). For a sequence `F : ℕ → X → α` this means
that equicontinuity at `x₀` of a tail `n ↦ F (n + N)` and continuity at `x₀` of the first `N`
members give equicontinuity at `x₀` of the whole sequence
(`TauCeti.equicontinuousAt_of_equicontinuousAt_add`). Local arguments often control a sequence
only from some index on, with the index depending on the point; this lemma assembles such local
control into equicontinuity of the original sequence.

Equicontinuity within a neighbourhood of `x₀` is equicontinuity at `x₀`
(`EquicontinuousWithinAt.equicontinuousAt`), as for continuity.

For an equicontinuous family `F : ι → X → α` into a uniform space, pointwise Cauchyness along any
filter `l` on `ι` propagates from a set `s` to its closure
(`EquicontinuousAt.cauchy_map_of_mem_closure`), so `{x | Cauchy (map (F · x) l)}` and
`{x | CauchySeq (F · x)}` are closed subsets of `X` without any separation or completeness
assumption on `α` (`Equicontinuous.isClosed_setOfPred_cauchy_map`,
`Equicontinuous.isClosed_setOfPred_cauchySeq`), parallel to Mathlib's
`EquicontinuousAt.tendsto_of_mem_closure` and `Equicontinuous.isClosed_setOfPred_tendsto`.
-/

public section

open Filter Topology Uniformity

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α]

/-- A family equicontinuous at `x₀` within a neighbourhood of `x₀` is equicontinuous at `x₀`. -/
theorem EquicontinuousWithinAt.equicontinuousAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (hF : EquicontinuousWithinAt F S x₀) (hS : S ∈ 𝓝 x₀) : EquicontinuousAt F x₀ := by
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.2 hS] at hF

/-- If `F : ι → X → α` is equicontinuous at `x ∈ closure s` and `i ↦ F i y` is Cauchy along `l`
for every `y ∈ s`, then `i ↦ F i x` is Cauchy along `l`. -/
theorem EquicontinuousAt.cauchy_map_of_mem_closure {l : Filter ι} {F : ι → X → α}
    {s : Set X} {x : X} (hF : EquicontinuousAt F x)
    (hs : ∀ y ∈ s, Cauchy (map (F · y) l)) (hx : x ∈ closure s) :
    Cauchy (map (F · x) l) := by
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  obtain ⟨y₀, hy₀⟩ := (eventually_mem_nhdsWithin (s := s) (a := x)).exists
  have hl : l.NeBot := (cauchy_map_iff.mp (hs y₀ hy₀)).1
  rw [cauchy_map_iff]
  refine ⟨hl, ((𝓤 α).basis_sets.tendsto_right_iff).mpr fun U hU ↦ ?_⟩
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
  have hex : ∀ᶠ y in 𝓝[s] x, y ∈ s ∧ ∀ i, (F i x, F i y) ∈ V :=
    eventually_mem_nhdsWithin.and ((hF V hV).filter_mono nhdsWithin_le_nhds)
  obtain ⟨y, hys, hFy⟩ := hex.exists
  filter_upwards [(cauchy_map_iff.mp (hs y hys)).2 hV] with p hp
  exact hVU ⟨F p.2 y, ⟨F p.1 y, hFy p.1, hp⟩, SetRel.symm V (hFy p.2)⟩

/-- For an equicontinuous family `F : ι → X → α` and any filter `l` on `ι`, the set of points `x`
where `i ↦ F i x` is Cauchy along `l` is closed. -/
theorem Equicontinuous.isClosed_setOfPred_cauchy_map {l : Filter ι} {F : ι → X → α}
    (hF : Equicontinuous F) :
    IsClosed {x : X | Cauchy (map (F · x) l)} :=
  closure_subset_iff_isClosed.mp fun x hx ↦ (hF x).cauchy_map_of_mem_closure (fun _ ↦ id) hx

/-- For an equicontinuous family `F : ι → X → α` indexed by a preorder, the set of points `x`
where `i ↦ F i x` is a Cauchy net is closed. -/
theorem Equicontinuous.isClosed_setOfPred_cauchySeq [Preorder ι] {F : ι → X → α}
    (hF : Equicontinuous F) :
    IsClosed {x : X | CauchySeq (F · x)} :=
  hF.isClosed_setOfPred_cauchy_map

namespace TauCeti

/-- A sequence of functions is equicontinuous at `x₀` if one of its tails `n ↦ F (n + N)` is,
and its first `N` members are continuous at `x₀`. -/
theorem equicontinuousAt_of_equicontinuousAt_add {F : ℕ → X → α} {x₀ : X} (N : ℕ)
    (hF : EquicontinuousAt (fun n ↦ F (n + N)) x₀) (hc : ∀ n < N, ContinuousAt (F n) x₀) :
    EquicontinuousAt F x₀ := by
  intro U hU
  have hfin : EquicontinuousAt (fun n : Fin N ↦ F n) x₀ :=
    equicontinuousAt_finite.2 fun n ↦ hc n n.isLt
  filter_upwards [hF U hU, hfin U hU] with x htail hhead n
  rcases lt_or_ge n N with hn | hn
  · exact hhead ⟨n, hn⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact htail k

end TauCeti
