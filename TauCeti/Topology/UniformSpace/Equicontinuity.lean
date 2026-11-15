/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuity from a tail and Cauchy propagation along closures

Equicontinuity at a point is insensitive to finitely many members of a family, provided each of
them is continuous there (`equicontinuousAt_finite`). For a sequence `F : ℕ → X → α` this means
that equicontinuity at `x₀` of a tail `n ↦ F (n + N)` and continuity at `x₀` of the first `N`
members give equicontinuity at `x₀` of the whole sequence
(`TauCeti.equicontinuousAt_of_equicontinuousAt_add`). Local arguments often control a sequence
only from some index on, with the index depending on the point; this lemma assembles such local
control into equicontinuity of the original sequence.

Equicontinuity within a neighbourhood of `x₀` is equicontinuity at `x₀`
(`EquicontinuousWithinAt.equicontinuousAt`), as for continuity.

Finally, for a family equicontinuous at `x`, if `(F · y)` is Cauchy along a filter `l` on a set
whose closure contains `x`, then `(F · x)` is also Cauchy along `l`
(`EquicontinuousAt.cauchy_map_of_mem_closure`), so `{x | Cauchy (l.map (F · x))}` is closed for an
equicontinuous family (`Equicontinuous.isClosed_setOfPred_cauchy_map`). These are the limit-free
Cauchy counterparts of Mathlib's `EquicontinuousAt.tendsto_of_mem_closure` and
`Equicontinuous.isClosed_setOfPred_tendsto`, requiring neither a candidate limit map nor
completeness of `α`.
-/

public section

open Filter Topology
open scoped Uniformity SetRel

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α]

/-- A family equicontinuous at `x₀` within a neighbourhood of `x₀` is equicontinuous at `x₀`. -/
theorem EquicontinuousWithinAt.equicontinuousAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (hF : EquicontinuousWithinAt F S x₀) (hS : S ∈ 𝓝 x₀) : EquicontinuousAt F x₀ := by
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.2 hS] at hF

/-- If `F : ι → X → α` is equicontinuous at `x`, `(F · y)` is Cauchy along `l` for every `y ∈ s`,
and `x ∈ closure s`, then `(F · x)` is Cauchy along `l`.

This is the Cauchy counterpart of `EquicontinuousAt.tendsto_of_mem_closure`, requiring no
candidate limit function on `s`. -/
theorem EquicontinuousAt.cauchy_map_of_mem_closure {l : Filter ι} {F : ι → X → α}
    {s : Set X} {x : X} (hF : EquicontinuousAt F x)
    (hs : ∀ y ∈ s, Cauchy (l.map (F · y))) (hx : x ∈ closure s) :
    Cauchy (l.map (F · x)) := by
  rw [cauchy_map_iff]
  refine ⟨?_, tendsto_def.mpr fun U hU ↦ ?_⟩
  · obtain ⟨y, -, hys⟩ := mem_closure_iff_nhds.mp hx Set.univ univ_mem
    exact (cauchy_map_iff.mp (hs y hys)).1
  · rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
    obtain ⟨y, hFy, hys⟩ := mem_closure_iff_nhds.mp hx _ (hF V hV)
    filter_upwards [tendsto_def.mp (cauchy_map_iff.mp (hs y hys)).2 V hV] with p hp
    exact hVU ⟨_, ⟨_, hFy p.1, hp⟩, SetRel.symm V (hFy p.2)⟩

/-- If `F : ι → X → α` is an equicontinuous family of functions and `l` is a filter on `ι`,
then `{x | Cauchy (l.map (F · x))}` is a closed set.

This is the Cauchy counterpart of `Equicontinuous.isClosed_setOfPred_tendsto`. -/
theorem Equicontinuous.isClosed_setOfPred_cauchy_map {l : Filter ι} {F : ι → X → α}
    (hF : Equicontinuous F) : IsClosed {x | Cauchy (l.map (F · x))} :=
  closure_subset_iff_isClosed.mp fun x hx ↦
    (hF x).cauchy_map_of_mem_closure (fun _ ↦ id) hx

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
