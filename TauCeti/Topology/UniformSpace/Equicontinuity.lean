/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Local, tail, and dense-Cauchy criteria for equicontinuous families

Equicontinuity within a neighbourhood of `x₀` is equicontinuity at `x₀`
(`EquicontinuousWithinAt.equicontinuousAt`), as for continuity. Equicontinuity at a point is also
insensitive to finitely many members of a family, provided each of them is continuous there
(`equicontinuousAt_finite`): for a sequence `F : ℕ → X → α`, equicontinuity at `x₀` of a tail
`n ↦ F (n + N)` and continuity at `x₀` of the first `N` members give equicontinuity at `x₀` of the
whole sequence (`TauCeti.equicontinuousAt_of_equicontinuousAt_add`).

Mathlib's `Equicontinuous.isClosed_setOfPred_tendsto` extends pointwise convergence of an
equicontinuous family `F : ι → X → α` from a dense set once a continuous limit function `f : X → α`
is already in hand. Before constructing `f`, one often knows only that `F · y` is Cauchy along a
filter `l` on `ι` for points `y` of a dense subset `s ⊆ X`. If `F` is equicontinuous at `x` and
`l.map (F · y)` is Cauchy for every `y ∈ s`, then `l.map (F · x)` is Cauchy whenever
`x ∈ closure s`. Hence for an equicontinuous family `F`, the locus `{x | Cauchy (l.map (F · x))}`
is closed, and when the target uniform space `α` is complete and `s` is dense in `X`, `F` converges
pointwise on all of `X` to a continuous limit function.

## Main results

* `EquicontinuousWithinAt.equicontinuousAt`: equicontinuity within a neighbourhood of `x₀` implies
  equicontinuity at `x₀`.
* `TauCeti.equicontinuousAt_of_equicontinuousAt_add`: equicontinuity at `x₀` of a sequence from
  equicontinuity of a shifted tail and continuity of the initial segment.
* `EquicontinuousAt.cauchy_map_of_mem_closure`: pointwise Cauchyness along a filter propagates to
  closure points at which the family is equicontinuous.
* `Equicontinuous.isClosed_setOfPred_cauchy_map`: the set of points along which an equicontinuous
  family is Cauchy is closed.
* `Equicontinuous.exists_continuous_tendsto_of_dense`: an equicontinuous family into a complete
  uniform space that is pointwise Cauchy on a dense subset converges pointwise everywhere to a
  continuous function.
-/

public section

open Filter Set Topology Uniformity

variable {ι X α : Type*} [TopologicalSpace X] [UniformSpace α]

/-- A family equicontinuous at `x₀` within a neighbourhood of `x₀` is equicontinuous at `x₀`. -/
theorem EquicontinuousWithinAt.equicontinuousAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (hF : EquicontinuousWithinAt F S x₀) (hS : S ∈ 𝓝 x₀) : EquicontinuousAt F x₀ := by
  rwa [EquicontinuousWithinAt, nhdsWithin_eq_nhds.2 hS] at hF

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

/-- If `F : ι → X → α` is equicontinuous at `x`, `l.map (F · y)` is Cauchy for every `y ∈ s`, and
`x ∈ closure s`, then `l.map (F · x)` is Cauchy. -/
theorem EquicontinuousAt.cauchy_map_of_mem_closure {l : Filter ι} {F : ι → X → α}
    {s : Set X} {x : X} (hF : EquicontinuousAt F x)
    (hs : ∀ y ∈ s, Cauchy (l.map (F · y))) (hx : x ∈ closure s) :
    Cauchy (l.map (F · x)) := by
  have hx' : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  obtain ⟨y₀, hy₀⟩ := (eventually_mem_nhdsWithin (s := s) (a := x)).exists
  have hl : l.NeBot := (hs y₀ hy₀).1.of_map
  refine cauchy_map_iff.mpr ⟨hl, tendsto_def.mpr fun U hU ↦ ?_⟩
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, _, hVU⟩
  have hnear : ∀ᶠ y in 𝓝[s] x, y ∈ s ∧ ∀ i, (F i x, F i y) ∈ V :=
    eventually_mem_nhdsWithin.and ((hF V hV).filter_mono nhdsWithin_le_nhds)
  rcases hnear.exists with ⟨y, hys, hFy⟩
  filter_upwards [tendsto_def.mp (cauchy_map_iff.mp (hs y hys)).2 V hV] with p hp
  exact hVU ⟨F p.2 y, ⟨F p.1 y, hFy p.1, hp⟩, SetRel.symm V (hFy p.2)⟩

/-- For an equicontinuous family `F : ι → X → α` and any filter `l` on `ι`, the set of points `x`
such that `l.map (F · x)` is Cauchy is closed in `X`. -/
theorem Equicontinuous.isClosed_setOfPred_cauchy_map {l : Filter ι} {F : ι → X → α}
    (hF : Equicontinuous F) :
    IsClosed {x : X | Cauchy (l.map (F · x))} :=
  closure_subset_iff_isClosed.mp fun x hx ↦
    (hF x).cauchy_map_of_mem_closure (fun _ ↦ id) hx

/-- If an equicontinuous family `F : ι → X → α` into a complete uniform space `α` is pointwise
Cauchy along a nontrivial filter `l` on a dense subset `s ⊆ X`, then `F` converges pointwise on all
of `X` to a continuous function `f : X → α`. -/
theorem Equicontinuous.exists_continuous_tendsto_of_dense [CompleteSpace α]
    {l : Filter ι} [l.NeBot] {F : ι → X → α} {s : Set X}
    (hF : Equicontinuous F) (hs : Dense s) (hc : ∀ y ∈ s, Cauchy (l.map (F · y))) :
    ∃ f : X → α, Continuous f ∧ ∀ x, Tendsto (F · x) l (𝓝 (f x)) := by
  have hc_all (x : X) : Cauchy (l.map (F · x)) :=
    hF.isClosed_setOfPred_cauchy_map.closure_subset_iff.mpr hc (hs x)
  choose f hf using fun x ↦ cauchy_map_iff_exists_tendsto.mp (hc_all x)
  exact ⟨f, (tendsto_pi_nhds.mpr hf).continuous_of_equicontinuous hF, hf⟩
