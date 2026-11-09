/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Coherent
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.CompactOpen

/-!
# Coherent topologies: gluing and products with a locally compact factor

The topology of `X` is coherent with a family `S` of subsets (`Topology.IsCoherentWith S`) when a
set is open as soon as it is relatively open in every member of `S`; equivalently, a map out of
`X` is continuous as soon as it is continuous on every member of `S`. A CW complex carries the
final topology of its skeleta, and the union of a tower of spaces is given the final topology of
its stages.

Functions on the members of such a family glue: if they are continuous and agree on overlaps, the
function they define by Mathlib's `Set.liftCover` is continuous
(`Topology.IsCoherentWith.continuous_liftCover`).

If `S` covers `X` and `Z` is locally compact, then the topology of `Z × X` is coherent with the
family of products `univ ×ˢ s`, `s ∈ S` (`Topology.IsCoherentWith.univ_prod`). So a homotopy
`I × X → Y`, with `I` the unit interval, is continuous as soon as it is continuous on each
`I × s`; this is how homotopies built stage by stage on a tower are glued. The proof is the
classical one: by the exponential law, a map `Z × X → Y` is continuous when its curried form
`X → C(Z, Y)` is, and continuity of the curried form can be checked on the members of `S`. This
is the argument of Mathlib's `Topology.IsQuotientMap.continuous_lift_prod_left`, for quotient maps.
Without the covering hypothesis the statement fails: the points of `X` outside every member of `S`
form a discrete open set, and `Z × {x}` need not be.
-/

public section

open Set

namespace Topology.IsCoherentWith

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {S : Set (Set X)}

/-- **Gluing along a coherent family.** If the topology of `X` is coherent with a covering family
of subsets, then continuous functions on its members which agree on overlaps glue by
`Set.liftCover` to a continuous function on `X`. -/
theorem continuous_liftCover {ι : Type*} {K : ι → Set X} (hK : IsCoherentWith (range K))
    {f : ∀ i, K i → Z} (hfc : ∀ i, Continuous (f i))
    (hf : ∀ i j (x : X) (hxi : x ∈ K i) (hxj : x ∈ K j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hKX : ⋃ i, K i = univ) : Continuous (liftCover K f hf hKX) := by
  refine hK.continuous_iff.2 ?_
  rintro _ ⟨i, rfl⟩
  exact continuousOn_iff_continuous_domRestrict.2 <| (hfc i).congr fun _ ↦ liftCover_coe _ |>.symm

/-- **Products with a locally compact space preserve coherence.** If the topology of `X` is
coherent with a family `S` of subsets covering `X`, and `Z` is locally compact, then the topology
of `Z × X` is coherent with the family of products `univ ×ˢ s` for `s ∈ S`. -/
theorem univ_prod [LocallyCompactSpace Z] (hS : IsCoherentWith S) (hSX : ⋃₀ S = univ) :
    IsCoherentWith ((univ ×ˢ ·) '' S : Set (Set (Z × X))) := by
  refine of_continuous_prop fun f hf ↦ ?_
  have hfS : ∀ s ∈ S, ContinuousOn f (univ ×ˢ s) := fun s hs ↦ hf _ ⟨s, hs, rfl⟩
  have hfx : ∀ x, Continuous fun z ↦ f (z, x) := fun x ↦ by
    obtain ⟨s, hs, hxs⟩ := mem_sUnion.1 (hSX.symm ▸ mem_univ x : x ∈ ⋃₀ S)
    exact (hfS s hs).comp_continuous (by fun_prop) fun z ↦ ⟨mem_univ z, hxs⟩
  let G : X → C(Z, Prop) := fun x ↦ ⟨_, hfx x⟩
  have hG : Continuous G := by
    refine hS.continuous_iff.2 fun s hs ↦ continuousOn_iff_continuous_domRestrict.2 ?_
    have hfs : Continuous fun p : s × Z ↦ f (p.2, p.1) :=
      (hfS s hs).comp_continuous (by fun_prop) fun p ↦ ⟨mem_univ _, p.1.2⟩
    exact (ContinuousMap.curry ⟨_, hfs⟩).continuous
  exact (ContinuousMap.continuous_uncurry_of_continuous ⟨G, hG⟩).comp continuous_swap

end Topology.IsCoherentWith
