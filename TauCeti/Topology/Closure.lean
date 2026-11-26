/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Basic
import TauCeti.Data.Set.Lattice

/-!
# Closures and neighbourhoods

The Seifert--van Kampen theorem takes as input two sets whose interiors cover the space. A common
choice is the complement of a set `s` together with a set `t` surrounding it. Their interiors
cover the space exactly when `closure s ⊆ interior t`. For a closed point `p`, any neighbourhood of
`p` qualifies. Likewise, an open set `U` and the complement of a closed set `K ⊆ U` have interiors
covering the space; this is the cover used by excision onto a neighbourhood.

A point `y₀` adherent to a set `B` but not in it is approached by `B` in every neighbourhood, so no
neighbourhood of `y₀` lies in a set disjoint from `B` together with `y₀` itself. In particular, a
point adherent to two disjoint sets but in neither has no neighbourhood that misses one of them
away from the point.

A set containing a punctured neighbourhood of a non-isolated point `x` has `x` in its closure.

Let a finite family of sets cover an open set `U`, each set of the family lying inside or outside
`s`, such that a member meeting the closure of another lies in that closure. Then every point of
`closure s ∩ U` lies in a member contained in the closure of a member contained in `s`. This is how
the closure of a set is described through a stratification adapted to it.

Membership in a closed set passes to limits, so pointwise limits of maps into a closed set map
into it.

In a T1 space, when the closure of a set `P` adds only finitely many points, near any point the
closure adds only that point.

## Main declarations

* `TauCeti.interior_compl_union_interior_eq_univ_iff`: the interiors of `sᶜ` and `t` cover the
  space if and only if `closure s ⊆ interior t`.
* `TauCeti.interior_compl_singleton_union_interior_eq_univ`: the interiors of the complement of a
  closed point and of a neighbourhood of that point cover the space.
* `TauCeti.interior_union_interior_compl_eq_univ`: the interiors of an open set `U` and of the
  complement of a closed set `K ⊆ U` cover the space.
* `TauCeti.not_subset_union_singleton_of_mem_closure`: an open neighbourhood of a point of
  `closure B \ B` is not contained in `A ∪ {y₀}` for any `A` disjoint from `B`.
* `TauCeti.exists_mem_subset_closure_of_mem_closure_inter`: in a finite cover of an open set `U`
  by sets inside or outside `s` satisfying the frontier condition, a point of `closure s ∩ U` lies
  in a member contained in the closure of a member contained in `s`.
* `TauCeti.mem_closure_of_mem_nhdsNE`: a set containing a punctured neighbourhood of a
  non-isolated point has that point in its closure.
* `TauCeti.mapsTo_of_tendsto_of_isClosed`: pointwise limits of maps into a closed set map into
  it.
* `TauCeti.subset_closure_range_domRestrict_preimage`: the values of a family that lie in an open
  set contained in the closure of its range are dense in that set.
* `TauCeti.subset_closure_range_subtypeVal_inter`: the points of `L` lying in an open set
  contained in the closure of `L` are dense in that set.
* `TauCeti.subset_closure_range_subtypeVal_inter_of_subset`: if the points of `L` lying in `s`
  are dense in `s`, those lying in an open subset of `s` are dense in it.
* `TauCeti.nhdsWithin_closure_le_nhdsWithin_insert`: if the closure of `P` adds finitely many
  points, then near any point `w` it contains only `w` and points of `P`.
* `Dense.mem_of_nonempty_interior_closure_singleton`: a dense set stable under generization
  contains every point whose closure has nonempty interior.
* `Dense.frequently_mem_nhdsWithin`: a dense set occurs frequently in `𝓝[t] x` for any open set
  `t` whose filter `𝓝[t] x` is nontrivial.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The interiors of `sᶜ` and `t` cover the space if and only if `t` is a neighbourhood of every
point of the closure of `s`. -/
theorem interior_compl_union_interior_eq_univ_iff {s t : Set X} :
    interior sᶜ ∪ interior t = univ ↔ closure s ⊆ interior t := by
  rw [interior_compl, ← compl_subset_iff_union, compl_compl]

/-- The complement of a closed point `p` and a neighbourhood of `p` have interiors covering the
space. -/
theorem interior_compl_singleton_union_interior_eq_univ {p : X} (hp : IsClosed ({p} : Set X))
    {B : Set X} (hB : B ∈ 𝓝 p) : interior {p}ᶜ ∪ interior B = univ :=
  interior_compl_union_interior_eq_univ_iff.2 <| by
    rwa [hp.closure_eq, singleton_subset_iff, mem_interior_iff_mem_nhds]

/-- If the open set `U` contains the closed set `K`, the interiors of `U` and `Kᶜ` cover the
space. -/
theorem interior_union_interior_compl_eq_univ {U K : Set X} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) : interior U ∪ interior Kᶜ = univ := by
  rw [union_comm, interior_compl_union_interior_eq_univ_iff, hK.closure_eq, hU.interior_eq]
  exact hKU

/-- An open set `N` around a point `y₀` of `closure B \ B` is not contained in `A ∪ {y₀}` for any
`A` disjoint from `B`: `N` meets `B` at a point other than `y₀`. -/
theorem not_subset_union_singleton_of_mem_closure {A B N : Set X} {y₀ : X} (hN : IsOpen N)
    (hy₀N : y₀ ∈ N) (hy₀ : y₀ ∈ closure B) (hAB : Disjoint A B) (hy₀B : y₀ ∉ B) :
    ¬N ⊆ A ∪ {y₀} := fun hNA ↦ by
  obtain ⟨y, hyN, hyB⟩ := mem_closure_iff.1 hy₀ N hN hy₀N
  rcases hNA hyN with hyA | rfl
  · exact disjoint_left.1 hAB hyA hyB
  · exact hy₀B hyB

/-- Let a finite family `𝒞` cover an open set `U`, each member lying inside or outside `s`, such
that a member meeting the closure of another member lies in that closure. Then every point of
`closure s ∩ U` lies in a member contained in the closure of a member contained in `s`. -/
theorem exists_mem_subset_closure_of_mem_closure_inter {s U : Set X} {𝒞 : Set (Set X)}
    (hU : IsOpen U) (h𝒞fin : 𝒞.Finite) (h𝒞cov : U ⊆ ⋃₀ 𝒞) (hs : ∀ C ∈ 𝒞, C ⊆ s ∨ Disjoint C s)
    (h𝒞front : ∀ B ∈ 𝒞, ∀ C ∈ 𝒞, (B ∩ closure C).Nonempty → B ⊆ closure C)
    {y : X} (hy : y ∈ closure s ∩ U) :
    ∃ B ∈ 𝒞, y ∈ B ∧ ∃ C ∈ 𝒞, C ⊆ s ∧ B ⊆ closure C := by
  obtain ⟨B, hB, hyB⟩ := mem_sUnion.1 (h𝒞cov hy.2)
  -- Since `U` is open, `y` lies in the closure of `s ∩ U`, inside the union of the members in `s`.
  have hyC : y ∈ closure (⋃ C ∈ {C ∈ 𝒞 | C ⊆ s}, C) := by
    rw [← sUnion_eq_biUnion, sUnion_sep_subset_eq_inter hs]
    exact closure_mono (inter_subset_inter_right s h𝒞cov) <|
      closure_mono (inter_comm U s).subset (hU.inter_closure ⟨hy.2, hy.1⟩)
  rw [(h𝒞fin.subset (sep_subset _ _)).closure_biUnion] at hyC
  obtain ⟨C, ⟨hC, hCs⟩, hyC⟩ := mem_iUnion₂.1 hyC
  exact ⟨B, hB, hyB, C, hC, hCs, h𝒞front B hB C hC ⟨y, hyB, hyC⟩⟩

/-- A set containing a punctured neighbourhood of a non-isolated point `x` has `x` in its
closure. -/
theorem mem_closure_of_mem_nhdsNE {s : Set X} {x : X} [(𝓝[≠] x).NeBot] (hs : s ∈ 𝓝[≠] x) :
    x ∈ closure s :=
  mem_closure_iff_nhdsWithin_neBot.2 (Filter.neBot_of_le (nhdsWithin_le_of_mem hs))

/-- Pointwise limits of maps into a closed set `L` map into `L`: if every `u m` maps `S` into
`L` and `u m s → v s` for every `s ∈ S`, then `v` maps `S` into `L`. -/
theorem mapsTo_of_tendsto_of_isClosed {α ι : Type*} {l : Filter ι} [l.NeBot] {L : Set X}
    (hL : IsClosed L) {S : Set α} {u : ι → α → X} {v : α → X} (hu : ∀ m, MapsTo (u m) S L)
    (hv : ∀ s ∈ S, Filter.Tendsto (fun m ↦ u m s) l (𝓝 (v s))) :
    MapsTo v S L :=
  fun s hs ↦ hL.mem_of_tendsto (hv s hs) (Filter.Eventually.of_forall fun m ↦ hu m hs)

/-- When an open set `s` lies in the closure of the values of `c`, the values of `c` lying in `s`
are dense in `s`. -/
theorem subset_closure_range_domRestrict_preimage {α : Type*} {c : α → X} {s : Set X}
    (hs : IsOpen s) (h : s ⊆ closure (range c)) :
    s ⊆ closure (range ((c ⁻¹' s).domRestrict c)) := by
  rw [range_domRestrict, image_preimage_eq_inter_range]
  exact fun x hx ↦ hs.inter_closure ⟨hx, h hx⟩

/-- When an open set `s` lies in the closure of `L`, the points of `L` lying in `s` are dense in
`s`. -/
theorem subset_closure_range_subtypeVal_inter {L s : Set X} (hs : IsOpen s)
    (h : s ⊆ closure L) : s ⊆ closure (range (Subtype.val : ↥(L ∩ s) → X)) := by
  rw [Subtype.range_coe, inter_comm]
  exact fun x hx ↦ hs.inter_closure ⟨hx, h hx⟩

/-- When the points of `L` lying in `s` are dense in `s`, the points of `L` lying in an open subset
`t` of `s` are dense in `t`. -/
theorem subset_closure_range_subtypeVal_inter_of_subset {L s t : Set X} (ht : IsOpen t)
    (hts : t ⊆ s) (h : s ⊆ closure (range (Subtype.val : ↥(L ∩ s) → X))) :
    t ⊆ closure (range (Subtype.val : ↥(L ∩ t) → X)) :=
  subset_closure_range_subtypeVal_inter ht fun _ hx ↦
    closure_mono (range_subset_iff.2 fun d ↦ d.property.1) (h (hts hx))

/-- If the closure of `P` adds only finitely many points to `P`, then near any point `w` the
closure of `P` contains only `w` and points of `P`. -/
theorem nhdsWithin_closure_le_nhdsWithin_insert [T1Space X] {P : Set X}
    (hP : (closure P \ P).Finite) (w : X) : 𝓝[closure P] w ≤ 𝓝[insert w P] w := by
  have hfar : ((closure P \ P) \ {w})ᶜ ∈ 𝓝 w := hP.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  refine nhdsWithin_le_of_mem (mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, hfar, fun x ⟨hx, hxc⟩ ↦ ?_⟩)
  by_contra hxP
  rw [mem_insert_iff, not_or] at hxP
  exact hx ⟨⟨hxc, hxP.2⟩, hxP.1⟩

end TauCeti

/-- A dense set stable under generization contains every point whose closure has nonempty
interior. -/
theorem Dense.mem_of_nonempty_interior_closure_singleton
    {X : Type*} [TopologicalSpace X] {s : Set X} (hd : Dense s)
    (hs : StableUnderGeneralization s) {x : X} (hx : (interior (closure {x})).Nonempty) :
    x ∈ s := by
  obtain ⟨y, hys, hy⟩ := hd.exists_mem_open isOpen_interior hx
  exact hs (specializes_iff_mem_closure.mpr (interior_subset hy)) hys

/-- A dense set `D` occurs frequently in `𝓝[t] x` whenever `t` is open and `𝓝[t] x` is
nontrivial. -/
theorem Dense.frequently_mem_nhdsWithin {X : Type*} [TopologicalSpace X] {D t : Set X}
    (hD : Dense D) (ht : IsOpen t) {x : X} [h : (𝓝[t] x).NeBot] :
    ∃ᶠ y in 𝓝[t] x, y ∈ D := by
  rw [Filter.frequently_mem_iff_neBot, ← nhdsWithin_inter', ← mem_closure_iff_nhdsWithin_neBot]
  exact closure_minimal (hD.open_subset_closure_inter ht) isClosed_closure
    (mem_closure_iff_nhdsWithin_neBot.mpr h)
