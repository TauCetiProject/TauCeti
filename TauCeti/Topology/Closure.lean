/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NhdsWithin

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

Membership in a closed set passes to limits, so pointwise limits of maps into a closed set map
into it.

## Main declarations

* `TauCeti.interior_compl_union_interior_eq_univ_iff`: the interiors of `sᶜ` and `t` cover the
  space if and only if `closure s ⊆ interior t`.
* `TauCeti.interior_compl_singleton_union_interior_eq_univ`: the interiors of the complement of a
  closed point and of a neighbourhood of that point cover the space.
* `TauCeti.interior_union_interior_compl_eq_univ`: the interiors of an open set `U` and of the
  complement of a closed set `K ⊆ U` cover the space.
* `TauCeti.not_subset_union_singleton_of_mem_closure`: an open neighbourhood of a point of
  `closure B \ B` is not contained in `A ∪ {y₀}` for any `A` disjoint from `B`.
* `TauCeti.mem_closure_of_mem_nhdsNE`: a set containing a punctured neighbourhood of a
  non-isolated point has that point in its closure.
* `TauCeti.mapsTo_of_tendsto_of_isClosed`: pointwise limits of maps into a closed set map into
  it.
* `TauCeti.subset_closure_range_domRestrict_preimage`: the values of a family that lie in an open
  set contained in the closure of its range are dense in that set.
* `TauCeti.mem_closure_iff_mem_closure_image_of_isInducing_domRestrict`: closure membership along
  a continuous map that is inducing on a closed subset containing the set.
* `TauCeti.closure_eq_of_isInducing_domRestrict`: transferring a closure computation along an
  injective continuous map that is inducing on a closed subset containing the set.
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

/-- If `f` is continuous, `f '' s` is closed with `f ⁻¹' (f '' s) ⊆ s`, and `s.domRestrict f` is
inducing, then closure membership for any `t ⊆ s` can be tested in the target space. -/
theorem mem_closure_iff_mem_closure_image_of_isInducing_domRestrict {Y : Type*}
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s t : Set X} (hfs : IsClosed (f '' s))
    (hpre : f ⁻¹' (f '' s) ⊆ s) (hind : IsInducing (s.domRestrict f)) (ht : t ⊆ s) {x : X} :
    x ∈ closure t ↔ f x ∈ closure (f '' t) := by
  refine ⟨fun hx ↦ mem_closure_image hf.continuousAt hx, fun hx ↦ ?_⟩
  have hxs : x ∈ s := hpre <| by
    rw [mem_preimage, ← hfs.closure_eq]
    exact closure_mono (image_mono ht) hx
  have himg : s.domRestrict f '' ((↑) ⁻¹' t : Set s) = f '' t := by
    ext y
    simp only [mem_image, mem_preimage, Subtype.exists, domRestrict_apply]
    exact ⟨fun ⟨a, _, hat, hfa⟩ ↦ ⟨a, hat, hfa⟩, fun ⟨a, hat, hfa⟩ ↦ ⟨a, ht hat, hat, hfa⟩⟩
  have hx' : (⟨x, hxs⟩ : s) ∈ closure ((↑) ⁻¹' t : Set s) := by
    rw [hind.closure_eq_preimage_closure_image, mem_preimage, domRestrict_apply, himg]
    exact hx
  exact closure_mono (image_preimage_subset _ _)
    (mem_closure_image continuous_subtypeVal.continuousAt hx')

/-- If `f` is continuous and injective, `f '' s` is closed, and `s.domRestrict f` is inducing,
then any closure identity `closure (f '' t) = f '' u` with `t ⊆ s` pulls back to
`closure t = u`. -/
theorem closure_eq_of_isInducing_domRestrict {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (hf_inj : Function.Injective f) {s t u : Set X} (hfs : IsClosed (f '' s))
    (hind : IsInducing (s.domRestrict f)) (ht : t ⊆ s) (hfu : closure (f '' t) = f '' u) :
    closure t = u := by
  ext x
  rw [mem_closure_iff_mem_closure_image_of_isInducing_domRestrict hf hfs
      (hf_inj.preimage_image s).subset hind ht,
    hfu, hf_inj.mem_set_image]

end TauCeti
