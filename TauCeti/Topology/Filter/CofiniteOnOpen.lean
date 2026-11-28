/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.DenseEmbedding

/-!
# The cofinite-on-open filter for indexed topological data

Given a type `α` equipped with an index map `place : α → ι` and a topological coordinate
`point : α → X`, a set `S : Set α` belongs to `TauCeti.cofiniteOnOpen place point` if every
nonempty open set `V ⊆ X` contains a nonempty open subset `O ⊆ V` such that, for all but finitely
many indices `w : ι`, every `a : α` with `place a = w` and `point a ∈ O` lies in `S`.

This abstracts the filter of "most Frobenii" (`New.mostFrobenii`) on Frobenius data `(w, A, s)`
with `place = w` and `point = s ∈ Gal(Ω/E)`.

## Main definitions and results

* `TauCeti.cofiniteOnOpen`: the filter of sets containing all data above cofinitely many indices
  on a nonempty open subset of every nonempty open set.
* `TauCeti.cofiniteOnOpenAt`: the meet of `cofiniteOnOpen` with `Filter.comap point (nhds g)`.
* `TauCeti.tendsto_place_cofiniteOnOpen`: `place` tends to `Filter.cofinite` along
  `cofiniteOnOpen`.
* `TauCeti.tendsto_point_cofiniteOnOpenAt`: for continuous `f : X → Z`, `f ∘ point` tends to `f g`
  along `cofiniteOnOpenAt place point g`.
* `TauCeti.eventually_cofiniteOnOpen_of_isOpenEmbedding`: pullback along an open embedding
  `φ : X → Y` and an index map `π : ι → ι'`.
* `TauCeti.dense_of_cofiniteOnOpen`: if every nonempty open `O ⊆ X` is hit above infinitely many
  indices, then any property holding eventually along `cofiniteOnOpen` holds on a dense set.

## References

* Provenance: adapted from `New.mostFrobenii`, `New.mostFrobeniiAt`, `New.tendsto_mostFrobeniiAt`,
  `New.tendsto_place_mostFrobenii`, `New.eventually_mostFrobenii_of_isOpenEmbedding`, and
  `New.dense_of_mostFrobenii` in `grh/src/Lib/GaloisRep/Main/Defs.lean` of `grh-lean`
  (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

@[expose] public section

namespace TauCeti

open Filter Topology

variable {α ι X : Type*} [TopologicalSpace X]

/-- The filter on `α` of sets `S` such that every nonempty open `V ⊆ X` contains a nonempty open
`O ⊆ V` with `∀ᶠ w in cofinite, ∀ a, place a = w → point a ∈ O → a ∈ S`. -/
def cofiniteOnOpen (place : α → ι) (point : α → X) : Filter α where
  sets :=
    {S : Set α |
      ∀ V : Set X, IsOpen V → V.Nonempty →
        ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧
          ∀ᶠ w : ι in cofinite, ∀ a : α, place a = w → point a ∈ O → a ∈ S}
  univ_sets V hV hV_ne := ⟨V, subset_rfl, hV, hV_ne, by simp⟩
  sets_of_superset hS hST V hV hV_ne := by
    obtain ⟨O, hOV, hO, hO_ne, h_ev⟩ := hS V hV hV_ne
    exact ⟨O, hOV, hO, hO_ne, h_ev.mono fun w hw a ha haO ↦ hST (hw a ha haO)⟩
  inter_sets hS hT V hV hV_ne := by
    obtain ⟨O, hOV, hO, hO_ne, hS_ev⟩ := hS V hV hV_ne
    obtain ⟨O', hO'O, hO', hO'_ne, hT_ev⟩ := hT O hO hO_ne
    refine ⟨O', hO'O.trans hOV, hO', hO'_ne, ?_⟩
    filter_upwards [hS_ev, hT_ev] with w hwS hwT a ha haO'
    exact ⟨hwS a ha (hO'O haO'), hwT a ha haO'⟩

/-- The filter `cofiniteOnOpen place point` refined by `point` tending to `g`. -/
abbrev cofiniteOnOpenAt (place : α → ι) (point : α → X) (g : X) : Filter α :=
  cofiniteOnOpen place point ⊓ comap point (𝓝 g)

/-- Along `cofiniteOnOpen place point`, the index `place` tends to `cofinite`. -/
theorem tendsto_place_cofiniteOnOpen (place : α → ι) (point : α → X) :
    Tendsto place (cofiniteOnOpen place point) cofinite := by
  intro S hS V hV hV_ne
  refine ⟨V, subset_rfl, hV, hV_ne, ?_⟩
  filter_upwards [hS] with w hw a ha _ using show place a ∈ S by rwa [ha]

/-- For a continuous map `f : X → Z`, `f ∘ point` tends to `f g` along
`cofiniteOnOpenAt place point g`. -/
theorem tendsto_point_cofiniteOnOpenAt {Z : Type*} [TopologicalSpace Z]
    (place : α → ι) (point : α → X) {g : X} {f : X → Z} (hf : Continuous f) :
    Tendsto (fun a : α ↦ f (point a)) (cofiniteOnOpenAt place point g) (𝓝 (f g)) :=
  (hf.tendsto g).comp (tendsto_comap.mono_left inf_le_right)

/-- Pullback of `cofiniteOnOpen` along an open embedding `φ : X → Y` and an index map
`π : ι → ι'`. -/
theorem eventually_cofiniteOnOpen_of_isOpenEmbedding {β ι' Y : Type*} [TopologicalSpace Y]
    {place : α → ι} {point : α → X} {place' : β → ι'} {point' : β → Y}
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (π : ι → ι') {S : Set α}
    (hS : S ∈ cofiniteOnOpen place point) :
    ∀ᶠ b : β in cofiniteOnOpen place' point',
      ∀ a : α, π (place a) = place' b → φ (point a) = point' b → a ∈ S := by
  intro V hV hV_ne
  by_cases h_meet : (φ ⁻¹' V).Nonempty
  · obtain ⟨O, hO_sub, hO_open, hO_ne, h_cof⟩ := hS (φ ⁻¹' V) (hV.preimage hφ.continuous) h_meet
    refine ⟨φ '' O, Set.image_subset_iff.mpr hO_sub, hφ.isOpenMap O hO_open, hO_ne.image φ, ?_⟩
    filter_upwards [(h_cof.image π).compl_mem_cofinite] with v hv b hb hbO a hπ hφa
    have h_mem : point a ∈ O := hφ.injective.mem_set_image.mp (by rwa [hφa])
    by_contra ha_not
    exact hv ⟨place a, fun h_good ↦ ha_not (h_good a rfl h_mem), hπ.trans hb⟩
  · refine ⟨V, subset_rfl, hV, hV_ne, .of_forall fun v b _ hbO a _ hφa ↦ ?_⟩
    exact absurd ⟨point a, show φ (point a) ∈ V by rwa [hφa]⟩ h_meet

/-- If every nonempty open set `O ⊆ X` is hit by `point` above cofinitely many (equivalently,
frequently along `cofinite`) indices `place a`, then any property `p (point a)` holding eventually
along `cofiniteOnOpen place point` holds on a dense subset of `X`. -/
theorem dense_of_cofiniteOnOpen {place : α → ι} {point : α → X}
    (h_hit : ∀ O : Set X, IsOpen O → O.Nonempty →
      ∃ᶠ w : ι in cofinite, ∃ a : α, place a = w ∧ point a ∈ O)
    {p : X → Prop} (hp : ∀ᶠ a : α in cofiniteOnOpen place point, p (point a)) :
    Dense {s : X | p s} := by
  refine dense_iff_inter_open.mpr fun V hV hV_ne ↦ ?_
  obtain ⟨O, hOV, hO, hO_ne, h_cof⟩ := hp V hV hV_ne
  obtain ⟨w, ⟨a, ha_place, haO⟩, hw_good⟩ := ((h_hit O hO hO_ne).and_eventually h_cof).exists
  exact ⟨point a, hOV haO, hw_good a ha_place haO⟩

end TauCeti
