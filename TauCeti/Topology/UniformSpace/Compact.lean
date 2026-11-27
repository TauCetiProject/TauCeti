/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Compact

/-!
# Compact sets in uniform spaces: separating maps and near retractions

## Finite subfamilies of separating maps

If continuous maps `f i : X → Y` from a compact uniform space separate points through a closed
set `V` (`∀ i, (f i x, f i y) ∈ V` implies `x = y`), then for every entourage `W` there is a
finite set `F` of indices such that `∀ i ∈ F, (f i x, f i y) ∈ V` already implies `(x, y) ∈ W`
(`TauCeti.exists_finset_forall_mem_of_isClosed`). The closed sets
`{(x, y) | (f i x, f i y) ∈ V}` meet the compact complement of the interior of `W` in the empty
set, so finitely many of them already do.

## Near retractions onto compact sets

Let `S` be a compact subset of a uniform space `X`, and assign to every point `s ∈ S` a
neighbourhood `G s`. There are a neighbourhood `U` of `S` and a map `r : X → X` sending `U` into
`S`, not necessarily continuous, which is close to the identity relative to the sets `G s`: every
point of `U` has a neighbourhood `V` such that `V` and the image under `r` of `V ∩ U` lie in a
single set `G s` (`IsCompact.exists_mem_nhdsSet_mapsTo_forall_exists_nhds`). Such maps compare
cochains on a neighbourhood of `S` with cochains on `S` itself, for instance in the continuity of
Alexander–Spanier cohomology for compact subsets.
-/

public section

namespace TauCeti

open Set
open scoped Uniformity

variable {X : Type*} [UniformSpace X] [CompactSpace X]

/-- **Finite windows.** On a compact uniform space, if continuous maps `f i` into a topological
space `Y` separate points through a closed set `V`, then for every entourage `W` a finite set `F`
of indices suffices: `(f i x, f i y) ∈ V` for every `i ∈ F` implies `(x, y) ∈ W`. -/
theorem exists_finset_forall_mem_of_isClosed {ι Y : Type*} [TopologicalSpace Y] {f : ι → X → Y}
    (hf : ∀ i, Continuous (f i)) {V : Set (Y × Y)} (hV : IsClosed V)
    (hsep : ∀ x y, (∀ i, (f i x, f i y) ∈ V) → x = y) {W : Set (X × X)} (hW : W ∈ 𝓤 X) :
    ∃ F : Finset ι, ∀ x y, (∀ i ∈ F, (f i x, f i y) ∈ V) → (x, y) ∈ W := by
  have hK : IsCompact (interior W)ᶜ := isOpen_interior.isClosed_compl.isCompact
  have hclosed (i : ι) : IsClosed {p : X × X | (f i p.1, f i p.2) ∈ V} :=
    hV.preimage (((hf i).comp continuous_fst).prodMk ((hf i).comp continuous_snd))
  obtain ⟨F, hF⟩ := hK.elim_finite_subfamily_closed _ hclosed <| by
    refine Set.disjoint_left.2 fun p hp hmem ↦ hp ?_
    obtain ⟨x, y⟩ := p
    obtain rfl : x = y := hsep x y fun i ↦ Set.mem_iInter.1 hmem i
    exact refl_mem_uniformity (interior_mem_uniformity hW)
  refine ⟨F, fun x y hxy ↦ interior_subset (by_contra fun hp ↦ ?_)⟩
  exact Set.disjoint_left.1 hF hp (Set.mem_iInter₂.2 fun i hi ↦ hxy i hi)

end TauCeti

open Topology

/-- **Near retractions onto a compact set.** Let `S` be a compact subset of a uniform space and
assign to every `s ∈ S` a neighbourhood `G s` of `s`. There are a neighbourhood `U` of `S` and a
map `r : X → X` sending `U` into `S` such that every point of `U` has a neighbourhood `V` for which
`V` and `r '' (V ∩ U)` lie in a single set `G s`.

The map `r` sends each point of `U` to a point of `S` that is close to it; it is not continuous in
general. -/
theorem IsCompact.exists_mem_nhdsSet_mapsTo_forall_exists_nhds {X : Type*} [UniformSpace X]
    {S : Set X} (hS : IsCompact S) {G : S → Set X} (hG : ∀ s : S, G s ∈ 𝓝 (s : X)) :
    ∃ U ∈ 𝓝ˢ S, ∃ r : X → X, Set.MapsTo r U S ∧
      ∀ y ∈ U, ∃ s : S, ∃ V ∈ 𝓝 y, V ⊆ G s ∧ Set.MapsTo r (V ∩ U) (G s) := by
  classical
  -- A Lebesgue entourage `D` of the cover by the sets `G s`, and a symmetric `E` with
  -- `E ○ E ○ E ⊆ D`.
  obtain ⟨D, hD, hDG⟩ := lebesgue_number_lemma_nhds' hS (U := fun x hx ↦ G ⟨x, hx⟩)
    fun x hx ↦ hG ⟨x, hx⟩
  obtain ⟨E, hE, hEs, hEEE⟩ := comp_comp_symm_mem_uniformity_sets hD
  -- `U` is the `E`-neighbourhood of `S`, and `r` picks an `E`-close point of `S`.
  let U : Set X := {x | ∃ s ∈ S, (s, x) ∈ E}
  let r : X → X := fun x ↦ if h : ∃ s ∈ S, (s, x) ∈ E then h.choose else x
  have hr (x : X) (hx : x ∈ U) : r x ∈ S ∧ (r x, x) ∈ E := by
    simp only [U, Set.mem_ofPred_eq] at hx
    simp only [r, dite_eq_left hx]
    exact hx.choose_spec
  have hE3 {a b c d : X} (hab : (a, b) ∈ E) (hbc : (b, c) ∈ E) (hcd : (c, d) ∈ E) :
      (a, d) ∈ D :=
    hEEE ⟨c, ⟨b, hab, hbc⟩, hcd⟩
  refine ⟨U, mem_nhdsSet_iff_forall.2 fun s hs ↦ ?_, r, fun x hx ↦ (hr x hx).1, fun y hy ↦ ?_⟩
  · exact Filter.mem_of_superset (mem_nhds_left s hE) fun x hx ↦ ⟨s, hs, hx⟩
  · -- Near `y`, everything is `D`-close to the point `r y` of `S`.
    obtain ⟨hyS, hyE⟩ := hr y hy
    obtain ⟨s, hs⟩ := hDG (r y) hyS
    refine ⟨s, {x | (y, x) ∈ E}, mem_nhds_left y hE, fun x hx ↦ hs ?_, fun x hx ↦ hs ?_⟩
    · exact hE3 (refl_mem_uniformity hE) (SetRel.symm E hx) (SetRel.symm E hyE)
    · exact hE3 (hr x hx.2).2 (SetRel.symm E hx.1) (SetRel.symm E hyE)
