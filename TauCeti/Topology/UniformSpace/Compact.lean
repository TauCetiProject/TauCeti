/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Finite subfamilies of separating maps on compact uniform spaces

If continuous maps `f i : X → Y` from a compact uniform space separate points through a closed
set `V` (`∀ i, (f i x, f i y) ∈ V` implies `x = y`), then for every entourage `W` there is a
finite set `F` of indices such that `∀ i ∈ F, (f i x, f i y) ∈ V` already implies `(x, y) ∈ W`
(`TauCeti.exists_finset_forall_mem_of_isClosed`). The closed sets
`{(x, y) | (f i x, f i y) ∈ V}` meet the compact complement of the interior of `W` in the empty
set, so finitely many of them already do.
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
