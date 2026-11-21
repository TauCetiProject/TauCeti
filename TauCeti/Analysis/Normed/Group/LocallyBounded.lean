/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import TauCeti.Topology.UniformSpace.CompactConvergence

/-!
# Local boundedness of families on compact sets

A family of maps is locally bounded on a set if its values on each compact subset admit a norm
bound uniform in the index. The definition only needs a topological domain and a norm on the
target. Local boundedness is preserved by restricting the domain or reindexing the family, and
implies a uniform bound at each point.

For seminormed group targets, total boundedness of the continuous restrictions, for the
uniformity of compact convergence (whose topology is the compact-open topology), implies local
boundedness; in particular relative compactness does. This works on an arbitrary topological
domain: on each compact subset, the values of a totally bounded family form a totally bounded,
hence bounded, set (`ContinuousMap.totallyBounded_biUnion_image`).

## Main results

* `TauCeti.IsLocallyBoundedOn`: uniform boundedness on each compact subset.
* `TauCeti.IsLocallyBoundedOn.mono` and `TauCeti.IsLocallyBoundedOn.comp`: stability under domain
  restriction and reindexing.
* `TauCeti.isLocallyBoundedOn_of_totallyBounded_range`: total boundedness, in particular
  relative compactness, of continuous restrictions gives local boundedness.
-/

public section

open Set Topology

namespace TauCeti

variable {ι E : Type*}

section LocallyBounded

variable {X : Type*} [TopologicalSpace X] [Norm E] {s t : Set X} {F : ι → X → E}

/-- A family `F : ι → X → E` of maps from a topological space into a type with a norm is
**locally bounded** on `s` if it is uniformly bounded — with a single constant, independent of
the index — on every compact subset of `s`. -/
def IsLocallyBoundedOn (F : ι → X → E) (s : Set X) : Prop :=
  ∀ K ⊆ s, IsCompact K → ∃ C, ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ C

/-- The defining compact-set characterization of local boundedness. -/
@[simp]
theorem isLocallyBoundedOn_def :
    IsLocallyBoundedOn F s ↔
      ∀ K ⊆ s, IsCompact K → ∃ C, ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ C :=
  Iff.rfl

/-- Local boundedness is inherited by subsets. -/
theorem IsLocallyBoundedOn.mono (hb : IsLocallyBoundedOn F s) (hts : t ⊆ s) :
    IsLocallyBoundedOn F t :=
  fun _K hKt hK => hb _ (hKt.trans hts) hK

/-- Local boundedness is inherited by any reindexing of the family: the bound on a compact set is
uniform in the index, so it survives being restricted to a subfamily.

In particular, passing to a subsequence preserves local boundedness. -/
theorem IsLocallyBoundedOn.comp {κ : Type*} (hb : IsLocallyBoundedOn F s)
    (σ : κ → ι) : IsLocallyBoundedOn (fun k => F (σ k)) s := by
  intro K hKs hK
  obtain ⟨C, hC⟩ := hb K hKs hK
  exact ⟨C, fun k => hC (σ k)⟩

/-- A locally bounded family is bounded at each point of the set, uniformly in the index. -/
theorem IsLocallyBoundedOn.exists_forall_norm_le (hb : IsLocallyBoundedOn F s) {z : X}
    (hz : z ∈ s) : ∃ C, ∀ i, ‖F i z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb {z} (singleton_subset_iff.2 hz) isCompact_singleton
  exact ⟨C, fun i => hC i z (mem_singleton z)⟩

/-- A family bounded by a single constant on all of `s` is locally bounded on `s`. -/
theorem isLocallyBoundedOn_of_forall_norm_le {C : ℝ}
    (h : ∀ i, ∀ z ∈ s, ‖F i z‖ ≤ C) : IsLocallyBoundedOn F s :=
  fun _K hKs _hK => ⟨C, fun i z hz => h i z (hKs hz)⟩

end LocallyBounded

section GeneralDomain

variable [SeminormedAddGroup E] {X : Type*} [TopologicalSpace X] {Ω : Set X}
  {F : ι → X → E} {f : ι → C(Ω, E)}

/-- A family of maps into a seminormed group whose continuous restrictions to `Ω` form a totally
bounded set in `C(↥Ω, E)`, for the uniformity of compact convergence, is locally bounded on `Ω`.

In particular this applies to a relatively compact family of restrictions. The domain is an
arbitrary topological space; local compactness is not required. -/
theorem isLocallyBoundedOn_of_totallyBounded_range
    (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) (htb : TotallyBounded (Set.range f)) :
    IsLocallyBoundedOn F Ω := by
  refine isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set Ω) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (ContinuousMap.totallyBounded_biUnion_image htb hK').isBounded
  refine ⟨C, fun i z hz => ?_⟩
  have hz' : (⟨z, hKΩ hz⟩ : Ω) ∈ Subtype.val ⁻¹' K := mem_preimage.2 hz
  simpa [hf i] using hC _ (mem_biUnion (mem_range_self i) (mem_image_of_mem (f i) hz'))

end GeneralDomain

end TauCeti
