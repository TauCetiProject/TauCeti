/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.CompactOpen

/-!
# Local boundedness of families on compact sets

A family of maps is locally bounded on a set if its values on each compact subset admit a norm
bound uniform in the index. The definition only needs a topological domain and a norm on the
target. Local boundedness is preserved by restricting the domain or reindexing the family, and
implies a uniform bound at each point.

For seminormed group targets, relative compactness of the continuous restrictions implies local
boundedness. This uses the compact-open topology and works on an arbitrary topological domain:
restriction to a compact subset makes joint evaluation continuous, and compactness bounds the norm
of all evaluations there at once.

## Main results

* `TauCeti.IsLocallyBoundedOn`: uniform boundedness on each compact subset.
* `TauCeti.IsLocallyBoundedOn.mono` and `TauCeti.IsLocallyBoundedOn.comp`: stability under domain
  restriction and reindexing.
* `TauCeti.isLocallyBoundedOn_of_isCompact_closure_range`: relative compactness of continuous
  restrictions gives local boundedness.
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

/-- A family of maps into a seminormed group whose continuous restrictions to `Ω` are relatively
compact in `C(↥Ω, E)` is locally bounded on `Ω`.

The domain is an arbitrary topological space; local compactness is not required. -/
theorem isLocallyBoundedOn_of_isCompact_closure_range
    (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) (hcpt : IsCompact (closure (Set.range f))) :
    IsLocallyBoundedOn F Ω := by
  refine isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set Ω) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
  let S : Set Ω := Subtype.val ⁻¹' K
  have : CompactSpace S := isCompact_iff_compactSpace.mp hK'
  -- Restriction to the compact domain S makes joint evaluation continuous.
  have hcont : Continuous fun p : C(Ω, E) × S => ‖(p.1.restrict S) p.2‖ :=
    (continuous_eval.comp ((ContinuousMap.continuous_restrict S).prodMap continuous_id)).norm
  obtain ⟨C, hC⟩ := ((hcpt.prod isCompact_univ).image hcont).bddAbove
  refine ⟨C, fun i z hz => ?_⟩
  have hmem : (f i, (⟨⟨z, hKΩ hz⟩, hz⟩ : S)) ∈
      closure (Set.range f) ×ˢ (univ : Set S) :=
    ⟨subset_closure ⟨i, rfl⟩, mem_univ _⟩
  simpa [ContinuousMap.restrict_apply, hf i] using hC (mem_image_of_mem _ hmem)

end GeneralDomain

end TauCeti
