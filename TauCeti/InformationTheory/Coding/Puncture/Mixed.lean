/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.Puncture.Basic
public import TauCeti.InformationTheory.Coding.Additive.Equivalence

/-!
# Commuting puncturing and shortening

Puncturing and shortening on disjoint deleted coordinate sets commute. Both orders retain
`s ∩ t`, where `s` is retained by puncturing and `t` by shortening. The canonical subtype
flattening equivalences put their results on this common coordinate type.

Without disjointness, puncturing after shortening is contained in shortening after puncturing:
the latter imposes zero only on `s \ t`, while the former imposes zero on all of `tᶜ`.
The membership criteria make this distinction explicit. These identities allow mixed coordinate
deletions to be reordered without changing the code when no coordinate is deleted twice.
They apply to additive codes over arbitrary abelian alphabets and specialize to linear codes.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.5 and 1.7.
-/

public section

namespace TauCeti
namespace AdditiveCode

variable {A ι : Type*} [AddCommGroup A]

-- These composite criteria are not simp lemmas: the individual membership rules already
-- simplify their left-hand sides. Use `rw` to obtain the single-lift formulations.

/-- After puncturing to `s` and shortening to `t`, a word on `s ∩ t` has a lift in the original
code which vanishes on `s \ t`. Coordinates outside `s` are unrestricted. -/
theorem mem_reindex_shorten_puncture_iff (C : AdditiveCode A ι) (s t : Set ι)
    (y : {i // i ∈ s ∧ i ∈ t} → A) :
    y ∈ reindex (shorten (puncture C s) (Subtype.val ⁻¹' t))
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (· ∈ t)).symm ↔
      ∃ x ∈ C, (∀ i ∈ s, i ∉ t → x i = 0) ∧ ∀ j : {i // i ∈ s ∧ i ∈ t}, x j = y j := by
  rw [mem_reindex, mem_shorten]
  constructor
  · rintro ⟨z, hz, hz0, hzy⟩
    obtain ⟨x, hx, hxz⟩ := mem_puncture.mp hz
    refine ⟨x, hx, fun i hi hit ↦ (hxz ⟨i, hi⟩).trans (hz0 ⟨i, hi⟩ hit), ?_⟩
    intro j
    exact (hxz ⟨j, j.2.1⟩).trans (hzy ⟨⟨j, j.2.1⟩, j.2.2⟩)
  · rintro ⟨x, hx, hx0, hxy⟩
    refine ⟨s.domRestrict x, mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩,
      fun i hit ↦ hx0 i i.2 hit, ?_⟩
    intro j
    exact hxy ⟨j.1, j.1.2, j.2⟩

/-- After shortening to `t` and puncturing to `s`, a word on `s ∩ t` has a lift in the original
code which vanishes everywhere outside `t`. -/
theorem mem_reindex_puncture_shorten_iff (C : AdditiveCode A ι) (s t : Set ι)
    (y : {i // i ∈ s ∧ i ∈ t} → A) :
    y ∈ reindex (puncture (shorten C t) (Subtype.val ⁻¹' s))
        ((Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ t) (· ∈ s)).symm) ↔
      ∃ x ∈ C, (∀ i ∉ t, x i = 0) ∧ ∀ j : {i // i ∈ s ∧ i ∈ t}, x j = y j := by
  rw [mem_reindex, mem_puncture]
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hx0, hxz⟩ := mem_shorten.mp hz
    refine ⟨x, hx, hx0, fun j ↦ ?_⟩
    exact (hxz ⟨j, j.2.2⟩).trans (hzy ⟨⟨j, j.2.2⟩, j.2.1⟩)
  · rintro ⟨x, hx, hx0, hxy⟩
    refine ⟨t.domRestrict x, mem_shorten.mpr ⟨x, hx, hx0, fun _ ↦ rfl⟩, fun j ↦ ?_⟩
    exact hxy ⟨j.1, j.2, j.1.2⟩

/-- Puncturing after shortening imposes at least the conditions imposed in the opposite order.
Both codes are transported to the retained coordinates `s ∩ t`. -/
theorem reindex_puncture_shorten_le (C : AdditiveCode A ι) (s t : Set ι) :
    reindex (puncture (shorten C t) (Subtype.val ⁻¹' s))
        ((Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ t) (· ∈ s)).symm) ≤
      reindex (shorten (puncture C s) (Subtype.val ⁻¹' t))
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (· ∈ t)).symm := by
  intro y hy
  obtain ⟨x, hx, hx0, hxy⟩ := (mem_reindex_puncture_shorten_iff C s t y).mp hy
  exact (mem_reindex_shorten_puncture_iff C s t y).mpr
    ⟨x, hx, fun i _ hit ↦ hx0 i hit, hxy⟩

/-- Puncturing and shortening commute when their deleted sets are disjoint, equivalently when
the retained sets cover all coordinates. Both orders are transported to `s ∩ t`. -/
theorem reindex_shorten_puncture_eq (C : AdditiveCode A ι) (s t : Set ι)
    (hst : s ∪ t = Set.univ) :
    reindex (shorten (puncture C s) (Subtype.val ⁻¹' t))
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (· ∈ t)).symm =
      reindex (puncture (shorten C t) (Subtype.val ⁻¹' s))
        ((Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ t) (· ∈ s)).symm) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, hx0, hxy⟩ := (mem_reindex_shorten_puncture_iff C s t y).mp hy
    refine (mem_reindex_puncture_shorten_iff C s t y).mpr ⟨x, hx, ?_, hxy⟩
    intro i hit
    have hi : i ∈ s ∪ t := hst ▸ Set.mem_univ i
    exact hx0 i (hi.resolve_right hit) hit
  · exact reindex_puncture_shorten_le C s t

end AdditiveCode

variable {F ι : Type*} [Field F]

/-- For linear codes, puncturing after shortening is contained in shortening after puncturing,
after identifying both retained coordinate types with `s ∩ t`. -/
theorem reindex_puncture_shorten_le (C : LinearCode F ι) (s t : Set ι) :
    reindex (puncture (shorten C t) (Subtype.val ⁻¹' s))
        ((Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ t) (· ∈ s)).symm) ≤
      reindex (shorten (puncture C s) (Subtype.val ⁻¹' t))
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (· ∈ t)).symm := by
  apply (Submodule.toAddSubgroup_le _ _).mp
  simpa only [← AdditiveCode.reindex_toAddSubgroup, LinearCode.puncture_toAddSubgroup,
    LinearCode.shorten_toAddSubgroup] using
    AdditiveCode.reindex_puncture_shorten_le C.toAddSubgroup s t

/-- Puncturing and shortening a linear code commute on disjoint deleted coordinate sets.
The retained sets cover all coordinates, and the output is indexed by their intersection. -/
theorem reindex_shorten_puncture_eq (C : LinearCode F ι) (s t : Set ι)
    (hst : s ∪ t = Set.univ) :
    reindex (shorten (puncture C s) (Subtype.val ⁻¹' t))
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (· ∈ t)).symm =
      reindex (puncture (shorten C t) (Subtype.val ⁻¹' s))
        ((Equiv.subtypeEquivRight (fun _ ↦ and_comm)).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ t) (· ∈ s)).symm) := by
  apply Submodule.toAddSubgroup_injective
  simpa only [← AdditiveCode.reindex_toAddSubgroup, LinearCode.puncture_toAddSubgroup,
    LinearCode.shorten_toAddSubgroup] using
    AdditiveCode.reindex_shorten_puncture_eq C.toAddSubgroup s t hst

end TauCeti
