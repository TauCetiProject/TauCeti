/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Puncture

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Information sets of linear codes

An information set is a set of retained coordinates on which restriction gives a linear
isomorphism from the code to the full word space. Thus every message on these coordinates
extends to exactly one codeword. The inverse is a systematic encoder, without making a
canonical choice of information coordinates.

This file characterizes information sets by puncturing and shortening, constructs the
restriction equivalence, and proves that every finite-length linear code has an information
set of cardinality equal to its dimension. Information sets are preserved by coordinate
reindexing. These results provide the intrinsic input for systematic matrix presentations.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
  Press, 2003, Sections 1.2–1.4.
-/

public section

namespace TauCeti

variable {F ι : Type*} [Field F]

/-- A retained set of coordinates is an information set if restriction to it is bijective
on the code. -/
def IsInformationSet (C : LinearCode F ι) (s : Set ι) : Prop :=
  Function.Bijective (fun x : C ↦ fun i : s ↦ (x : ι → F) i)

/-- The defining restriction criterion for an information set. -/
theorem isInformationSet_iff_bijective (C : LinearCode F ι) (s : Set ι) :
    IsInformationSet C s ↔
      Function.Bijective (fun x : C ↦ fun i : s ↦ (x : ι → F) i) := Iff.rfl

/-- Every message on an information set extends to exactly one codeword. -/
theorem isInformationSet_iff_existsUnique (C : LinearCode F ι) (s : Set ι) :
    IsInformationSet C s ↔ ∀ y : s → F, ∃! x : C, ∀ i : s, (x : ι → F) i = y i := by
  simp only [isInformationSet_iff_bijective, Function.bijective_iff_existsUnique, funext_iff]

/-- Restriction to an information set is a linear equivalence. Its inverse is the systematic
encoder with those information coordinates. -/
noncomputable def IsInformationSet.equiv {C : LinearCode F ι} {s : Set ι}
    (h : IsInformationSet C s) : C ≃ₗ[F] (s → F) :=
  LinearEquiv.ofBijective ((LinearMap.funLeft F F (Subtype.val : s → ι)).domRestrict C) h

/-- The information-set equivalence reads the retained coordinates. -/
@[simp]
theorem IsInformationSet.equiv_apply {C : LinearCode F ι} {s : Set ι}
    (h : IsInformationSet C s) (x : C) (i : s) : h.equiv x i = (x : ι → F) i := (rfl)

/-- Encoding a message preserves each information coordinate. -/
@[simp]
theorem IsInformationSet.equiv_symm_apply {C : LinearCode F ι} {s : Set ι}
    (h : IsInformationSet C s) (y : s → F) (i : s) :
    (h.equiv.symm y : ι → F) i = y i :=
  congrFun (h.equiv.apply_symm_apply y) i

/-- A retained set is an information set exactly when puncturing fills its word space and
shortening to the complementary coordinates gives the zero code. -/
theorem isInformationSet_iff_puncture_eq_top_and_shorten_compl_eq_bot
    (C : LinearCode F ι) (s : Set ι) :
    IsInformationSet C s ↔ puncture C s = ⊤ ∧ shorten C sᶜ = ⊥ := by
  constructor
  · intro h
    constructor
    · apply top_unique
      intro y _
      obtain ⟨x, hx⟩ := h.2 y
      exact mem_puncture.mpr ⟨x, x.property, fun i ↦ congrFun hx i⟩
    · apply bot_unique
      intro y hy
      obtain ⟨x, hx, hx0, hxy⟩ := mem_shorten.mp hy
      have hz : (⟨x, hx⟩ : C) = 0 := h.1 (by
        funext i
        exact hx0 i (by simpa only [Set.mem_compl_iff, not_not] using i.property))
      have hxz : x = 0 := congrArg Subtype.val hz
      apply funext
      intro i
      simpa [hxz] using (hxy i).symm
  · rintro ⟨hp, hs⟩
    constructor
    · intro x z hxz
      have hd : (fun i : ↥(sᶜ) ↦ (x : ι → F) i - (z : ι → F) i) ∈ shorten C sᶜ := by
        refine mem_shorten.mpr ⟨(x : ι → F) - (z : ι → F), C.sub_mem x.property z.property, ?_,
          fun _ ↦ rfl⟩
        intro i hi
        have his : i ∈ s := by simpa using hi
        exact sub_eq_zero.mpr (congrFun hxz ⟨i, his⟩)
      rw [hs, Submodule.mem_bot] at hd
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ s
      · exact congrFun hxz ⟨i, hi⟩
      · exact sub_eq_zero.mp (congrFun hd ⟨i, hi⟩)
    · intro y
      have hy : y ∈ puncture C s := hp ▸ Submodule.mem_top
      obtain ⟨x, hx, hxy⟩ := mem_puncture.mp hy
      exact ⟨⟨x, hx⟩, funext hxy⟩

/-- A finite information set has one coordinate per dimension of the code. -/
theorem IsInformationSet.ncard_eq_finrank {C : LinearCode F ι} {s : Set ι}
    [Finite s] (h : IsInformationSet C s) : s.ncard = Module.finrank F C := by
  let := Fintype.ofFinite s
  rw [h.equiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  exact (Set.fintypeCard_eq_ncard s).symm

/-- Every finite-dimensional linear code has a finite information set. No particular set is
canonical; finite-length codes are a special case. -/
theorem exists_isInformationSet (C : LinearCode F ι) [FiniteDimensional F C] :
    ∃ s : Set ι, s.Finite ∧ IsInformationSet C s := by
  classical
  let v : ι → Module.Dual F C := fun i ↦ (LinearMap.proj i).comp C.subtype
  have hv : Submodule.span F (Set.range v) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro x hx
    have hx' : (x : ι → F) ≠ 0 := by simpa using hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx'
    exact ⟨v i, Set.mem_range_self i, hi⟩
  obtain ⟨s, _, _, hspan, hli⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty F v) (Set.empty_subset Set.univ)
  have hs : Submodule.span F (Set.range fun i : s ↦ v i) = ⊤ := by
    rw [← Set.image_eq_range]
    apply top_unique
    rw [← hv]
    exact Submodule.span_le.mpr (by simpa using hspan)
  let b : Module.Basis s F (Module.Dual F C) := Module.Basis.mk hli hs.ge
  have : Finite s := Module.Finite.finite_basis b
  let e : C ≃ₗ[F] (s → F) := (Module.evalEquiv F C).trans b.dualBasis.equivFun
  have he : ∀ x : C, e x = fun i : s ↦ (x : ι → F) i := by
    intro x
    funext i
    simp only [e, LinearEquiv.trans_apply, Module.Basis.dualBasis_equivFun,
      Module.evalEquiv_apply, Module.Dual.eval_apply]
    exact congrArg (fun f : Module.Dual F C ↦ f x) (Module.Basis.mk_apply hli hs.ge i)
  refine ⟨s, Set.toFinite s, ?_⟩
  rw [isInformationSet_iff_bijective, ← funext he]
  exact e.bijective

/-- A coordinate reindexing carries an information set to its inverse image. -/
theorem IsInformationSet.reindex {C : LinearCode F ι} {s : Set ι}
    (h : IsInformationSet C s) {κ : Type*} (e : κ ≃ ι) :
    IsInformationSet (reindex C e) (e ⁻¹' s) := by
  rw [isInformationSet_iff_puncture_eq_top_and_shorten_compl_eq_bot] at h ⊢
  constructor
  · rw [puncture_reindex, h.1, reindex_top]
  · rw [← Set.preimage_compl, shorten_reindex, h.2, reindex_bot]

/-- Being an information set is invariant under coordinate reindexing. -/
@[simp]
theorem isInformationSet_reindex_iff {C : LinearCode F ι} {s : Set ι}
    {κ : Type*} (e : κ ≃ ι) :
    IsInformationSet (reindex C e) (e ⁻¹' s) ↔ IsInformationSet C s := by
  constructor
  · intro h
    simpa [← Set.preimage_comp] using h.reindex e.symm
  · exact fun h ↦ h.reindex e

end TauCeti
