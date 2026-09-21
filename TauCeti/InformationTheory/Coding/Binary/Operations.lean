/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.InformationTheory.Coding.DirectSum
public import TauCeti.InformationTheory.Coding.Equivalence

/-!
# Operations on even and doubly-even binary codes

Evenness and double evenness are preserved by direct sums and coordinate permutations. Over the
binary field every unit is one, so monomial transformations are exactly coordinate permutations;
consequently the same invariance holds for monomial equivalence, and the monomial and permutation
automorphism groups of a binary code coincide.

These results provide the closure properties used to build larger self-orthogonal binary codes
from smaller ones without changing the divisibility conditions on their Hamming weights.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, Chapters 1
and 9.
-/

public section

namespace TauCeti

/-! ### Binary monomial transformations -/

variable {ι κ : Type*}

/-- Over the binary field, a monomial transformation is its underlying coordinate permutation. -/
theorem monomialEquiv_zmod_two_eq_funCongrLeft (u : ι → (ZMod 2)ˣ) (e : ι ≃ κ) :
    monomialEquiv u e = LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm := by
  rw [Subsingleton.elim u 1, monomialEquiv_one]

/-- Over the binary field, the monomial group equals the coordinate-permutation group. -/
theorem monomialGroup_zmod_two_eq_permutationGroup :
    monomialGroup (ZMod 2) ι = permutationGroup (ZMod 2) ι := by
  apply le_antisymm
  · intro f hf
    obtain ⟨u, e, rfl⟩ := mem_monomialGroup.mp hf
    exact mem_permutationGroup.mpr
      ⟨e, (monomialEquiv_zmod_two_eq_funCongrLeft u e).symm⟩
  · exact permutationGroup_le_monomialGroup

/-- For binary linear codes, monomial equivalence is the same as permutation equivalence. -/
theorem isMonomialEquivalent_zmod_two_iff {C : LinearCode (ZMod 2) ι}
    {D : LinearCode (ZMod 2) κ} :
    IsMonomialEquivalent C D ↔ IsPermutationEquivalent C D := by
  constructor
  · rw [isMonomialEquivalent_iff, isPermutationEquivalent_iff]
    rintro ⟨u, e, h⟩
    exact ⟨e, (monomialEquiv_zmod_two_eq_funCongrLeft u e) ▸ h⟩
  · exact IsPermutationEquivalent.isMonomialEquivalent

/-- The monomial and permutation automorphism groups of a binary linear code coincide. -/
theorem monomialAut_zmod_two_eq_permutationAut (C : LinearCode (ZMod 2) ι) :
    monomialAut C = permutationAut C := by
  ext f
  rw [mem_monomialAut, mem_permutationAut, monomialGroup_zmod_two_eq_permutationGroup]

/-! ### Direct sums -/

namespace BinaryCode

variable {C : LinearCode (ZMod 2) ι} {D : LinearCode (ZMod 2) κ}

/-- The direct sum of two even binary codes is even. -/
theorem IsEven.directSum [Fintype ι] [Fintype κ] (hC : IsEven C) (hD : IsEven D) :
    IsEven (C.directSum D) := by
  rw [isEven_iff] at hC hD
  rw [isEven_iff]
  intro x hx
  let z : C.directSum D := ⟨x, hx⟩
  let p := C.directSumEquivProd D z
  have hweight := Submodule.hammingNorm_directSumEquivProd_symm C D p.1 p.2
  have hz : (C.directSumEquivProd D).symm p = z := LinearEquiv.symm_apply_apply _ _
  rw [hz] at hweight
  rw [hweight]
  exact (hC p.1 p.1.2).add (hD p.2 p.2.2)

/-- A direct sum of binary codes is even exactly when both summands are even. -/
@[simp]
theorem isEven_directSum_iff [Fintype ι] [Fintype κ] :
    IsEven (C.directSum D) ↔ IsEven C ∧ IsEven D := by
  constructor
  · intro h
    rw [isEven_iff] at h
    constructor
    · rw [isEven_iff]
      intro x hx
      have hmem : Sum.elim x (0 : κ → ZMod 2) ∈ C.directSum D := by
        rw [Submodule.mem_directSum_iff]
        exact ⟨hx, D.zero_mem⟩
      simpa using h (Sum.elim x (0 : κ → ZMod 2)) hmem
    · rw [isEven_iff]
      intro y hy
      have hmem : Sum.elim (0 : ι → ZMod 2) y ∈ C.directSum D := by
        rw [Submodule.mem_directSum_iff]
        exact ⟨C.zero_mem, hy⟩
      simpa using h (Sum.elim (0 : ι → ZMod 2) y) hmem
  · rintro ⟨hC, hD⟩
    exact hC.directSum hD

/-- The direct sum of two doubly-even binary codes is doubly even. -/
theorem IsDoublyEven.directSum [Fintype ι] [Fintype κ]
    (hC : IsDoublyEven C) (hD : IsDoublyEven D) : IsDoublyEven (C.directSum D) := by
  rw [isDoublyEven_iff] at hC hD
  rw [isDoublyEven_iff]
  intro x hx
  let z : C.directSum D := ⟨x, hx⟩
  let p := C.directSumEquivProd D z
  have hweight := Submodule.hammingNorm_directSumEquivProd_symm C D p.1 p.2
  have hz : (C.directSumEquivProd D).symm p = z := LinearEquiv.symm_apply_apply _ _
  rw [hz] at hweight
  rw [hweight]
  exact dvd_add (hC p.1 p.1.2) (hD p.2 p.2.2)

/-- A direct sum of binary codes is doubly even exactly when both summands are doubly even. -/
@[simp]
theorem isDoublyEven_directSum_iff [Fintype ι] [Fintype κ] :
    IsDoublyEven (C.directSum D) ↔ IsDoublyEven C ∧ IsDoublyEven D := by
  constructor
  · intro h
    rw [isDoublyEven_iff] at h
    constructor
    · rw [isDoublyEven_iff]
      intro x hx
      have hmem : Sum.elim x (0 : κ → ZMod 2) ∈ C.directSum D := by
        rw [Submodule.mem_directSum_iff]
        exact ⟨hx, D.zero_mem⟩
      simpa using h (Sum.elim x (0 : κ → ZMod 2)) hmem
    · rw [isDoublyEven_iff]
      intro y hy
      have hmem : Sum.elim (0 : ι → ZMod 2) y ∈ C.directSum D := by
        rw [Submodule.mem_directSum_iff]
        exact ⟨C.zero_mem, hy⟩
      simpa using h (Sum.elim (0 : ι → ZMod 2) y) hmem
  · rintro ⟨hC, hD⟩
    exact hC.directSum hD

/-! ### Equivalence invariance -/

variable [Fintype ι] [Fintype κ]

/-- Permutation equivalence preserves evenness of binary codes. -/
theorem IsEven.of_isPermutationEquivalent (hC : IsEven C) (h : IsPermutationEquivalent C D) :
    IsEven D := by
  rw [isPermutationEquivalent_iff] at h
  obtain ⟨e, he⟩ := h
  rw [isEven_iff] at hC
  rw [isEven_iff]
  intro y hy
  rw [← he] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hweight := hammingNorm_monomialEquiv (1 : ι → (ZMod 2)ˣ) e x
  rw [monomialEquiv_one] at hweight
  exact hweight.symm ▸ hC x hx

/-- Evenness of binary codes is invariant under permutation equivalence. -/
theorem isEven_iff_of_isPermutationEquivalent (h : IsPermutationEquivalent C D) :
    IsEven C ↔ IsEven D :=
  ⟨fun hC ↦ hC.of_isPermutationEquivalent h,
    fun hD ↦ hD.of_isPermutationEquivalent h.symm⟩

/-- Permutation equivalence preserves double evenness of binary codes. -/
theorem IsDoublyEven.of_isPermutationEquivalent (hC : IsDoublyEven C)
    (h : IsPermutationEquivalent C D) : IsDoublyEven D := by
  rw [isPermutationEquivalent_iff] at h
  obtain ⟨e, he⟩ := h
  rw [isDoublyEven_iff] at hC
  rw [isDoublyEven_iff]
  intro y hy
  rw [← he] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hweight := hammingNorm_monomialEquiv (1 : ι → (ZMod 2)ˣ) e x
  rw [monomialEquiv_one] at hweight
  exact hweight.symm ▸ hC x hx

/-- Double evenness of binary codes is invariant under permutation equivalence. -/
theorem isDoublyEven_iff_of_isPermutationEquivalent (h : IsPermutationEquivalent C D) :
    IsDoublyEven C ↔ IsDoublyEven D :=
  ⟨fun hC ↦ hC.of_isPermutationEquivalent h,
    fun hD ↦ hD.of_isPermutationEquivalent h.symm⟩

/-- Evenness of binary codes is invariant under monomial equivalence. -/
theorem isEven_iff_of_isMonomialEquivalent (h : IsMonomialEquivalent C D) :
    IsEven C ↔ IsEven D :=
  isEven_iff_of_isPermutationEquivalent (isMonomialEquivalent_zmod_two_iff.mp h)

/-- Double evenness of binary codes is invariant under monomial equivalence. -/
theorem isDoublyEven_iff_of_isMonomialEquivalent (h : IsMonomialEquivalent C D) :
    IsDoublyEven C ↔ IsDoublyEven D :=
  isDoublyEven_iff_of_isPermutationEquivalent (isMonomialEquivalent_zmod_two_iff.mp h)

end BinaryCode

end TauCeti
