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

Evenness and double evenness are preserved by direct sums and by monomial equivalence, hence
also by coordinate permutations. Over the binary field every unit is one, so the two notions of
equivalence agree anyway, by `TauCeti.isMonomialEquivalent_iff_isPermutationEquivalent`.

These results provide the closure properties used to build larger self-orthogonal binary codes
from smaller ones without changing the divisibility conditions on their Hamming weights.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, Chapters 1
and 9.
-/

public section

namespace TauCeti

namespace BinaryCode

variable {ι κ : Type*} {C : LinearCode (ZMod 2) ι} {D : LinearCode (ZMod 2) κ}
  [Fintype ι] [Fintype κ]

/-! ### Direct sums -/

/-- A direct sum of binary codes is even exactly when both summands are even. -/
@[simp]
theorem isEven_directSum_iff : IsEven (C.directSum D) ↔ IsEven C ∧ IsEven D := by
  simp only [isEven_iff, even_iff_two_dvd]
  exact Submodule.forall_dvd_hammingNorm_directSum_iff C D 2

/-- The direct sum of two even binary codes is even. -/
theorem IsEven.directSum (hC : IsEven C) (hD : IsEven D) : IsEven (C.directSum D) :=
  isEven_directSum_iff.mpr ⟨hC, hD⟩

/-- A direct sum of binary codes is doubly even exactly when both summands are doubly even. -/
@[simp]
theorem isDoublyEven_directSum_iff :
    IsDoublyEven (C.directSum D) ↔ IsDoublyEven C ∧ IsDoublyEven D := by
  simp only [isDoublyEven_iff]
  exact Submodule.forall_dvd_hammingNorm_directSum_iff C D 4

/-- The direct sum of two doubly-even binary codes is doubly even. -/
theorem IsDoublyEven.directSum (hC : IsDoublyEven C) (hD : IsDoublyEven D) :
    IsDoublyEven (C.directSum D) :=
  isDoublyEven_directSum_iff.mpr ⟨hC, hD⟩

/-! ### Equivalence invariance -/

/-- Evenness of binary codes is invariant under monomial equivalence. -/
theorem isEven_iff_of_isMonomialEquivalent (h : IsMonomialEquivalent C D) :
    IsEven C ↔ IsEven D := by
  simpa only [isEven_iff, even_iff_two_dvd] using h.forall_dvd_hammingNorm_iff 2

/-- Monomial equivalence preserves evenness of binary codes. -/
theorem IsEven.of_isMonomialEquivalent (hC : IsEven C) (h : IsMonomialEquivalent C D) :
    IsEven D :=
  (isEven_iff_of_isMonomialEquivalent h).mp hC

/-- Double evenness of binary codes is invariant under monomial equivalence. -/
theorem isDoublyEven_iff_of_isMonomialEquivalent (h : IsMonomialEquivalent C D) :
    IsDoublyEven C ↔ IsDoublyEven D := by
  rw [isDoublyEven_iff, isDoublyEven_iff]
  exact h.forall_dvd_hammingNorm_iff 4

/-- Monomial equivalence preserves double evenness of binary codes. -/
theorem IsDoublyEven.of_isMonomialEquivalent (hC : IsDoublyEven C)
    (h : IsMonomialEquivalent C D) : IsDoublyEven D :=
  (isDoublyEven_iff_of_isMonomialEquivalent h).mp hC

end BinaryCode

end TauCeti
