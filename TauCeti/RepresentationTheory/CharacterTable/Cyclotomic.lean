/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Eigenrow
import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RingTheory.Cyclotomic.Integral

/-!
# Exact cyclotomic representatives of character-table entries

Both the ordinary and central character tables of a finite group have entries in the image of
the distinguished embedding of `TauCeti.Cyclotomic e`, where `e` is the group exponent.
Ordinary character values are sums of roots of unity. Central-character values are integral
and are rational multiples of ordinary values, so they belong to the ring of integers of the
same cyclotomic field. These representatives supply the exact tables needed for reconstruction
from modular character data.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] (e : ℕ) [NeZero e] (he : e = Monoid.exponent G)

include he

section Finite

variable [Finite G]

/-- Every ordinary character-table entry has an exact cyclotomic representative at the group
exponent. -/
theorem characterTable_mem_range_complexEmbedding
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    characterTable ℂ G i C ∈ Set.range (Cyclotomic.complexEmbedding (e := e)) := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  rw [Cyclotomic.mem_range_complexEmbedding_iff, characterTable_apply,
    ← character_irreducibleRepresentation]
  exact Representation.char_mem_adjoin_of_isPrimitiveRoot (irreducibleRepresentation ℂ i)
    Cyclotomic.isPrimitiveRoot_complexRoot (he ▸ Monoid.pow_exponent_eq_one g)

end Finite

variable [Fintype G] [DecidableEq G]

/-- Every central character-table entry has an exact cyclotomic representative at the group
exponent, including when its expression in terms of ordinary values involves division by the
character degree. -/
theorem centralCharacterTable_mem_range_complexEmbedding
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    centralCharacterTable ℂ G i C ∈ Set.range (Cyclotomic.complexEmbedding (e := e)) := by
  apply Cyclotomic.mem_range_complexEmbedding_of_isIntegral
  · let K := IntermediateField.adjoin ℚ {Cyclotomic.complexRoot e}
    have hchar : characterTable ℂ G i C ∈ K := by
      have hle : Algebra.adjoin ℤ {Cyclotomic.complexRoot e} ≤
          K.toSubalgebra.restrictScalars ℤ := by
        apply Algebra.adjoin_le
        exact Set.singleton_subset_iff.mpr
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
      exact hle (Cyclotomic.mem_range_complexEmbedding_iff.mp
        (characterTable_mem_range_complexEmbedding e he i C))
    rw [centralCharacterTable_eq_div i
      (Nat.cast_ne_zero.mpr (characterDegree_pos ℂ i).ne')]
    exact K.div_mem (K.mul_mem (K.natCast_mem _) hchar) (K.natCast_mem _)
  · rw [centralCharacterTable_apply]
    exact Representation.isIntegral_centralCharacter_classSumCenter _ C

end TauCeti
