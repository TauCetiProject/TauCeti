/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.CharacterTable.CoefficientBounds
public import TauCeti.RepresentationTheory.CharacterTable.Eigenrow
import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RingTheory.Cyclotomic.Bounds
public import TauCeti.RingTheory.Cyclotomic.Integral

/-!
# Exact cyclotomic representatives of character-table entries

Both the ordinary and central character tables of a finite group have entries in the image of
the distinguished embedding of `TauCeti.Cyclotomic e`, where `e` is the group exponent.
Ordinary character values are sums of roots of unity. Central-character values are integral
and are rational multiples of ordinary values, so they belong to the ring of integers of the
same cyclotomic field. These representatives supply the exact tables needed for reconstruction
from modular character data. The central representative on a class `C` has power-basis
coefficients bounded by `|C| * Cyclotomic.rootCoeffBound e`, and is tied to the ordinary one by
the division-free identity `d * w = |C| * x`.
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

/-- **Exact ordinary and central values.** The entries of the ordinary and central tables at a
row and a class `C` are the complex images of exact elements `x` and `w`, satisfying the
division-free identity `d * w = |C| * x` for the degree `d` of the row, and the coefficients of
`w` are bounded by `|C| * Cyclotomic.rootCoeffBound e`, with no dependence on the degree. -/
theorem exists_exact_character_and_central_values
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    ∃ x w : Cyclotomic e,
      Cyclotomic.complexEmbedding x = characterTable ℂ G i C ∧
      Cyclotomic.complexEmbedding w = centralCharacterTable ℂ G i C ∧
      (characterDegree ℂ i : Cyclotomic e) * w = (Nat.card C.carrier : Cyclotomic e) * x ∧
      ∀ j, (w.coeff j).natAbs ≤ Nat.card C.carrier * Cyclotomic.rootCoeffBound e := by
  obtain ⟨x, hx⟩ := characterTable_mem_range_complexEmbedding e he i C
  obtain ⟨w, hw⟩ := centralCharacterTable_mem_range_complexEmbedding e he i C
  have hmul := centralCharacterTable_mul_characterDegree (k := ℂ) i C
  refine ⟨x, w, hx, hw, Cyclotomic.complexEmbedding_injective ?_, fun j ↦ ?_⟩
  · simpa only [map_mul, map_natCast, hx, hw, mul_comm] using hmul
  · obtain ⟨g, rfl⟩ := C.exists_rep
    apply Representation.coeff_natAbs_le_of_finrank_mul_complexEmbedding_eq_natCast_mul_char
      (irreducibleRepresentation ℂ i) (he ▸ Monoid.pow_exponent_eq_one g)
      (by simpa using characterDegree_pos ℂ i)
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hw, mul_comm,
      character_irreducibleRepresentation, characterTable_apply] using hmul

end TauCeti
