/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Golay.Basic
public import TauCeti.InformationTheory.Coding.MinimumDistance.Operations
public import TauCeti.InformationTheory.Coding.ParityExtension

/-!
# The binary Golay code of length twenty-three

Deleting one coordinate from the extended binary Golay code leaves the binary Golay code with
parameters `[23, 12, 7]`. The dimension is unchanged because the extended code has minimum
distance eight, and the minimum distance drops by exactly one because every coordinate is met
by an octad, whose restriction is then a codeword of weight seven.

All weights of the extended code are even, so restoring the parity coordinate recovers it: the
parity extension of a punctured Golay code is the extended Golay code with its coordinates
relabelled, hence permutation equivalent to it. This is the exact sense in which the length-23
code determines the length-24 one.

The conventions are those of Huffman and Pless, *Fundamentals of Error-Correcting Codes*,
§1.5 and Chapter 9.
-/

public section

namespace TauCeti.BinaryGolay

variable (i : Fin 24)

/-- A punctured binary Golay code has length twenty-three: deleting one of the twenty-four
coordinates leaves twenty-three. -/
theorem card_compl_singleton : Fintype.card ({i}ᶜ : Set (Fin 24)) = 23 := by
  rw [Fintype.card_compl_set]
  simp

/-- A punctured binary Golay code has dimension twelve. -/
@[simp]
theorem finrank_punctureAt_code :
    Module.finrank (ZMod 2) (punctureAt code i) = 12 := by
  rw [finrank_punctureAt_eq code i (by rw [hammingMinDist_code]; norm_num), finrank_code]

/-- A punctured binary Golay code has 4096 words. -/
@[simp↓]
theorem natCard_punctureAt_code : Nat.card (punctureAt code i) = 4096 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_punctureAt_code]
  norm_num [Nat.card_eq_fintype_card]

/-- A punctured binary Golay code has minimum distance seven. -/
@[simp]
theorem hammingMinDist_punctureAt_code :
    Set.hammingMinDist (punctureAt code i : Set (({i}ᶜ : Set (Fin 24)) → ZMod 2)) = 7 := by
  obtain ⟨x, hx, hxw, hxi⟩ := exists_mem_code_hammingNorm_eq_eight i
  -- Split the octad into its retained part `y` and the single deleted coordinate `z`.
  set y := ({i}ᶜ : Set (Fin 24)).domRestrict x with hy
  set z := (({i}ᶜ : Set (Fin 24))ᶜ).domRestrict x with hz
  have hyC : y ∈ punctureAt code i := by
    rw [punctureAt_def]
    exact mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩
  have hzw : hammingNorm z = 1 := by
    have hle : hammingNorm z ≤ 1 := by
      simpa only [hz, compl_compl, Fintype.card_unique] using
        hammingNorm_le_card_fintype (x := z)
    have hne : z ≠ 0 := fun h ↦ hxi (congrFun h ⟨i, by simp⟩)
    have := (hammingNorm_eq_zero (x := z)).not.mpr hne
    omega
  have hyw : hammingNorm y = 7 := by
    have hsplit := hammingNorm_eq_domRestrict_add_domRestrict_compl ({i}ᶜ : Set (Fin 24)) x
    rw [hxw, ← hy, ← hz, hzw] at hsplit
    omega
  have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hyw
  have hupper := Set.hammingMinDist_le_hammingNorm (E := (punctureAt code i).toAddSubgroup)
    hyC hy0
  rw [Submodule.coe_toAddSubgroup, hyw] at hupper
  have hlower := hammingMinDist_le_hammingMinDist_punctureAt_add_one code i
  rw [hammingMinDist_code] at hlower
  omega

/-- Restoring the parity coordinate to a punctured binary Golay code gives back the extended
binary Golay code, with the deleted coordinate reinstated at `none`. -/
theorem parityExtension_punctureAt_code :
    parityExtension (punctureAt code i) = reindex code (Equiv.optionSubtypeNe i) :=
  parityExtension_punctureAt code i code_le_singleParityCheckCode

/-- Extending a punctured binary Golay code by its parity coordinate gives a code permutation
equivalent to the extended binary Golay code. -/
theorem isPermutationEquivalent_parityExtension_punctureAt_code :
    IsPermutationEquivalent (parityExtension (punctureAt code i)) code :=
  parityExtension_punctureAt_code i ▸ isPermutationEquivalent_reindex code
    (Equiv.optionSubtypeNe i)

end TauCeti.BinaryGolay
