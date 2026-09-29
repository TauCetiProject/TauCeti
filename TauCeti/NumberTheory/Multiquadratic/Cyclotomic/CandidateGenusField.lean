/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Basic
public import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.GenusCharGroup
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant

/-!
# The candidate genus field as a cyclotomic character subfield

For squarefree `d` with fundamental discriminant `D`, the candidate genus field of `ℚ(√d)` is the
compositum of the quadratic fields `ℚ(√P)` over the prime discriminants `P` dividing `D`. It lies
in every cyclotomic subfield `K ⊆ ℂ` of level `|D|`, and inside `K` the Galois correspondence
identifies it with the intermediate field attached to the genus characters, the Dirichlet
characters of level `|D|` that are products of the quadratic characters of the prime
discriminants dividing `D`. This is the explicit Kronecker–Weber description of the genus field:
it is cut out of `ℚ(ζ_|D|)` by the genus character group.

## Main results

* `TauCeti.Multiquadratic.genusFieldRoot_mem_of_isCyclotomicExtension`: every chosen root
  generating the candidate genus field lies in a cyclotomic subfield of `ℂ` of level `|D|`.
* `TauCeti.Multiquadratic.candidateGenusField_eq_map_characterSubfield_genusCharGroup`: the
  candidate genus field is the image in `ℂ` of the character subfield of the genus character
  group.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
-/

public section

open IntermediateField IsCyclotomicExtension IsCyclotomicExtension.Rat

namespace TauCeti.Multiquadratic

variable {d : ℤ} (hd : Squarefree d) (K : IntermediateField ℚ ℂ) [NumberField K]
  [IsCyclotomicExtension {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K]

/-- The level of the genus characters, `|∏ P| = |D|`, is nonzero. -/
instance neZero_natAbs_prod_genusPrimeDiscriminants :
    NeZero (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs :=
  ⟨by
    rw [(genusPrimeDiscriminants_spec hd).2.2]
    exact Int.natAbs_ne_zero.mpr (fundamentalDiscriminant_ne_zero hd.ne_zero)⟩

omit [NumberField K] in
include K in
/-- **Every chosen root of the candidate genus field lies in a cyclotomic field of level `|D|`.**
-/
theorem genusFieldRoot_mem_of_isCyclotomicExtension
    (P : {P // P ∈ genusPrimeDiscriminants hd}) : genusFieldRoot hd P ∈ K := by
  have hN : 0 < (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs :=
    Nat.pos_of_ne_zero (neZero_natAbs_prod_genusPrimeDiscriminants hd).out
  have hζ : IsPrimitiveRoot ((zeta (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs ℚ K : K) : ℂ)
      (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs :=
    (zeta_spec _ ℚ K).map_of_injective (f := K.val) Subtype.val_injective
  refine candidateGenusField_le_of_isPrimitiveRoot hd hN hζ (zeta _ ℚ K).2 ?_
    (genusFieldRoot_mem_candidateGenusField hd P)
  rw [(genusPrimeDiscriminants_spec hd).2.2]

/-- The rational scalar turning the chosen root of the radicand of `P` into a root of `P`
itself: `2` when `P` is an even prime discriminant, `1` otherwise. -/
noncomputable def genusFieldRootScale (P : {P // P ∈ genusPrimeDiscriminants hd}) : ℚ :=
  if (P : ℤ) = 4 * primeDiscriminantRadicand P then 2 else 1

/-- The scale is nonzero. -/
theorem genusFieldRootScale_ne_zero (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    genusFieldRootScale hd P ≠ 0 := by
  unfold genusFieldRootScale
  split_ifs <;> norm_num

omit [NumberField K] in
include K in
/-- A square root of the prime discriminant `P` itself, inside the cyclotomic field `K`. -/
@[expose] noncomputable def genusFieldRootOfPrimeDiscriminant
    (P : {P // P ∈ genusPrimeDiscriminants hd}) : K :=
  ⟨algebraMap ℚ ℂ (genusFieldRootScale hd P) * genusFieldRoot hd P,
    K.mul_mem (K.algebraMap_mem _) (genusFieldRoot_mem_of_isCyclotomicExtension hd K P)⟩

omit [NumberField K] in
@[simp] theorem coe_genusFieldRootOfPrimeDiscriminant
    (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    (genusFieldRootOfPrimeDiscriminant hd K P : ℂ) =
      algebraMap ℚ ℂ (genusFieldRootScale hd P) * genusFieldRoot hd P :=
  rfl

omit [NumberField K] in
/-- The rescaled root squares to the prime discriminant. -/
theorem genusFieldRootOfPrimeDiscriminant_sq (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    genusFieldRootOfPrimeDiscriminant hd K P ^ 2 = ((P : ℤ) : K) := by
  have hP := (genusPrimeDiscriminants_spec hd).1 P P.2
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_genusFieldRootOfPrimeDiscriminant, mul_pow, genusFieldRoot_sq,
    SubringClass.coe_intCast]
  unfold genusFieldRootScale
  rcases primeDiscriminant_eq_radicand_or_eq_four_mul_radicand hP with h | h
  · have h4 : ¬ ((P : ℤ) = 4 * primeDiscriminantRadicand P) := by
      intro h4
      have : primeDiscriminantRadicand P = 0 := by linarith
      exact hP.ne_zero (by rw [h, this])
    rw [ite_eq_right_of_eq_false _ _ (eq_false h4), map_one, one_pow, one_mul, ← h]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), map_ofNat]
    conv_rhs => rw [h]
    push_cast
    ring

/-- **The candidate genus field is cut out of the cyclotomic field by the genus characters.** For
squarefree `d` with fundamental discriminant `D` and a cyclotomic subfield `K ⊆ ℂ` of level `|D|`,
the candidate genus field of `ℚ(√d)` is the image in `ℂ` of the intermediate field of `K` that the
character correspondence attaches to the genus character group of `D`. -/
theorem candidateGenusField_eq_map_characterSubfield_genusCharGroup [IsAbelianGalois ℚ K]
    (R : Type*) [CommRing R] [CharZero R]
    [HasEnoughRootsOfUnity R
      (Monoid.exponent (ZMod (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs)ˣ)] :
    candidateGenusField hd =
      ((intermediateFieldEquivSubgroupChar (∏ P ∈ genusPrimeDiscriminants hd, P).natAbs K R).symm
        ((genusCharGroup (genusPrimeDiscriminants hd) (genusPrimeDiscriminants_spec hd).1).map
          (MulChar.ringHomCompHom (Int.castRingHom R)))).map K.val := by
  rw [characterSubfield_genusCharGroup_eq_adjoin_range _ _ R
    (genusFieldRootOfPrimeDiscriminant hd K) (genusFieldRootOfPrimeDiscriminant_sq hd K),
    adjoin_map, ← Set.range_comp, candidateGenusField_def]
  refine le_antisymm (adjoin_le_iff.mpr ?_) (adjoin_le_iff.mpr ?_)
  · rintro _ ⟨P, rfl⟩
    have hscale : genusFieldRoot hd P =
        (algebraMap ℚ ℂ (genusFieldRootScale hd P))⁻¹ *
          (K.val ∘ genusFieldRootOfPrimeDiscriminant hd K) P := by
      rw [Function.comp_apply, coe_val, coe_genusFieldRootOfPrimeDiscriminant, ← mul_assoc,
        inv_mul_cancel₀ ((map_ne_zero _).mpr (genusFieldRootScale_ne_zero hd P)), one_mul]
    rw [hscale]
    exact mul_mem (inv_mem (IntermediateField.algebraMap_mem _ _)) (subset_adjoin ℚ _ ⟨P, rfl⟩)
  · rintro _ ⟨P, rfl⟩
    rw [Function.comp_apply, coe_val, coe_genusFieldRootOfPrimeDiscriminant]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin ℚ _ ⟨P, rfl⟩)

end TauCeti.Multiquadratic
