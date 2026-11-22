/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower
public import TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values
import TauCeti.NumberTheory.NumberField.Global.RayClass.ImaginaryQuadratic
import TauCeti.NumberTheory.NumberField.Quadratic.Units

/-!
# Ray class field degrees for imaginary quadratic fields

Let `K` be an imaginary quadratic field (`[IsTotallyComplex K]`, `finrank ℚ K = 2`) of discriminant
`D = NumberField.discr K`, and let `Modulus.spanNat K N` denote the purely finite modulus `(N)` for
`N ≠ 0`. Combining the relative ray-class reciprocity of
`TauCeti.NumberTheory.ClassFieldTheory.ClassFields.Tower`, the unit-congruence indices of
`TauCeti.NumberTheory.NumberField.Global.RayClass.ImaginaryQuadratic`, and the residue-unit
counts of `TauCeti.NumberTheory.NumberField.Quadratic.ResidueUnits` yields the closed ray class
field degree dictionary over `hilbertClassField K` (for the multiplication-matrix Galois actions,
see `TauCeti.NumberTheory.ClassFieldTheory.ClassFields.MatrixReciprocity`):

* `[K_(N) : H_K] * #(𝓞 K)ˣ = #(𝓞 K ⧸ (N))ˣ` for every `3 ≤ N`
  (`finrank_hilbertClassField_rayClassField_spanNat_mul_card_units`).
* Closed values of `[K_(N) : H_K]` at levels `2`, `3`, `6`, and `8` for all imaginary quadratic
  fields — including `D = -4` and `D = -3`, where `[K_(2) : H_K] = 1` despite
  `#(𝓞 K ⧸ (2))ˣ > 1`.
* Unconditional relative tower degrees `[K_(6) : K_(2)] = (3 - χ_D(3)).toNat` and
  `[K_(8) : K_(2)] = 8`, valid uniformly for every imaginary quadratic discriminant `D`, together
  with the mod-`24` criterion `fundamentalDiscriminantChar_two_eq_neg_one_and_three_eq_zero_iff`
  characterizing the inert-two, ramified-three branch `D ≡ 21 (mod 24)`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §§9, 11.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1, 6.
-/

public noncomputable section

open IsDedekindDomain Module NumberField TauCeti.GlobalNumberFields TauCeti.NumberField
open scoped NumberField nonZeroDivisors
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr
  fundamentalDiscriminantChar_le_one fundamentalDiscriminantChar_neg_four_two
  fundamentalDiscriminantChar_neg_four_three fundamentalDiscriminantChar_neg_three_two
  fundamentalDiscriminantChar_neg_three_three)

namespace TauCeti.Multiquadratic

/-- The fundamental-discriminant character satisfies `χ_D(2) = -1` and `χ_D(3) = 0` iff
`D ≡ 21 (mod 24)` (the inert-two, ramified-three CM branch). -/
theorem fundamentalDiscriminantChar_two_eq_neg_one_and_three_eq_zero_iff {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) :
    fundamentalDiscriminantChar D hD 2 = -1 ∧ fundamentalDiscriminantChar D hD 3 = 0 ↔
      D % 24 = 21 := by
  have h2 := fundamentalDiscriminantChar_two_eq_neg_one_iff hD
  have h3 : fundamentalDiscriminantChar D hD 3 = 0 ↔ D % 3 = 0 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := fundamentalDiscriminantChar_natCast_eq_legendreSym hD (q := 3) (by decide)
    rw [show ((3 : ℕ) : ℤ) = 3 by rfl, Int.cast_ofNat] at h
    rw [h, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    norm_cast
  rw [h2, h3]
  omega

end TauCeti.Multiquadratic

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-! ### Ray class field degrees for imaginary quadratic fields -/

section Degrees

variable [IsTotallyComplex K]

/-- **General relative degree relation at level `N ≥ 3` for imaginary quadratic fields**:
`[K_(N) : H_K] * #(𝓞 K)ˣ = #(𝓞 K ⧸ (N))ˣ`, with `#(𝓞 K)ˣ` given by
`TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr`. -/
theorem finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    (hK : finrank ℚ K = 2) {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K N)) *
        Nat.card (𝓞 K)ˣ =
      Nat.card (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ := by
  have hrel := finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
    (Modulus.spanNat_infinitePart (K := K) N)
  rw [Modulus.spanNat_finitePart, index_unitsCongruenceSubgroup_spanNat_of_three_le hK hN,
    ← TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at hrel
  exact hrel

/-- Integer-cast form of `finrank_hilbertClassField_rayClassField_spanNat_mul_card_units` with
`#(𝓞 K)ˣ` evaluated by discriminant. -/
private theorem intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    (hK : finrank ℚ K = 2) {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K N))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K N))] :
    (Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K N)) : ℤ) *
        (if discr K = -4 then 4 else if discr K = -3 then 6 else 2) =
      (Nat.card (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ : ℤ) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_spanNat_mul_card_units hK hN
  rw [Nat.cast_mul, TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr hK] at h
  simpa using h

omit [IsTotallyComplex K] in
/-- Case split on `discr K ∈ {-4, -3}` together with the values of `χ_D(2)` and `χ_D(3)`
(and the uniform bound `χ_D(2), χ_D(3) ≤ 1` away from `-4` and `-3`). -/
private theorem discr_cases_char_two_three (hK : finrank ℚ K = 2) :
    (discr K = -4 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 = 0 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3 = -1) ∨
    (discr K = -3 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 = -1 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3 = 0) ∨
    (discr K ≠ -4 ∧ discr K ≠ -3 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2 ≤ 1 ∧
      fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3 ≤ 1) := by
  generalize hD : isFundamentalDiscr_discr hK = hD'
  clear hD
  generalize discr K = D at hD' ⊢
  rcases eq_or_ne D (-4) with rfl | h4
  · exact Or.inl ⟨rfl, fundamentalDiscriminantChar_neg_four_two hD',
      fundamentalDiscriminantChar_neg_four_three hD'⟩
  rcases eq_or_ne D (-3) with rfl | h3
  · exact Or.inr (Or.inl ⟨rfl, fundamentalDiscriminantChar_neg_three_two hD',
      fundamentalDiscriminantChar_neg_three_three hD'⟩)
  · exact Or.inr (Or.inr ⟨h4, h3, fundamentalDiscriminantChar_le_one hD' 2,
      fundamentalDiscriminantChar_le_one hD' 3⟩)

/-- **Degree of `K_(2)` over the Hilbert class field**: `1` at `D = -4` and `D = -3` (where the
fourth or sixth roots of unity surject onto `(𝓞 K ⧸ (2))ˣ`), and `(2 - χ_D(2)).toNat` (`1`, `2`,
or `3` according as `2` splits, ramifies, or is inert) for `D < -4`. -/
theorem finrank_hilbertClassField_rayClassField_two (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) =
      if discr K = -4 ∨ discr K = -3 then 1
      else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat := by
  have hrel := congrArg (Nat.cast : ℕ → ℤ) <|
    finrank_hilbertClassField_rayClassField_mul_index_of_infinitePart_eq_empty
      (Modulus.spanNat_infinitePart (K := K) 2)
  rw [Nat.cast_mul, Modulus.spanNat_finitePart, Nat.cast_ofNat, card_units_quotient_span_two hK,
    index_unitsCongruenceSubgroup_spanNat_two hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, hc2, _⟩ | ⟨hD, hc2, _⟩ | ⟨h4, h3, _, _⟩
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [h4, h3] at hrel ⊢; omega

/-- Specialization of `finrank_hilbertClassField_rayClassField_two` to `discr K < -4`. -/
theorem finrank_hilbertClassField_rayClassField_two_of_discr_lt_neg_four (hK : finrank ℚ K = 2)
    (hd : discr K < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) =
      (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat := by
  have hnot : ¬(discr K = -4 ∨ discr K = -3) := by omega
  simp [finrank_hilbertClassField_rayClassField_two hK, hnot]

/-- **Degree of `K_(3)` over the Hilbert class field**: `2` at `D = -4`, `1` at `D = -3`, and
`(3 - χ_D(3)).toNat` (`2`, `3`, or `4` according as `3` splits, ramifies, or is inert) for
`D < -4`. -/
theorem finrank_hilbertClassField_rayClassField_three (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) =
      if discr K = -4 then 2 else if discr K = -3 then 1
      else (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have hrel := intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units hK (le_refl 3)
  rw [Nat.cast_ofNat, card_units_quotient_span_three hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, _, hc3⟩ | ⟨hD, _, hc3⟩ | ⟨h4, h3, _, _⟩
  · simp [hD, hc3] at hrel ⊢; omega
  · simp [hD, hc3] at hrel ⊢; omega
  · simp [h4, h3] at hrel ⊢; omega

/-- Specialization of `finrank_hilbertClassField_rayClassField_three` to `discr K < -4`. -/
theorem finrank_hilbertClassField_rayClassField_three_of_discr_lt_neg_four (hK : finrank ℚ K = 2)
    (hd : discr K < -4)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 3))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 3)) =
      (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  simp [finrank_hilbertClassField_rayClassField_three hK, show discr K ≠ -4 by omega,
    show discr K ≠ -3 by omega]

/-- **Degree of `K_(6)` over the Hilbert class field** for all imaginary quadratic fields. -/
theorem finrank_hilbertClassField_rayClassField_six (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 6))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 6))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) =
      (if discr K = -4 ∨ discr K = -3 then 1
        else (2 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 2).toNat) *
        (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  have hrel := intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    hK (N := 6) (by decide)
  rw [Nat.cast_ofNat, card_units_quotient_span_six hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, hc2, hc3⟩ | ⟨hD, hc2, hc3⟩ | ⟨h4, h3, hc2, hc3⟩
  · simp [hD, hc2, hc3] at hrel ⊢; omega
  · simp [hD, hc2, hc3] at hrel ⊢; omega
  · simp only [h4, h3, or_self, ↓reduceIte] at hrel ⊢
    rw [← Int.toNat_mul (by omega) (by omega)]
    exact Nat.cast_injective (R := ℤ) (by rw [Int.toNat_of_nonneg (by nlinarith)]; linarith)

/-- **Degree of `K_(8)` over the Hilbert class field** for all imaginary quadratic fields. -/
theorem finrank_hilbertClassField_rayClassField_eight (hK : finrank ℚ K = 2)
    [Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 8))]
    [IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 8))] :
    Module.finrank (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) =
      8 * (if discr K = -4 ∨ discr K = -3 then 1
        else (2 - fundamentalDiscriminantChar (discr K)
          (isFundamentalDiscr_discr hK) 2).toNat) := by
  have hrel := intCast_finrank_hilbertClassField_rayClassField_spanNat_mul_card_units
    hK (N := 8) (by decide)
  rw [Nat.cast_ofNat, card_units_quotient_span_eight hK] at hrel
  rcases discr_cases_char_two_three hK with ⟨hD, hc2, _⟩ | ⟨hD, hc2, _⟩ | ⟨h4, h3, _, _⟩
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [hD, hc2] at hrel ⊢; omega
  · simp [h4, h3] at hrel ⊢; omega

/-- **Unconditional relative degree `[K_(6) : K_(2)] = 3 - χ_D(3)`** for every imaginary quadratic
field `K` (including `D = -4` and `D = -3`, since the unit congruence subgroup shrinks from `{±1}`
to `{1}` between levels `2` and `6`). -/
theorem finrank_rayClassField_two_rayClassField_six (hK : finrank ℚ K = 2)
    [Algebra (rayClassField (Modulus.spanNat K 2)) (rayClassField (Modulus.spanNat K 6))]
    [IsScalarTower K (rayClassField (Modulus.spanNat K 2))
      (rayClassField (Modulus.spanNat K 6))] :
    Module.finrank (rayClassField (Modulus.spanNat K 2))
        (rayClassField (Modulus.spanNat K 6)) =
      (3 - fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) 3).toNat := by
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 2))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 6))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 6)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hmul := finrank_hilbertClassField_mul_finrank_rayClassField
    (Modulus.spanNat K 2) (Modulus.spanNat K 6)
  rw [finrank_hilbertClassField_rayClassField_two hK,
    finrank_hilbertClassField_rayClassField_six hK] at hmul
  refine Nat.mul_left_cancel ?_ hmul
  split_ifs
  · omega
  · have := fundamentalDiscriminantChar_le_one (isFundamentalDiscr_discr hK) 2; omega

/-- **Unconditional relative degree `[K_(8) : K_(2)] = 8`** for every imaginary quadratic field `K`
(including `D = -4` and `D = -3`). -/
theorem finrank_rayClassField_two_rayClassField_eight (hK : finrank ℚ K = 2)
    [Algebra (rayClassField (Modulus.spanNat K 2)) (rayClassField (Modulus.spanNat K 8))]
    [IsScalarTower K (rayClassField (Modulus.spanNat K 2))
      (rayClassField (Modulus.spanNat K 8))] :
    Module.finrank (rayClassField (Modulus.spanNat K 2))
        (rayClassField (Modulus.spanNat K 8)) = 8 := by
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 2))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 2)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) :=
    (IntermediateField.inclusion
      (hilbertClassField_le_rayClassField (Modulus.spanNat K 8))).toAlgebra
  have : IsScalarTower K (hilbertClassField K) (rayClassField (Modulus.spanNat K 8)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hmul := finrank_hilbertClassField_mul_finrank_rayClassField
    (Modulus.spanNat K 2) (Modulus.spanNat K 8)
  rw [finrank_hilbertClassField_rayClassField_two hK,
    finrank_hilbertClassField_rayClassField_eight hK] at hmul
  refine Nat.mul_left_cancel ?_ (hmul.trans (mul_comm 8 _))
  split_ifs
  · omega
  · have := fundamentalDiscriminantChar_le_one (isFundamentalDiscr_discr hK) 2; omega

end Degrees

end TauCeti.ClassFieldTheory
