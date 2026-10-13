/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.Basic
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.NumberTheory.LocalField.QuadraticForm.CupPadicTwo
import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
import TauCeti.Algebra.Group.Units.Basic

/-!
# Stiefel–Whitney and Evens values over `ℚ₂(√5)`

For the coefficients `1`, `2 + √5`, `3 + 2√5`, `16 + 7√5` and their negatives,
this file computes the invariants of the twisted trace forms and the Evens norms of
their Kummer classes. Write `κ = (-1) ∪ (-1) ≠ 0` over `ℚ₂`.
The second Stiefel–Whitney values are `κ, 0, κ, 0` on the positive coefficients and
zero on their negatives. The Evens values are `0, κ, 0, κ` and `κ, κ, κ, κ`, respectively.
Thus the two tables differ by the second class `κ` of the untwisted trace form.

The coefficient is supplied as a unit with an identifying equation, so these calculations
apply directly to any construction of the representatives. They do not require a chosen
diagonalization. The first class and corestriction are computed from the norm, and the
second class from Kahn's trace–norm formula and the dyadic Hilbert symbol.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. **78** (1984), Lemme II.2.1 and Théorème 2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2.
-/

public section

noncomputable section

namespace TauCeti.DyadicSqrtFive

open _root_.QuadraticMap

private theorem sqrtFive_not_mem : sqrtFive ∉ Set.range (algebraMap ℚ_[2] DyadicSqrtFive) := by
  rintro ⟨c, hc⟩
  apply Padic.not_isSquare_five
  refine ⟨c, ?_⟩
  apply (algebraMap ℚ_[2] DyadicSqrtFive).injective
  rw [map_mul, hc, ← _root_.sq, sqrtFive_sq, map_ofNat]

private def traceEntry (ε : Fin 2) (i : Fin 4) : ℚ_[2]ˣ :=
  Units.mk0 ((-1) ^ ε.val * ![2, 4, 6, 32] i)
    (by fin_cases ε <;> fin_cases i <;> norm_num)

private def normEntry (i : Fin 4) : ℚ_[2]ˣ :=
  Units.mk0 (![1, -1, -11, 11] i) (by fin_cases i <;> norm_num)

private theorem coefficient_eq (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i) :
    (a : DyadicSqrtFive) =
      algebraMap ℚ_[2] DyadicSqrtFive ((-1) ^ ε.val * ![1, 2, 3, 16] i) +
      algebraMap ℚ_[2] DyadicSqrtFive ((-1) ^ ε.val * ![0, 1, 2, 7] i) * sqrtFive := by
  rw [ha]
  fin_cases ε <;> fin_cases i <;> norm_num [map_ofNat] <;> ring

private theorem trace_eq (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i) :
    Algebra.trace ℚ_[2] DyadicSqrtFive a = traceEntry ε i := by
  rw [coefficient_eq ε i a ha,
    Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul_of_sq_eq
      sqrtFive_not_mem (by simp [map_ofNat] :
        sqrtFive ^ 2 = algebraMap ℚ_[2] DyadicSqrtFive 5)]
  fin_cases ε <;> fin_cases i <;> norm_num [traceEntry]

private theorem norm_eq (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i) :
    Algebra.normUnits ℚ_[2] a = normEntry i := by
  ext
  rw [Algebra.coe_normUnits, coefficient_eq ε i a ha, norm_add_mul_sqrtFive]
  fin_cases ε <;> fin_cases i <;> norm_num [normEntry]

private def traceUnitPart (ε : Fin 2) (i : Fin 4) : ℤ_[2]ˣ :=
  (PadicInt.isUnit_iff.mpr (PadicInt.norm_intCast_eq_one_iff.mpr
    (by fin_cases ε <;> fin_cases i <;> norm_num <;> decide :
      IsCoprime ((-1) ^ ε.val * ![1, 1, 3, 1] i : ℤ) 2))).unit

private def cupUnitPart (i : Fin 4) : ℤ_[2]ˣ :=
  (PadicInt.isUnit_iff.mpr (PadicInt.norm_intCast_eq_one_iff.mpr
    (by fin_cases i <;> norm_num <;> decide : IsCoprime (![-5, 5, 55, -55] i : ℤ) 2))).unit

private theorem cup_trace_norm (ε : Fin 2) (i : Fin 4) :
    kummerCup ℚ_[2] (squareClass (traceEntry ε i))
        (squareClass (-(Units.mk0 (5 : ℚ_[2]) (by norm_num) * normEntry i))) =
      ((if ε = 0 then ![1, 0, 1, 0] i else 0) : ZMod 2) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  rw [kummerCup_eq_hilbertSymbol_smul_padicTwo]
  have ht : (traceEntry ε i : ℚ_[2]) =
      2 ^ (![1, 2, 1, 5] i : ℤ) * ((traceUnitPart ε i : ℤ_[2]) : ℚ_[2]) := by
    simp only [traceEntry, Units.val_mk0, traceUnitPart, IsUnit.unit_spec]
    fin_cases ε <;> fin_cases i <;>
      norm_num [PadicInt.coe_intCast, PadicInt.coe_natCast, map_ofNat] <;> norm_cast
    all_goals
      -- The integer-ring coercion reduces to a subtype projection here.
      erw [PadicInt.coe_natCast 3]
      norm_num
  have hn : (-(Units.mk0 (5 : ℚ_[2]) (by norm_num) * normEntry i) : ℚ_[2]) =
      2 ^ (0 : ℤ) * ((cupUnitPart i : ℤ_[2]) : ℚ_[2]) := by
    simp only [Units.val_mk0, normEntry, cupUnitPart,
      IsUnit.unit_spec]
    fin_cases i <;> norm_num [PadicInt.coe_intCast, PadicInt.coe_natCast, map_ofNat] <;>
      norm_cast
  have het : serreEps (traceUnitPart ε i) =
      (ε.val : ZMod 2) + ![0, 0, 1, 0] i := by
    fin_cases ε <;> fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, zero_add, add_zero, one_add_one_eq_two,
      ZMod.natCast_self]
    all_goals first
      | (apply (serreEps_eq_zero_iff _).2
         norm_num [traceUnitPart, IsUnit.unit_spec, map_ofNat] <;> decide)
      | (apply (serreEps_eq_one_iff _).2
         norm_num [traceUnitPart, IsUnit.unit_spec, map_ofNat] <;> decide)
  have hen : serreEps (cupUnitPart i) = (![1, 0, 1, 0] i : ZMod 2) := by
    fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
    all_goals first
      | (apply (serreEps_eq_zero_iff _).2
         norm_num [cupUnitPart, IsUnit.unit_spec, map_ofNat]
         all_goals decide)
      | (apply (serreEps_eq_one_iff _).2
         norm_num [cupUnitPart, IsUnit.unit_spec, map_ofNat]
         all_goals decide)
  have hon : serreOmega (cupUnitPart i) = (![1, 1, 0, 0] i : ZMod 2) := by
    fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
    all_goals first
      | (apply (serreOmega_eq_zero_iff _).2
         norm_num [cupUnitPart, IsUnit.unit_spec, map_ofNat]
         all_goals decide)
      | (apply (serreOmega_eq_one_iff _).2
         norm_num [cupUnitPart, IsUnit.unit_spec, map_ofNat]
         all_goals decide)
  rw [hilbertSymbol_padicTwo ht hn, het, hen, hon]
  congr 1
  fin_cases ε <;> fin_cases i <;> norm_num [additiveIntUnitsAddEquiv_apply] <;> decide

private theorem normEntry_squareClass (i : Fin 4) :
    squareClass (normEntry i) =
      squareClass (padicTwoSquareClassRep (![0, 1, 2, 3] i)) := by
  have hu : IsUnit (-55 : ℤ_[2]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_intCast_eq_one_iff.mpr (by norm_num; decide))
  have hs : IsSquare (-55 : ℚ_[2]) := by
    have h := (isSquare_coe_iff_mem_unitsPrincipal_three hu.unit).2 (by
      rw [mem_unitsPrincipal_iff_toZModPow, IsUnit.unit_spec]
      norm_num [map_ofNat]; decide)
    rw [IsUnit.unit_spec] at h
    convert h using 1
    norm_cast
  rw [squareClass_eq_iff_isSquare_mul, ← isSquare_units_val_iff]
  fin_cases i <;> norm_num [normEntry] <;> exact hs

private theorem kummerClass_normEntry (i : Fin 4) :
    kummerClass (normEntry i) =
      ![0, kummerClass (-1), kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        kummerClass (-1) + kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))] i := by
  rw [← kummerSquareClassEquiv_squareClass, normEntry_squareClass,
    kummerSquareClassEquiv_squareClass]
  have hrep : padicTwoSquareClassRep (![0, 1, 2, 3] i) =
      ![1, -1, Units.mk0 (5 : ℚ_[2]) (by norm_num),
        -1 * Units.mk0 (5 : ℚ_[2]) (by norm_num)] i := by
    ext
    fin_cases i <;> norm_num
  rw [hrep]
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ',
    kummerClass_mul, kummerClass_one]

/-- **Corestriction on the eight signed coefficients.** The norms are `1`, `-1`, `-11`, `11`
for either sign, whose square classes are `1`, `-1`, `5`, `-5` over `ℚ₂`. -/
theorem galoisCor_kummerClass_table
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2])
    (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i) :
    galoisCor ℚ_[2] DyadicSqrtFive σ 1 (kummerClass a) =
      ![0, kummerClass (-1), kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        kummerClass (-1) + kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))] i := by
  rw [galoisCor_kummerClass, norm_eq ε i a ha, kummerClass_normEntry]

/-- **The first Stiefel–Whitney table of the twisted trace forms.** For either sign, the
classes are `(5)`, `(-1) + (5)`, `0`, `(-1)`, in the order of the displayed coefficients. -/
theorem sw1Class_traceTransfer_table (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i)
    (hQ : (((a : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    sw1Class (formClass _ hQ) =
      ![kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        kummerClass (-1) + kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        0, kummerClass (-1)] i := by
  let σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] := IsSepClosed.lift
  have h1 : ((sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate :=
    (QuadraticMap.sq.nondegenerate_traceTransfer_iff).2 (by
      simpa using (QuadraticMap.nondegenerate_smul_sq (one_ne_zero : (1 : DyadicSqrtFive) ≠ 0)))
  rw [sw1Class_formClass_traceTransfer_smul_sq σ a hQ h1,
    sw1Class_formClass_traceTransfer_sq_of_sq
      (d := Units.mk0 (5 : ℚ_[2]) (by norm_num)) finrank_eq_two sqrtFive_not_mem
      (by simp [map_ofNat]) h1, galoisCor_kummerClass_table σ ε i a ha]
  have h5 : 2 • kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)) = 0 :=
    cohomF2.two_nsmul_eq_zero _ _ _
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', add_zero] <;>
    abel_nf at h5 ⊢ <;> simp only [h5, zero_add]

/-- **The second Stiefel–Whitney table of the twisted trace forms.** The positive rows
have coefficients `1, 0, 1, 0` along `κ = (-1) ∪ (-1)`; every negative row is zero. -/
theorem sw2Class_traceTransfer_table (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i)
    (hQ : (((a : DyadicSqrtFive) • sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate) :
    sw2Class (formClass _ hQ) =
      ((if ε = 0 then ![1, 0, 1, 0] i else 0) : ZMod 2) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  rw [sw2Class_formClass_traceTransfer_smul_sq_of_sq
    (d := Units.mk0 (5 : ℚ_[2]) (by norm_num)) finrank_eq_two sqrtFive_not_mem
    (by simp [map_ofNat]) a (t := traceEntry ε i) (trace_eq ε i a ha).symm hQ,
    norm_eq ε i a ha, ← kummerCup_squareClass_squareClass, cup_trace_norm]

/-- **The Evens-norm table on the eight signed coefficients.** Along every embedding,
the positive coefficients have values `0, κ, 0, κ` and all four negative coefficients have
value `κ`, where `κ = (-1) ∪ (-1)` is the nonzero dyadic cup class. -/
theorem galoisEvens_kummerClass_table
    (σ : DyadicSqrtFive →ₐ[ℚ_[2]] SeparableClosure ℚ_[2])
    (ε : Fin 2) (i : Fin 4) (a : DyadicSqrtFiveˣ)
    (ha : (a : DyadicSqrtFive) = (-1) ^ ε.val *
      ![1, 2 + sqrtFive, 3 + 2 * sqrtFive, 16 + 7 * sqrtFive] i) :
    galoisEvens ℚ_[2] DyadicSqrtFive σ finrank_eq_two (kummerClass a) =
      ((if ε = 0 then ![0, 1, 0, 1] i else 1) : ZMod 2) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  let : Invertible (2 : DyadicSqrtFive) := invertibleOfNonzero (by norm_num)
  have hQ : (((a : DyadicSqrtFive) • QuadraticMap.sq
      (R := DyadicSqrtFive) (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate :=
    (nondegenerate_traceTransfer_iff _).2 (nondegenerate_smul_sq a.ne_zero)
  have h1 : ((QuadraticMap.sq (R := DyadicSqrtFive)
      (A := DyadicSqrtFive)).traceTransfer ℚ_[2]).Nondegenerate :=
    (nondegenerate_traceTransfer_iff _).2 (by
      simpa using (nondegenerate_smul_sq (one_ne_zero : (1 : DyadicSqrtFive) ≠ 0)))
  have hr := sw2Class_formClass_traceTransfer_smul_sq σ finrank_eq_two a hQ h1
  rw [cup_sw1Class_formClass_traceTransfer_sq_galoisCor_eq_zero σ finrank_eq_two
      (d := Units.mk0 (5 : ℚ_[2]) (by norm_num)) sqrtFive_not_mem (by simp [map_ofNat]) h1,
    add_zero, sw2Class_formClass_traceTransfer_sq_of_sq
      (d := Units.mk0 (5 : ℚ_[2]) (by norm_num)) finrank_eq_two sqrtFive_not_mem
      (by simp [map_ofNat]) h1, sw2Class_traceTransfer_table ε i a ha hQ] at hr
  have h2 : unitOfInvertible (2 : ℚ_[2]) = Units.mk0 2 two_ne_zero := by ext; simp
  rw [h2, cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo,
    ← kummerCup_squareClass_squareClass] at hr
  apply add_left_cancel (a := kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)))
  rw [← hr]
  conv_rhs => lhs; rw [← one_smul (ZMod 2)
    (kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)))]
  rw [← add_smul]
  congr 1
  fin_cases ε <;> fin_cases i <;> decide

end TauCeti.DyadicSqrtFive
