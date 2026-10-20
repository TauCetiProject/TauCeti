/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.Data.ZMod.IntUnitsPower
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.NumberTheory.LocalField.QuadraticForm.AnisotropicQuaternary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo

/-!
# Kummer cup products over `ℚ_2`

The dyadic Hilbert-symbol values and the cup-norm comparison show that `(2) ∪ (5)` is
nonzero in `H²(G_{ℚ_2}, 𝔽₂)`. The classification of local quaternion algebras identifies
this cup with `(-1) ∪ (-1)`, since both Hilbert symbols are `-1`.

Every Kummer cup is its Hilbert-symbol logarithm times this nonzero class. In the
square-class basis `-1`, `2`, `5`, this gives the Gram coefficient
`x₀ y₀ + x₁ y₂ + x₂ y₁`, and hence the full `8 × 8` cup table. These formulas turn
second Stiefel–Whitney calculations into arithmetic in `ZMod 2`.

These computations use `TauCeti.cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one`,
`TauCeti.cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq`, and
`TauCeti.BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, for the dyadic Hilbert symbols.
* J.-P. Serre, *Local Fields*, Chapter XIV, §2, for the Kummer cup comparison.
-/

public section

noncomputable section

namespace TauCeti

/-- The cup `(2) ∪ (5)` over `ℚ_2` is nonzero, since `(2,5)_{ℚ_2} = -1`. -/
theorem cup_kummerClass_two_five_ne_zero_padicTwo :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
      (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) ≠ 0 := by
  rw [Ne, cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one,
    hilbertSymbol_two_five_padicTwo]
  norm_num

/-- Over `ℚ_2`, the two nonzero quaternion cups `(2) ∪ (5)` and `(-1) ∪ (-1)` agree. -/
theorem cup_kummerClass_two_five_eq_neg_one_neg_one_padicTwo :
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero))
      (kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))) =
    (trivialF2TopPairing (AbsoluteGaloisGroup ℚ_[2])).cup 1 1
      (kummerClass (-1)) (kummerClass (-1)) := by
  apply (cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq _ _ _ _).2
  exact (BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq _ _ _ _).2
    (hilbertSymbol_two_five_padicTwo.trans hilbertSymbol_neg_one_neg_one_padicTwo.symm)

/-- The Kummer cup over `ℚ₂` is the logarithm of its Hilbert symbol times the nonzero
class `(-1) ∪ (-1)`. The logarithm sends the signs `+1`, `-1` to `0`, `1`. -/
theorem kummerCup_eq_hilbertSymbol_smul_padicTwo (a b : ℚ_[2]ˣ) :
    kummerCup ℚ_[2] (squareClass a) (squareClass b) =
      additiveIntUnitsAddEquiv (Additive.ofMul (hilbertSymbol a b)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  rw [kummerCup_squareClass_squareClass, kummerCup_squareClass_squareClass]
  have hpos : additiveIntUnitsAddEquiv (Additive.ofMul (1 : ℤˣ)) = 0 := by simp
  have hneg : additiveIntUnitsAddEquiv (Additive.ofMul (-1 : ℤˣ)) = 1 := by simp
  rcases Int.units_eq_one_or (hilbertSymbol a b) with hab | hab
  · rw [hab, hpos, zero_smul]
    exact (cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one _ _).2 hab
  · rw [hab, hneg, one_smul]
    exact (cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq _ _ _ _).2
      ((BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq _ _ _ _).2
        (hab.trans hilbertSymbol_neg_one_neg_one_padicTwo.symm))

/-- **The Gram formula for the Kummer cup over `ℚ₂`.** In square-class coordinates along
`-1`, `2`, `5`, the cup is `x₀ y₀ + x₁ y₂ + x₂ y₁` times the nonzero class
`(-1) ∪ (-1)`. The scalar lies in `ZMod 2`. -/
theorem kummerCup_padicTwo (x y : SquareClassGroup ℚ_[2]) :
    kummerCup ℚ_[2] x y =
      (padicTwoSquareClassBasis.repr x 0 * padicTwoSquareClassBasis.repr y 0 +
        padicTwoSquareClassBasis.repr x 1 * padicTwoSquareClassBasis.repr y 2 +
        padicTwoSquareClassBasis.repr x 2 * padicTwoSquareClassBasis.repr y 1) •
      kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  obtain ⟨a, rfl⟩ : ∃ a : ℚ_[2]ˣ, squareClass a = x := ⟨_, squareClass_toMul_out x⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℚ_[2]ˣ, squareClass b = y := ⟨_, squareClass_toMul_out y⟩
  rw [kummerCup_eq_hilbertSymbol_smul_padicTwo,
    ← hilbertSymbolOnSquareClasses_squareClass, hilbertSymbolOnSquareClasses_padicTwo]
  congr 1
  have hlog (t : ZMod 2) :
      additiveIntUnitsAddEquiv (Additive.ofMul ((-1 : ℤˣ) ^ t)) = t := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) t with rfl | rfl <;> simp
  exact hlog _

/-- **The full dyadic Kummer cup table.** The representatives are ordered
`1, -1, 5, -5, 2, -2, 10, -10`. An entry `1` denotes the nonzero class `(-1) ∪ (-1)`;
an entry `0` denotes zero. -/
theorem kummerCup_padicTwoSquareClassRep (i j : Fin 8) :
    kummerCup ℚ_[2] (squareClass (padicTwoSquareClassRep i))
        (squareClass (padicTwoSquareClassRep j)) =
      (!![0, 0, 0, 0, 0, 0, 0, 0;
          0, 1, 0, 1, 0, 1, 0, 1;
          0, 0, 0, 0, 1, 1, 1, 1;
          0, 1, 0, 1, 1, 0, 1, 0;
          0, 0, 1, 1, 0, 0, 1, 1;
          0, 1, 1, 0, 0, 1, 1, 0;
          0, 0, 1, 1, 1, 1, 0, 0;
          0, 1, 1, 0, 1, 0, 0, 1] i j : ZMod 2) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  rw [kummerCup_eq_hilbertSymbol_smul_padicTwo, hilbertSymbol_padicTwoSquareClassRep]
  congr 1
  simp only [additiveIntUnitsAddEquiv_apply, toMul_ofMul]
  fin_cases i <;> fin_cases j <;> norm_num

end TauCeti
