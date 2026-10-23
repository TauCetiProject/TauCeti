/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Class
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Cup.PadicTwo

/-!
# Stiefel–Whitney calculations over `ℚ₂`

The square classes of `-1`, `2`, `5` give coordinates for the first Stiefel–Whitney class.
The second class is a multiple of the nonzero cup `(-1) ∪ (-1)`: its coefficient is the
sum over pairs of the Gram expression `x₀ y₀ + x₁ y₂ + x₂ y₁`, computed in `ZMod 2`.
Thus a diagonalization with unit coefficients computes both classes by finite arithmetic.
The formulas apply in every rank, including zero, and compute the descended invariants
of regular forms through their diagonalizations.

For the representatives `1, -1, 5, -5, 2, -2, 10, -10`, the first-class table records the
eight Kummer classes. The second-class table on the forms `⟨a, a⟩` is
`0, κ, 0, κ, 0, κ, 0, κ`, where `κ = (-1) ∪ (-1) ≠ 0`; on `⟨1, a⟩` it is zero.
The second class of a line is already zero by `TauCeti.sw2_fin_one`.

The calculations reuse `TauCeti.padicTwoSquareClassBasis`,
`TauCeti.hilbertSymbol_padicTwoSquareClassRep`, and `TauCeti.kummerCup_padicTwo`.

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §4.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2 and Chapter IV, §2.
-/

public section

noncomputable section

namespace TauCeti

open Finset

/-- The first Stiefel–Whitney class in the square-class coordinates `-1`, `2`, `5` is
the Kummer image of the sum of the coefficient vectors. -/
theorem sw1_padicTwo {n : ℕ} (w : Fin n → ℚ_[2]ˣ) :
    sw1 w = ∑ j : Fin 3,
      (∑ i, padicTwoSquareClassBasis.repr (squareClass (w i)) j) •
        kummerSquareClassEquiv ℚ_[2] (padicTwoSquareClassBasis j) := by
  rw [sw1_eq_kummerSquareClassEquiv]
  have h := padicTwoSquareClassBasis.sum_repr (squareClass (∏ i, w i))
  rw [← h]
  simp only [map_sum, squareClass_prod, Finsupp.finsetSum_apply]
  congr 1
  funext j
  exact ZMod.map_smul (n := 2) (kummerSquareClassEquiv ℚ_[2]) _ _

/-- **The second Stiefel–Whitney class over `ℚ₂`, in every rank.** Its coefficient
along `(-1) ∪ (-1)` is the sum of the dyadic Gram expression over pairs of coefficients.
All arithmetic in this coefficient takes place in `ZMod 2`. -/
theorem sw2_padicTwo {n : ℕ} (w : Fin n → ℚ_[2]ˣ) :
    sw2 w =
      (∑ i, ∑ j ∈ Ioi i,
        (padicTwoSquareClassBasis.repr (squareClass (w i)) 0 *
            padicTwoSquareClassBasis.repr (squareClass (w j)) 0 +
          padicTwoSquareClassBasis.repr (squareClass (w i)) 1 *
            padicTwoSquareClassBasis.repr (squareClass (w j)) 2 +
          padicTwoSquareClassBasis.repr (squareClass (w i)) 2 *
            padicTwoSquareClassBasis.repr (squareClass (w j)) 1)) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  rw [sw2_def]
  simp only [sum_smul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  exact kummerCup_padicTwo _ _

/-- **The first-class table of the dyadic lines.** In order `1, -1, 5, -5, 2, -2, 10, -10`,
the entries are the sums of the Kummer classes of the generators `-1`, `2`, `5`. -/
theorem sw1_padicTwoSquareClassRep (i : Fin 8) :
    sw1 (fun _ : Fin 1 => padicTwoSquareClassRep i) =
      ![0, kummerClass (-1),
        kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        kummerClass (-1) + kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero),
        kummerClass (-1) + kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero),
        kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero) +
          kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num)),
        kummerClass (-1) + kummerClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero) +
          kummerClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))] i := by
  have hrep : padicTwoSquareClassRep i =
      ![1, -1, Units.mk0 (5 : ℚ_[2]) (by norm_num),
        -1 * Units.mk0 (5 : ℚ_[2]) (by norm_num),
        Units.mk0 (2 : ℚ_[2]) two_ne_zero,
        -1 * Units.mk0 (2 : ℚ_[2]) two_ne_zero,
        Units.mk0 (2 : ℚ_[2]) two_ne_zero * Units.mk0 (5 : ℚ_[2]) (by norm_num),
        -1 * Units.mk0 (2 : ℚ_[2]) two_ne_zero *
          Units.mk0 (5 : ℚ_[2]) (by norm_num)] i := by
    apply Units.ext
    fin_cases i <;> simp <;> norm_num
  rw [sw1_fin_one, hrep]
  fin_cases i <;> simp [← kummerClass_mul]

/-- **The second-class table of the eight repeated-coefficient binary forms** `⟨a, a⟩`.
The nonzero entries occur exactly at `a = -1, -5, -2, -10`. -/
theorem sw2_repeat_padicTwoSquareClassRep (i : Fin 8) :
    sw2 (fun _ : Fin 2 => padicTwoSquareClassRep i) =
      (![0, 1, 0, 1, 0, 1, 0, 1] i : ZMod 2) •
        kummerCup ℚ_[2] (squareClass (-1)) (squareClass (-1)) := by
  rw [sw2_fin_two, ← kummerCup_squareClass_squareClass, kummerCup_padicTwoSquareClassRep]
  congr 1
  revert i
  decide

end TauCeti
