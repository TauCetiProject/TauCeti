/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Alexander.Invariance
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Basic

/-!
# Alexander weights for a circle-and-arc Reidemeister clasp

The old crossing coefficients are unchanged by pushing a crossing-free circle across an arc. The
two new crossings have explicit coefficients determined by the directions of the cut arc, the
new circle, and the chosen over-strand. These formulas are the coefficient part of the local
Alexander-module calculation; eliminating the four new generators is the remaining step.
-/

public section
noncomputable section
open LaurentPolynomial

namespace TauCeti.OrientedPDCode
open PDCode

variable {n : ℕ} (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool)

@[simp] theorem alexanderWeight_insertCircleClasp_castSucc_castSucc (i : Fin n) (s : Fin 4) :
    (D.insertCircleClasp p o b).alexanderWeight i.castSucc.castSucc s =
      D.alexanderWeight i s := by
  simp [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply]

/-- The four coefficients at the first new crossing, in slot order. -/
theorem alexanderWeight_insertCircleClasp_castSucc_last (s : Fin 4) :
    (D.insertCircleClasp p o b).alexanderWeight (Fin.last n).castSucc s =
      ![
        if !b then 1 else T (if !D.orientation p then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1),
        if b then 1 else T (if !o then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1),
        if !b then 1 else T (if D.orientation p then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1),
        if b then 1 else T (if o then
          -if (D.orientation p ^^ o) = b then 1 else -1
        else if (D.orientation p ^^ o) = b then 1 else -1)
      ] s := by
  fin_cases s <;>
    simp [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply,
      orientation_insertCircleClasp_first, insertCircleClasp_overPair_castSucc_last]

/-- The four coefficients at the second new crossing, in slot order. -/
theorem alexanderWeight_insertCircleClasp_last (s : Fin 4) :
    (D.insertCircleClasp p o b).alexanderWeight (Fin.last (n + 1)) s =
      ![
        if b then 1 else T (if !o then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1),
        if !b then 1 else T (if !D.orientation p then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1),
        if b then 1 else T (if o then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1),
        if !b then 1 else T (if D.orientation p then
          -(-if (D.orientation p ^^ o) = b then 1 else -1)
        else -if (D.orientation p ^^ o) = b then 1 else -1)
      ] s := by
  fin_cases s <;>
    simp [alexanderWeight_def, PDCode.isOver_def, crossingSign_def, crossing_apply,
      orientation_insertCircleClasp_second, insertCircleClasp_overPair_last] <;>
    cases hD : D.orientation p <;> cases o <;> cases b <;> simp

end TauCeti.OrientedPDCode
