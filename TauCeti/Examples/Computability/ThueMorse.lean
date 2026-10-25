/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Computability.AutomaticSequence
public import Mathlib.Data.ZMod.Basic

/-!
# The two-state Thue–Morse automaton

This supplies the Thue–Morse check of ClassicalArithmeticCompletion §2.33.
The sequence is defined independently as binary digit-sum parity. The explicit automaton
has two states, retains its state on digit zero, and toggles it on digit one.
The output comparison uses the native least-significant-digit-first convention, including
the empty word at zero. The two recurrence formulas also identify the usual Thue–Morse sequence.
-/

public section
namespace TauCeti.Examples

/-- The Thue–Morse sequence is the parity of the sum of the binary digits. -/
def thueMorse (n : ℕ) : ZMod 2 := (Nat.digits 2 n).sum

/-- The two-state automaton retains the parity of the digits read so far. -/
def thueMorseDFAO : DFAO (Fin 2) (ZMod 2) (ZMod 2) where
  step q d := q + d.val
  start := 0
  output := id

private theorem evalFrom_thueMorseDFAO (l : List ℕ) (q : ZMod 2) :
    thueMorseDFAO.evalFrom q (l.map (Fin.ofNat 2)) = q + l.sum := by
  induction l generalizing q with
  | nil => simp only [List.map_nil, DFAO.evalFrom_nil, List.sum_nil, Nat.cast_zero, add_zero]
  | cons d l ih =>
    rw [List.map_cons, DFAO.evalFrom_cons]
    change thueMorseDFAO.evalFrom (q + ((d % 2 : ℕ) : ZMod 2))
      (l.map (Fin.ofNat 2)) = q + (d :: l).sum
    rw [ZMod.natCast_mod, ih, List.sum_cons, Nat.cast_add, add_assoc]

/-- The two-state automaton computes the actual binary digit-sum parity. -/
theorem thueMorseDFAO_output (n : ℕ) :
    thueMorseDFAO.output
      (thueMorseDFAO.eval ((Nat.digits 2 n).map (Fin.ofNat 2))) = thueMorse n := by
  rw [DFAO.eval_eq_evalFrom]
  change thueMorseDFAO.evalFrom 0 ((Nat.digits 2 n).map (Fin.ofNat 2)) =
    ((Nat.digits 2 n).sum : ZMod 2)
  rw [evalFrom_thueMorseDFAO, zero_add]

/-- Thue–Morse is two-automatic, witnessed by the explicit two-state automaton. -/
theorem isAutomatic_thueMorse : IsAutomatic 2 thueMorse := by
  simpa only [thueMorseDFAO_output] using thueMorseDFAO.isAutomatic

/-- The empty binary word gives the initial Thue–Morse value zero. -/
theorem thueMorse_zero : thueMorse 0 = 0 := by
  simp only [thueMorse, Nat.digits_zero, List.sum_nil, Nat.cast_zero]

/-- Appending a zero binary digit leaves the Thue–Morse value unchanged. -/
theorem thueMorse_two_mul (n : ℕ) : thueMorse (2 * n) = thueMorse n := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · rw [mul_zero]
  · simp only [thueMorse, Nat.digits_base_mul (by decide : 1 < 2) hn,
      List.sum_cons, zero_add]

/-- Appending a one binary digit toggles the Thue–Morse value. -/
theorem thueMorse_two_mul_add_one (n : ℕ) :
    thueMorse (2 * n + 1) = 1 + thueMorse n := by
  rw [thueMorse, add_comm (2 * n) 1,
    Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))]
  simp only [List.sum_cons, Nat.cast_add, Nat.cast_one, thueMorse]

end TauCeti.Examples
