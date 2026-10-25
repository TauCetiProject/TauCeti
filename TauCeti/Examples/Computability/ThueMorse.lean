/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Computability.AutomaticSequence

/-!
# The two-state Thue–Morse automaton

This demonstrates binary automaticity of digit-sum parity with a two-state automaton.
The sequence is defined independently as binary digit-sum parity. The automaton
has two states, retains its state on digit zero, and toggles it on digit one.
The output comparison uses the native least-significant-digit-first convention, including
the empty word at zero. The two recurrence formulas also identify the usual Thue–Morse sequence.
-/

public section
namespace TauCeti.Examples

/-- The Thue–Morse sequence is the parity of the sum of the binary digits. -/
def thueMorse (n : ℕ) : ZMod 2 := (Nat.digits 2 n).sum

/-- Express Thue–Morse as the parity of the binary digit sum. -/
theorem thueMorse_def (n : ℕ) : thueMorse n = (Nat.digits 2 n).sum := by
  simp only [thueMorse]

/-- The two-state automaton computes the actual binary digit-sum parity. -/
theorem parityDFAO_output_thueMorse (n : ℕ) :
    parityDFAO.output
      (parityDFAO.eval ((Nat.digits 2 n).map (Fin.ofNat 2))) = thueMorse n := by
  simp only [DFAO.eval_eq_evalFrom, parityDFAO_start, parityDFAO_output,
    evalFrom_parityDFAO, zero_add, thueMorse_def]

/-- Thue–Morse is two-automatic, witnessed by the explicit two-state automaton. -/
theorem isAutomatic_thueMorse : IsAutomatic 2 thueMorse := by
  simpa only [parityDFAO_output_thueMorse] using parityDFAO.isAutomatic

/-- The empty binary word gives the initial Thue–Morse value zero. -/
@[simp]
theorem thueMorse_zero : thueMorse 0 = 0 := by
  simp only [thueMorse, Nat.digits_zero, List.sum_nil, Nat.cast_zero]

/-- Appending a zero binary digit leaves the Thue–Morse value unchanged. -/
@[simp]
theorem thueMorse_two_mul (n : ℕ) : thueMorse (2 * n) = thueMorse n := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · rw [mul_zero]
  · simp only [thueMorse, Nat.digits_base_mul (by decide : 1 < 2) hn,
      List.sum_cons, zero_add]

/-- Appending a one binary digit toggles the Thue–Morse value. -/
@[simp]
theorem thueMorse_two_mul_add_one (n : ℕ) :
    thueMorse (2 * n + 1) = 1 + thueMorse n := by
  rw [thueMorse, add_comm (2 * n) 1,
    Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))]
  simp only [List.sum_cons, Nat.cast_add, Nat.cast_one, thueMorse]

end TauCeti.Examples
