/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.MilnorKTheory.Grading

/-!
# Vanishing of Milnor K-theory of finite fields

Every Steinberg pairing on a finite field `F` vanishes (`IsSteinbergPairing.eq_zero_of_finite`),
hence `MatsumotoGroup F` is trivial (`MatsumotoGroup.instSubsingleton`) and `MilnorK.degree F n`
vanishes for every `n ≥ 2` (`MilnorK.finiteField_vanishing`).

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), Example 1.5.
* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, Example 7.1.1.
-/

public section

namespace TauCeti.MilnorK

universe u

variable {F : Type u} [Field F]

/-- Over a finite field, every degree-two product `ofUnit a * ofUnit b` vanishes in `MilnorK F`. -/
theorem ofUnit_mul_eq_zero_of_finite [Finite F] (a b : Fˣ) : ofUnit a * ofUnit b = 0 :=
  isSteinbergPairing_ofUnit_mul.eq_zero_of_finite a b

/-- Over a finite field, every Milnor symbol of length at least `2` vanishes. -/
theorem symbol_eq_zero_of_finite [Finite F] {l : List Fˣ} (hl : 2 ≤ l.length) : symbol l = 0 := by
  match l, hl with
  | a :: b :: _, _ =>
    rw [symbol_cons, symbol_cons, ← mul_assoc, ofUnit_mul_eq_zero_of_finite a b, zero_mul]

/-- Over a finite field, `MilnorK.degree F n` is the bottom submodule for every `n ≥ 2`. -/
theorem degree_eq_bot_of_finite (F : Type u) [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n) :
    degree F n = ⊥ := by
  rw [eq_bot_iff, degree_le_iff]
  exact fun _ hl => (Submodule.mem_bot ℤ).mpr (symbol_eq_zero_of_finite (hl.symm ▸ hn))

/-- **Milnor K-groups of finite fields vanish in every degree at least two**: `Kₙᴹ(F) = 0` for
every finite field `F` and every `n ≥ 2` (Milnor 1970, Example 1.5; Weibel, III.7.1.1). -/
theorem finiteField_vanishing (F : Type u) [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (MilnorK.degree F n) := by rw [degree_eq_bot_of_finite F n hn]; infer_instance

end TauCeti.MilnorK
