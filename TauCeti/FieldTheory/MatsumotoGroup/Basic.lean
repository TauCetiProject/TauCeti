/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.MilnorK.SteinbergPairing
public import TauCeti.RingTheory.MilnorK.MatsumotoGroup

/-!
# Matsumoto's presentation of `K₂` of a field

For a field `F`, this file develops the field-specific identities and finite-field vanishing of the
**Matsumoto group** `TauCeti.MatsumotoGroup F` (defined over commutative semirings in
`TauCeti.RingTheory.MilnorK.MatsumotoGroup`):

* `{x, -x} = 0`, antisymmetry `{x, y} + {y, x} = 0`, and `{x, x} = {x, -1}`, so `{x, x}` has order
  dividing two;
* **every symbol vanishes over a finite field**, so `MatsumotoGroup F` is trivial for finite `F`.

Through Matsumoto's theorem the last statement is Steinberg's computation `K₂(𝔽_q) = 0`.

## Main results

* `TauCeti.MatsumotoGroup.symbol_self_neg`: `{x, -x} = 0` over a field.
* `TauCeti.MatsumotoGroup.symbol_add_symbol_swap`: `{x, y} + {y, x} = 0` over a field.
* `TauCeti.MatsumotoGroup.symbol_self`: `{x, x} = {x, -1}` over a field.
* `TauCeti.MatsumotoGroup.symbol_eq_zero_of_finite`: over a finite field every symbol is zero,
  so the Matsumoto group is trivial.

## References

* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*,
  Ann. Sci. École Norm. Sup. (4) 2 (1969).
* J. Milnor, *Introduction to Algebraic K-Theory*, §§9 and 11.
* C. Weibel, *The K-book*, Chapter III, Theorem 6.1 and Corollary 6.1.1.
-/

public section

namespace TauCeti

namespace MatsumotoGroup

section Field

variable {F : Type*} [Field F]

/-- **The Steinberg relation.** `{x, 1 - x} = 0` for `x ≠ 1`. -/
theorem symbol_mk0_one_sub (x : Fˣ) (hx : (1 : F) - x ≠ 0) :
    symbol x (Units.mk0 (1 - x) hx) = 0 :=
  symbol_of_add_eq_one (by simp)

/-- `{x, -x} = 0` for every unit `x`. -/
@[simp]
theorem symbol_self_neg (x : Fˣ) : symbol x (-x) = 0 :=
  isSteinbergPairing_symbol.map_neg_self x

/-- **Antisymmetry of Steinberg symbols.** `{y, x} = -{x, y}`. -/
theorem symbol_swap (x y : Fˣ) : symbol y x = -symbol x y :=
  isSteinbergPairing_symbol.map_anticomm y x

/-- **Antisymmetry of Steinberg symbols.** `{x, y} + {y, x} = 0`. -/
theorem symbol_add_symbol_swap (x y : Fˣ) : symbol x y + symbol y x = 0 := by
  rw [symbol_swap x y, add_neg_cancel]

/-- `{x, x} = {x, -1}`. -/
theorem symbol_self (x : Fˣ) : symbol x x = symbol x (-1) :=
  isSteinbergPairing_symbol.map_self x

/-- The symbol `{x, x}` has order dividing two. -/
theorem two_nsmul_symbol_self (x : Fˣ) : 2 • symbol x x = 0 :=
  isSteinbergPairing_symbol.two_nsmul_map_self x

/-- **Steinberg symbols vanish over a finite field.** Through Matsumoto's theorem this is
`K₂(𝔽_q) = 0`. -/
theorem symbol_eq_zero_of_finite [Finite F] (x y : Fˣ) : symbol x y = 0 :=
  isSteinbergPairing_symbol.eq_zero_of_finite x y

/-- The Matsumoto group of a finite field is trivial. -/
instance [Finite F] : Subsingleton (MatsumotoGroup F) :=
  subsingleton_of_forall_eq 0 fun q ↦ by
    induction q using induction_on with
    | symbol x y => exact symbol_eq_zero_of_finite x y
    | add a b ha hb => rw [ha, hb, add_zero]

end Field

end MatsumotoGroup

end TauCeti
