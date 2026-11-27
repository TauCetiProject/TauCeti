/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import TauCeti.RingTheory.MilnorK.Basic
import TauCeti.FieldTheory.MilnorK.SteinbergPairing
import TauCeti.RingTheory.MilnorK.Permutation

/-!
# Field identities and finite-field vanishing for Milnor K-theory

This file complements `TauCeti.RingTheory.MilnorK.Basic` and
`TauCeti.RingTheory.MilnorK.Permutation` by proving additional field-specific identities for
`TauCeti.MilnorK` over fields: characteristic-`2` and 2-torsion identities for `{a, a}` and
symbols with repeated entries, integer-scalar sign rules for commuting symbols, and vanishing in
degrees at least two over finite fields.

## Main results

* `TauCeti.MilnorK.two_nsmul_ofUnit_mul_self`, `TauCeti.MilnorK.ofUnit_mul_self_eq_zero_of_charTwo`,
  `TauCeti.MilnorK.two_nsmul_symbol_append_cons_cons_self`,
  `TauCeti.MilnorK.symbol_append_cons_cons_self_eq_zero_of_charTwo`: 2-torsion and
  characteristic-`2` vanishing for `{a, a}` and consecutive repeated entries.
* `TauCeti.MilnorK.ofUnit_mul_symbol`, `TauCeti.MilnorK.symbol_mul_symbol`: integer-scalar sign
  rules for commuting a degree-one class or a symbol past a symbol.
* `TauCeti.MilnorK.two_nsmul_symbol_ofFn_eq_zero_of_eq` and
  `TauCeti.MilnorK.symbol_ofFn_eq_zero_of_charTwo_of_eq`: repeated-entry torsion and vanishing in
  characteristic `2` for indexed symbols.
* `TauCeti.MilnorK.finiteField_vanishing`: `MilnorK.degree F n` vanishes for finite `F` and
  `2 ≤ n`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.7.1, Example III.7.2(a),
  Example III.7.2(c).
-/

public section

namespace TauCeti

namespace MilnorK

section FieldIdentities

variable {F : Type*} [Field F]

/-- Over a field, `2 • (ofUnit a * ofUnit a) = 0`. -/
theorem two_nsmul_ofUnit_mul_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 :=
  isSteinbergPairing_ofUnit_mul.two_nsmul_map_self a

/-- In characteristic `2`, `ofUnit a * ofUnit a = 0`. -/
theorem ofUnit_mul_self_eq_zero_of_charTwo [CharP F 2] (a : Fˣ) : ofUnit a * ofUnit a = 0 :=
  isSteinbergPairing_ofUnit_mul.map_self_eq_zero_of_charTwo a

/-- A symbol with a consecutive repeated entry is 2-torsion. -/
theorem two_nsmul_symbol_append_cons_cons_self (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    2 • symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [← mul_smul_comm 2 (symbol l₁), ← smul_mul_assoc 2 (ofUnit a * ofUnit a),
    two_nsmul_ofUnit_mul_self a, zero_mul, mul_zero]

/-- In characteristic `2`, any symbol with a consecutive repeated entry vanishes. -/
theorem symbol_append_cons_cons_self_eq_zero_of_charTwo [CharP F 2] (l₁ : List Fˣ) (a : Fˣ)
    (l₂ : List Fˣ) : symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [ofUnit_mul_self_eq_zero_of_charTwo a, zero_mul, mul_zero]

/-- Moving a degree-one class past a length-`n` symbol multiplies by `(-1) ^ n`. -/
theorem ofUnit_mul_symbol (a : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l = ((-1 : ℤ) ^ l.length) • (symbol l * ofUnit a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_comm a b, neg_mul, mul_assoc, ih,
      mul_smul_comm]
    simp only [List.length_cons, pow_succ', mul_smul, neg_smul, one_smul, mul_assoc]

/-- Multiplying two symbols commutes up to `(-1) ^ (l₁.length * l₂.length)`. -/
theorem symbol_mul_symbol (l₁ l₂ : List Fˣ) :
    symbol l₁ * symbol l₂ = ((-1 : ℤ) ^ (l₁.length * l₂.length)) • (symbol l₂ * symbol l₁) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [symbol_cons, mul_assoc, ih, mul_smul_comm, ← mul_assoc, ofUnit_mul_symbol]
    simp only [smul_mul_assoc, smul_smul, mul_assoc, List.length_cons, Nat.add_mul, Nat.one_mul,
      pow_add]

/-- Any symbol with a repeated entry (not necessarily adjacent) is 2-torsion. -/
theorem two_nsmul_symbol_ofFn_eq_zero_of_eq {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) :
    2 • symbol (List.ofFn a) = 0 :=
  two_nsmul_symbol_of_not_nodup (by rw [List.nodup_ofFn]; exact fun hinj ↦ hij (hinj ha))

/-- In characteristic `2`, any symbol with a repeated entry vanishes. -/
theorem symbol_ofFn_eq_zero_of_charTwo_of_eq [CharP F 2] {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) :
    symbol (List.ofFn a) = 0 :=
  symbol_eq_zero_of_not_nodup (by rw [List.nodup_ofFn]; exact fun hinj ↦ hij (hinj ha))

end FieldIdentities

section FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- Over a finite field, every product of two degree-one classes vanishes in `MilnorK F`. -/
theorem ofUnit_mul_ofUnit_eq_zero_of_finite (a b : Fˣ) : ofUnit a * ofUnit b = 0 :=
  isSteinbergPairing_ofUnit_mul.eq_zero_of_finite a b

/-- Over a finite field, every symbol of length at least two vanishes. -/
theorem symbol_eq_zero_of_finite {l : List Fˣ} (hl : 2 ≤ l.length) : symbol l = 0 := by
  match l with
  | a :: b :: rest =>
    rw [symbol_cons, symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_eq_zero_of_finite a b, zero_mul]

/-- Milnor K-groups of finite fields vanish in every degree at least two. -/
theorem finiteField_vanishing (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (degree F n) := by
  refine subsingleton_iff_forall_eq 0 |>.mpr fun x ↦ ?_
  induction x using degree_induction_on with
  | zero => rfl
  | symbol l hl => exact Subtype.ext (symbol_eq_zero_of_finite (hl.symm ▸ hn))
  | add x y hx hy => rw [hx, hy, add_zero]
  | smul k x hx => rw [hx, smul_zero]

end FiniteField

end MilnorK

end TauCeti
