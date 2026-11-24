/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.RingTheory.MilnorK.Basic
import TauCeti.Data.List.OfFn
import TauCeti.FieldTheory.MilnorK.SteinbergPairing

/-!
# Field identities and finite-field vanishing for Milnor K-theory

This file complements `TauCeti.RingTheory.MilnorK.Basic` by proving field-specific sign,
graded-commutativity, and permutation-sign rules for `TauCeti.MilnorK` over fields, repeated-entry
torsion and characteristic-`2` vanishing, and vanishing in degrees at least two over finite fields.

## Main results

* `TauCeti.MilnorK.ofUnit_mul_ofUnit_neg_self`, `TauCeti.MilnorK.ofUnit_mul_ofUnit_comm`,
  `TauCeti.MilnorK.ofUnit_mul_ofUnit_self`, `TauCeti.MilnorK.symbol_append_cons_cons_swap`:
  `{a, -a} = 0`, `{a, b} = -{b, a}`, `{a, a} = {a, -1}`, and swapping adjacent entries negates a
  symbol.
* `TauCeti.MilnorK.mul_comm_of_mem_degree`: graded commutativity over a field.
* `TauCeti.MilnorK.symbol_ofFn_comp_swap`: transposing two symbol entries negates the symbol.
* `TauCeti.MilnorK.symbol_ofFn_comp_perm`: permuting symbol entries multiplies by the sign.
* `TauCeti.MilnorK.two_nsmul_symbol_ofFn_eq_zero_of_eq` and
  `TauCeti.MilnorK.symbol_ofFn_eq_zero_of_charTwo_of_eq`: repeated-entry torsion and vanishing in
  characteristic `2`.
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

/-- Over a field, `{a, -a} = 0` for every unit `a`. -/
@[simp]
theorem ofUnit_mul_ofUnit_neg_self (a : Fˣ) : ofUnit a * ofUnit (-a) = 0 :=
  isSteinbergPairing_ofUnit_mul.map_neg_self a

/-- Over a field, the degree-one classes anticommute: `{a, b} = -{b, a}`. -/
theorem ofUnit_mul_ofUnit_comm (a b : Fˣ) : ofUnit a * ofUnit b = -(ofUnit b * ofUnit a) :=
  isSteinbergPairing_ofUnit_mul.map_anticomm a b

/-- Over a field, `{a, a} = {a, -1}`. Unlike in an exterior algebra, this class need not vanish:
`{-1, -1} ≠ 0` over `ℝ` (Weibel, Example III.7.2(c)). -/
theorem ofUnit_mul_ofUnit_self (a : Fˣ) : ofUnit a * ofUnit a = ofUnit a * ofUnit (-1) :=
  isSteinbergPairing_ofUnit_mul.map_self a

/-- Over a field, interchanging two neighbouring entries negates a Milnor symbol. -/
theorem symbol_append_cons_cons_swap (l₁ l₂ : List Fˣ) (a b : Fˣ) :
    symbol (l₁ ++ b :: a :: l₂) = -symbol (l₁ ++ a :: b :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_comm b a, neg_mul,
    mul_neg]

/-- Over a field, `2 • (ofUnit a * ofUnit a) = 0`. -/
theorem two_nsmul_ofUnit_mul_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 :=
  isSteinbergPairing_ofUnit_mul.two_nsmul_map_self a

/-- In characteristic `2`, `ofUnit a * ofUnit a = 0`. -/
theorem ofUnit_mul_self_eq_zero_of_charTwo [CharP F 2] (a : Fˣ) : ofUnit a * ofUnit a = 0 :=
  isSteinbergPairing_ofUnit_mul.map_self_eq_zero_of_charTwo a

/-- A consecutive repeated entry `a, a` may be replaced by `a, -1`. -/
theorem symbol_repeat_adjacent (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = symbol (l₁ ++ a :: (-1 : Fˣ) :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [ofUnit_mul_ofUnit_self a]

/-- A symbol with a consecutive repeated entry is 2-torsion. -/
theorem two_nsmul_symbol_repeat_adjacent (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    2 • symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [← mul_smul_comm 2 (symbol l₁), ← smul_mul_assoc 2 (ofUnit a * ofUnit a),
    two_nsmul_ofUnit_mul_self a, zero_mul, mul_zero]

/-- In characteristic `2`, any symbol with a consecutive repeated entry vanishes. -/
theorem symbol_repeat_adjacent_eq_zero_of_charTwo [CharP F 2] (l₁ : List Fˣ) (a : Fˣ)
    (l₂ : List Fˣ) : symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [ofUnit_mul_self_eq_zero_of_charTwo a, zero_mul, mul_zero]

/-- Moving a degree-one class past a length-`n` symbol multiplies by `(-1) ^ n`. -/
theorem ofUnit_mul_symbol (a : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l = ((-1 : ℤ) ^ l.length) • (symbol l * ofUnit a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_comm a b, neg_mul (ofUnit b * ofUnit a),
      mul_assoc, ih, mul_smul_comm, ← neg_smul, ← neg_one_mul, ← pow_succ', List.length_cons,
      mul_assoc]

/-- Multiplying two symbols commutes up to `(-1) ^ (l₁.length * l₂.length)`. -/
theorem symbol_mul_symbol (l₁ l₂ : List Fˣ) :
    symbol l₁ * symbol l₂ = ((-1 : ℤ) ^ (l₁.length * l₂.length)) • (symbol l₂ * symbol l₁) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [symbol_cons, mul_assoc, ih, mul_smul_comm, ← mul_assoc, ofUnit_mul_symbol]
    simp only [smul_mul_assoc, smul_smul, mul_assoc, List.length_cons, Nat.add_mul, Nat.one_mul,
      pow_add]

/-- Graded commutativity of `MilnorK F`: homogeneous elements `x ∈ degree F m` and `y ∈ degree F n`
satisfy `x * y = (-1) ^ (m * n) • (y * x)`. -/
theorem mul_comm_of_mem_degree {m n : ℕ} {x y : MilnorK F}
    (hx : x ∈ degree F m) (hy : y ∈ degree F n) :
    x * y = ((-1 : ℤ) ^ (m * n)) • (y * x) := by
  rw [degree_eq_span] at hx hy
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [add_mul, mul_add, smul_add, hu, hv])
    (fun k u _ hu ↦ by rw [smul_mul_assoc k u, mul_smul_comm k y, hu, smul_comm]) hx
  rintro _ ⟨l₁, rfl, rfl⟩
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [mul_add, add_mul, smul_add, hu, hv])
    (fun k u _ hu ↦ by rw [mul_smul_comm k (symbol l₁), smul_mul_assoc k u, hu, smul_comm]) hy
  rintro _ ⟨l₂, rfl, rfl⟩
  exact symbol_mul_symbol l₁ l₂

private theorem symbol_append_cons_append_cons (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ)
    (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: l₂ ++ b :: l₃) =
      symbol l₁ * (ofUnit a * symbol l₂ * ofUnit b) * symbol l₃ := by
  simp only [symbol_append, symbol_cons, mul_assoc]

private theorem ofUnit_mul_symbol_mul_ofUnit (a b : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l * ofUnit b =
      ((-1 : ℤ) ^ l.length) • (symbol l * (ofUnit a * ofUnit b)) := by
  rw [ofUnit_mul_symbol, smul_mul_assoc, mul_assoc]

private theorem symbol_swap_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ) (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: l₂ ++ b :: l₃) = -symbol (l₁ ++ b :: l₂ ++ a :: l₃) := by
  rw [symbol_append_cons_append_cons, symbol_append_cons_append_cons,
    ofUnit_mul_symbol_mul_ofUnit a b l₂, ofUnit_mul_symbol_mul_ofUnit b a l₂,
    ofUnit_mul_ofUnit_comm a b]
  simp only [mul_neg, smul_neg, neg_mul]

/-- Applying a transposition to the entries of a Milnor symbol negates it. -/
theorem symbol_ofFn_comp_swap {n : ℕ} (a : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j) :
    symbol (List.ofFn (a ∘ Equiv.swap i j)) = -symbol (List.ofFn a) := by
  wlog hlt : i.val < j.val generalizing i j
  · rw [Equiv.swap_comm]
    exact this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) (Fin.val_ne_of_ne hij).symm)
  conv_lhs => rw [List.ofFn_comp_swap_of_lt a hlt]
  conv_rhs => rw [List.ofFn_eq_take_cons_of_lt a hlt]
  exact symbol_swap_middle _ (a j) _ (a i) _

/-- Permuting the entries of a Milnor symbol multiplies it by the sign of the permutation. -/
theorem symbol_ofFn_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fˣ) :
    symbol (List.ofFn (a ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • symbol (List.ofFn a) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing a with
  | one => simp
  | swap_mul τ i j hij ih =>
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc,
      ih (a ∘ Equiv.swap i j), symbol_ofFn_comp_swap a hij, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hij]
    simp only [Units.val_neg, neg_mul, one_mul, neg_zsmul, smul_neg]

/-- Any symbol with a repeated entry (not necessarily adjacent) is 2-torsion. -/
theorem two_nsmul_symbol_ofFn_eq_zero_of_eq {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) :
    2 • symbol (List.ofFn a) = 0 := by
  have hcomp : a ∘ Equiv.swap i j = a := funext fun k ↦ by
    rcases eq_or_ne k i with rfl | hki
    · simp [ha]
    · rcases eq_or_ne k j with rfl | hkj
      · simp [ha]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [two_nsmul, add_eq_zero_iff_eq_neg]
  simpa only [hcomp] using symbol_ofFn_comp_swap a hij

/-- In characteristic `2`, any symbol with a repeated entry vanishes. -/
theorem symbol_ofFn_eq_zero_of_charTwo_of_eq [CharP F 2] {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) :
    symbol (List.ofFn a) = 0 := by
  wlog hlt : i.val < j.val generalizing i j
  · exact this hij.symm ha.symm (lt_of_le_of_ne (not_lt.mp hlt) (Fin.val_ne_of_ne hij).symm)
  rw [List.ofFn_eq_take_cons_of_lt a hlt, ha, symbol_append_cons_append_cons,
    ofUnit_mul_symbol_mul_ofUnit, ofUnit_mul_self_eq_zero_of_charTwo, mul_zero, smul_zero,
    mul_zero, zero_mul]

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
