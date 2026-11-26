/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.RingTheory.MilnorK.Basic
import TauCeti.Algebra.Ring.Parity
import TauCeti.Data.List.Swap

/-!
# Permutation skew-symmetry and repeated-entry identities in Milnor K-theory

Over any field `F`, `TauCeti.RingTheory.MilnorK.Basic` establishes that degree-one classes
anti-commute and satisfies graded commutativity (`MilnorK.mul_comm_of_mem_degree`). This file
extends those identities to general swaps and permutations of Milnor symbols
(`MilnorK.symbol_swap_middle`, `MilnorK.symbol_ofFn_comp_perm`), vanishing for opposite entries at
distinct positions (`MilnorK.symbol_neg_self_of_ne`), `2`-torsion for repeated entries
(`MilnorK.two_nsmul_symbol_of_duplicate`), and vanishing of repeated entries in characteristic `2`
(`MilnorK.symbol_eq_zero_of_duplicate_of_charTwo`).

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §7.1.
-/

public section

namespace TauCeti.MilnorK

variable {F : Type*} [Field F]

/-! ### Degree-two field identities in `MilnorK F` -/

/-- Every diagonal product `ofUnit a * ofUnit a` over a field is `2`-torsion. -/
theorem two_nsmul_ofUnit_mul_ofUnit_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 := by
  rw [two_nsmul]; exact add_eq_zero_iff_eq_neg.mpr (ofUnit_mul_ofUnit_comm a a)

/-- In characteristic two, every diagonal product `ofUnit a * ofUnit a` vanishes. -/
@[simp]
theorem ofUnit_mul_ofUnit_self_eq_zero_of_charTwo [CharP F 2] (a : Fˣ) :
    ofUnit a * ofUnit a = 0 := by
  have hneg1 : (-1 : Fˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
  rw [ofUnit_mul_ofUnit_self, hneg1, ofUnit_one, mul_zero]

/-! ### Skew-symmetry under entry swaps and permutations -/

private theorem symbol_separated (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ) (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: (l₂ ++ b :: l₃)) =
      (-1) ^ l₂.length * (symbol l₁ * symbol l₂ * (ofUnit a * ofUnit b) * symbol l₃) := by
  have hinner : ofUnit a * symbol l₂ * ofUnit b =
      (-1) ^ l₂.length * (symbol l₂ * (ofUnit a * ofUnit b)) := by
    rw [ofUnit_mul_of_mem_degree a (symbol_mem_degree l₂), mul_assoc, mul_assoc]
  calc symbol (l₁ ++ a :: (l₂ ++ b :: l₃))
      = symbol l₁ * (ofUnit a * symbol l₂ * ofUnit b) * symbol l₃ := by
        simp only [symbol_append, symbol_cons, mul_assoc]
    _ = symbol l₁ * ((-1) ^ l₂.length * (symbol l₂ * (ofUnit a * ofUnit b))) * symbol l₃ := by
        rw [hinner]
    _ = (-1) ^ l₂.length * (symbol l₁ * symbol l₂ * (ofUnit a * ofUnit b) * symbol l₃) := by
        rw [mul_neg_one_pow_mul]; simp only [mul_assoc]

/-- Swapping any two separated entries of a Milnor symbol negates it. -/
theorem symbol_swap_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ) (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: (l₂ ++ b :: l₃)) = -symbol (l₁ ++ b :: (l₂ ++ a :: l₃)) := by
  rw [symbol_separated l₁ a l₂ b l₃, symbol_separated l₁ b l₂ a l₃, ofUnit_mul_ofUnit_comm a b,
    mul_neg (α := MilnorK F), neg_mul (α := MilnorK F), mul_neg]

/-- Swapping two distinct entries `i ≠ j` of a Milnor symbol negates it. -/
theorem symbol_ofFn_comp_swap {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j) :
    symbol (List.ofFn (v ∘ Equiv.swap i j)) = -symbol (List.ofFn v) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨_, _, _, hv, hvs⟩ := List.exists_split_ofFn_swap v hlt
    rw [hv, hvs, symbol_swap_middle]
  · rw [Equiv.swap_comm]
    obtain ⟨_, _, _, hv, hvs⟩ := List.exists_split_ofFn_swap v hgt
    rw [hv, hvs, symbol_swap_middle]

/-- **Skew-symmetry of Milnor symbols**: permuting entries multiplies by `sign σ`. -/
theorem symbol_ofFn_comp_perm {n : ℕ} (v : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    symbol (List.ofFn (v ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • symbol (List.ofFn v) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => simp
  | swap_mul f i j hij ih =>
    have hcomp : v ∘ ⇑(Equiv.swap i j * f) = (v ∘ Equiv.swap i j) ∘ f :=
      funext fun k => congrArg v (Equiv.Perm.mul_apply (Equiv.swap i j) f k)
    rw [hcomp, ih (v ∘ Equiv.swap i j), symbol_ofFn_comp_swap v hij]
    simp [Equiv.Perm.sign_swap hij]

/-! ### Repeated and opposite entries -/

/-- A repeated adjacent entry in a Milnor symbol may be replaced by `a, -1`. -/
theorem symbol_append_cons_cons_self (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = symbol (l₁ ++ a :: (-1) :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁), ofUnit_mul_ofUnit_self, ← mul_assoc]

/-- A Milnor symbol containing two adjacent opposite entries `a, -a` vanishes. -/
theorem symbol_append_cons_cons_neg_self (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: (-a) :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁), ofUnit_mul_ofUnit_neg_self, mul_zero, zero_mul]

/-- A Milnor symbol containing opposite entries `v j = -v i` at distinct positions vanishes. -/
theorem symbol_neg_self_of_ne {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : v j = -v i) : symbol (List.ofFn v) = 0 := by
  have hvanish (l₁ l₂ l₃ : List Fˣ) (a : Fˣ) : symbol (l₁ ++ a :: (l₂ ++ (-a) :: l₃)) = 0 := by
    rw [symbol_separated, ofUnit_mul_ofUnit_neg_self, mul_zero, zero_mul, mul_zero]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨l₁, l₂, l₃, hv, -⟩ := List.exists_split_ofFn_swap v hlt
    rw [hv, h]; exact hvanish l₁ l₂ l₃ (v i)
  · obtain ⟨l₁, l₂, l₃, hv, -⟩ := List.exists_split_ofFn_swap v hgt
    have hi : v i = -v j := by rw [h, neg_neg]
    rw [hv, hi]; exact hvanish l₁ l₂ l₃ (v j)

/-- A Milnor symbol with a repeated entry is `2`-torsion. -/
theorem two_nsmul_symbol_of_duplicate {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : v i = v j) : 2 • symbol (List.ofFn v) = 0 := by
  have hswap : v ∘ Equiv.swap i j = v := funext fun k => by
    simp only [Function.comp_apply, Equiv.swap_apply_def]; split_ifs <;> simp_all
  have hneg := symbol_ofFn_comp_swap v hij
  rw [hswap] at hneg; rw [two_nsmul]; exact add_eq_zero_iff_eq_neg.mpr hneg

/-- Over a field of characteristic `2`, any Milnor symbol with a repeated entry vanishes. -/
theorem symbol_eq_zero_of_duplicate_of_charTwo [CharP F 2] {n : ℕ} (v : Fin n → Fˣ)
    {i j : Fin n} (hij : i ≠ j) (h : v i = v j) : symbol (List.ofFn v) = 0 :=
  symbol_neg_self_of_ne v hij (Units.ext (by simp [h, CharTwo.neg_eq]))

end TauCeti.MilnorK
