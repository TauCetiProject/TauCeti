/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.FieldTheory.MilnorKTheory.Grading
import TauCeti.Data.List.Swap

/-!
# Skew-symmetry and graded commutativity of Milnor K-theory

Over any field `F`, the Steinberg relation forces degree-one generators to anti-commute, yielding
graded commutativity (`MilnorK.mul_comm_of_mem_degree`), permutation skew-symmetry of Milnor symbols
(`MilnorK.symbol_ofFn_comp_perm`), vanishing for opposite pairs (`MilnorK.symbol_neg_self_of_ne`),
`2`-torsion for repeated entries (`MilnorK.two_nsmul_symbol_of_duplicate`), and vanishing of
repeated entries in characteristic `2` (`MilnorK.symbol_eq_zero_of_duplicate_of_charTwo`).

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §7.1.
-/

public section

namespace TauCeti.MilnorK

variable {F : Type*} [Field F]

/-! ### Degree-two field identities in `MilnorK F` -/

@[simp] theorem ofUnit_mul_neg_self (a : Fˣ) : ofUnit a * ofUnit (-a) = 0 :=
  isSteinbergPairing_ofUnit_mul.map_neg_self a
theorem ofUnit_mul_comm (a b : Fˣ) : ofUnit a * ofUnit b = -(ofUnit b * ofUnit a) :=
  isSteinbergPairing_ofUnit_mul.map_swap a b
theorem ofUnit_mul_self (a : Fˣ) : ofUnit a * ofUnit a = ofUnit a * ofUnit (-1) :=
  isSteinbergPairing_ofUnit_mul.map_self a
theorem two_nsmul_ofUnit_mul_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 :=
  isSteinbergPairing_ofUnit_mul.two_nsmul_map_self a
theorem ofUnit_mul_self_eq_zero_of_charTwo [CharP F 2] (a : Fˣ) : ofUnit a * ofUnit a = 0 :=
  isSteinbergPairing_ofUnit_mul.map_self_eq_zero_of_charTwo a

/-! ### Graded commutativity -/

/-- Moving a degree-one generator past a Milnor symbol multiplies by `(-1) ^ l.length`. -/
theorem ofUnit_mul_symbol (a : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l = (-1 : ℤ) ^ l.length • (symbol l * ofUnit a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [symbol_cons, List.length_cons, pow_succ', mul_zsmul, neg_one_zsmul, ← mul_assoc,
      ofUnit_mul_comm a b, neg_mul (α := MilnorK F), mul_assoc, ih, mul_smul_comm, ← mul_assoc]

/-- Commuting two Milnor symbols multiplies by `(-1) ^ (l₁.length * l₂.length)`. -/
theorem symbol_mul_symbol (l₁ l₂ : List Fˣ) :
    symbol l₁ * symbol l₂ = (-1 : ℤ) ^ (l₁.length * l₂.length) • (symbol l₂ * symbol l₁) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [symbol_cons, List.length_cons, add_mul, one_mul, pow_add, mul_zsmul, mul_assoc, ih,
      mul_smul_comm, ← mul_assoc, ofUnit_mul_symbol a l₂, smul_mul_assoc, mul_assoc]

/-- **Graded commutativity of `MilnorK F`**: homogeneous elements of degrees `m` and `n` satisfy
`x * y = (-1)^(m * n) • (y * x)`. -/
theorem mul_comm_of_mem_degree {m n : ℕ} {x y : MilnorK F}
    (hx : x ∈ degree F m) (hy : y ∈ degree F n) :
    x * y = (-1 : ℤ) ^ (m * n) • (y * x) := by
  rw [degree_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨l₁, rfl, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem _ hy => obtain ⟨l₂, rfl, rfl⟩ := hy; exact symbol_mul_symbol l₁ l₂
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [mul_add, add_mul, smul_add, h₁, h₂]
    | smul _ _ _ hy => rw [mul_smul_comm, smul_mul_assoc, smul_comm, hy]
  | zero => simp
  | add _ _ _ _ h₁ h₂ => rw [add_mul, mul_add, smul_add, h₁, h₂]
  | smul _ _ _ hx => rw [smul_mul_assoc, mul_smul_comm, smul_comm, hx]

/-! ### Skew-symmetry under entry swaps and permutations -/

/-- Swapping two adjacent entries of a Milnor symbol negates it. -/
theorem symbol_swap_adjacent (l₁ : List Fˣ) (a b : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: b :: l₂) = -symbol (l₁ ++ b :: a :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁), ofUnit_mul_comm a b, mul_neg (α := MilnorK F),
    neg_mul (α := MilnorK F), ← mul_assoc]

/-- Swapping any two separated entries of a Milnor symbol negates it. -/
theorem symbol_swap_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ) (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: (l₂ ++ b :: l₃)) = -symbol (l₁ ++ b :: (l₂ ++ a :: l₃)) := by
  have hinner : ofUnit a * symbol l₂ * ofUnit b = -(ofUnit b * symbol l₂ * ofUnit a) := by
    rw [ofUnit_mul_symbol a l₂, smul_mul_assoc, mul_assoc, ofUnit_mul_comm a b,
      mul_neg (α := MilnorK F), smul_neg, ← mul_assoc, ← smul_mul_assoc, ← ofUnit_mul_symbol b l₂]
  calc symbol (l₁ ++ a :: (l₂ ++ b :: l₃))
      = symbol l₁ * (ofUnit a * symbol l₂ * ofUnit b) * symbol l₃ := by
        simp only [symbol_append, symbol_cons, mul_assoc]
    _ = symbol l₁ * -(ofUnit b * symbol l₂ * ofUnit a) * symbol l₃ := by rw [hinner]
    _ = -symbol (l₁ ++ b :: (l₂ ++ a :: l₃)) := by
        rw [mul_neg (α := MilnorK F), neg_mul (α := MilnorK F)]
        simp only [symbol_append, symbol_cons, mul_assoc]

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
    rw [hcomp, ih (v ∘ Equiv.swap i j), symbol_ofFn_comp_swap v hij, smul_neg, map_mul,
      Equiv.Perm.sign_swap hij, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul, neg_zsmul]

/-! ### Repeated and opposite entries -/

/-- A repeated adjacent entry in a Milnor symbol may be replaced by `a, -1`. -/
theorem symbol_self_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = symbol (l₁ ++ a :: (-1) :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁), ofUnit_mul_self, ← mul_assoc]

/-- A Milnor symbol containing two adjacent opposite entries `a, -a` vanishes. -/
@[simp] theorem symbol_neg_self_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: (-a) :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁), ofUnit_mul_neg_self, mul_zero, zero_mul]

/-- A Milnor symbol containing opposite entries `v j = -v i` at distinct positions vanishes. -/
theorem symbol_neg_self_of_ne {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : v j = -v i) : symbol (List.ofFn v) = 0 := by
  have hvanish (l₁ l₂ l₃ : List Fˣ) (a : Fˣ) : symbol (l₁ ++ a :: (l₂ ++ (-a) :: l₃)) = 0 := by
    have hinner : ofUnit a * symbol l₂ * ofUnit (-a) = 0 := by
      rw [ofUnit_mul_symbol a l₂, smul_mul_assoc, mul_assoc, ofUnit_mul_neg_self,
        mul_zero, smul_zero]
    calc symbol (l₁ ++ a :: (l₂ ++ (-a) :: l₃))
        = symbol l₁ * (ofUnit a * symbol l₂ * ofUnit (-a)) * symbol l₃ := by
          simp only [symbol_append, symbol_cons, mul_assoc]
      _ = 0 := by rw [hinner, mul_zero, zero_mul]
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
