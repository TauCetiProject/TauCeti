/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.Ring

/-!
# Powers of negative one in a ground ring

This file provides the cast to a ground ring of Mathlib's unit-valued sign character
`Int.negOnePow : ℤ → ℤˣ`; the cast factors through `ℤ`.

## Main definitions

* `TauCeti.negOnePowCast`: the scalar `(-1) ^ e` in a ground ring.

## Main results

* `TauCeti.negOnePowCast_sum`: the sign of a finite sum is the product of the signs of its terms.
* `TauCeti.sum_range_negOnePowCast_telescope`: an alternating sum of products, in which one
  factor is replaced by a two-term correction, telescopes.
* `TauCeti.negOnePow_smul_eq_negOnePowCast_smul`: the unit-valued sign and its ground-ring cast
  induce the same scalar action on a module.
* `TauCeti.negOnePow_smul_negOnePow_smul`: the unit-valued sign acts as an involution.
* `Int.negOnePow_mul_one_sub`, `Int.negOnePow_mul_two_sub`: signs of quadratic products.
* `Int.negOnePow_sub_sub_one`, `TauCeti.negOnePow_mul_negOnePow_of_even`: the parity
  identities behind the sign cancellations of twisted differentials.
-/

public section

universe uR uA uI

namespace TauCeti

section NegOnePowCast

variable {R : Type uR} [Ring R]

variable (R) in
/-- The scalar `(-1) ^ e` in a ground ring. -/
def negOnePowCast (e : ℤ) : R := ((e.negOnePow : ℤ) : R)

/-- The ground-ring sign is the cast of Mathlib's `Int.negOnePow`. -/
theorem negOnePowCast_eq_intCast (e : ℤ) : negOnePowCast R e = ((e.negOnePow : ℤ) : R) :=
  (rfl)

@[simp]
theorem negOnePowCast_zero : negOnePowCast R 0 = 1 := by simp [negOnePowCast]

@[simp]
theorem negOnePowCast_one : negOnePowCast R 1 = -1 := by simp [negOnePowCast]

@[simp]
theorem negOnePowCast_neg (a : ℤ) : negOnePowCast R (-a) = negOnePowCast R a := by
  simp [negOnePowCast]

theorem negOnePowCast_add (a b : ℤ) :
    negOnePowCast R (a + b) = negOnePowCast R a * negOnePowCast R b := by
  simp [negOnePowCast, Int.negOnePow_add]

@[simp]
theorem negOnePowCast_two_mul (a : ℤ) : negOnePowCast R (2 * a) = 1 := by
  simp [negOnePowCast]

/-- The scalar `(-1) ^ e` squares to one. -/
@[simp]
theorem negOnePowCast_mul_self (e : ℤ) : negOnePowCast R e * negOnePowCast R e = 1 := by
  rw [← negOnePowCast_add, ← two_mul, negOnePowCast_two_mul]

theorem negOnePowCast_even {e : ℤ} (he : Even e) : negOnePowCast R e = 1 := by
  simp [negOnePowCast, Int.negOnePow_even _ he]

theorem negOnePowCast_odd {e : ℤ} (he : Odd e) : negOnePowCast R e = -1 := by
  simp [negOnePowCast, Int.negOnePow_odd _ he]

section

variable {A : Type uA} [AddCommGroup A] [Module R A]

/-- A sign `(-1) ^ e`, acting through the units of `ℤ`, acts as its cast to the ground ring. -/
theorem negOnePow_smul_eq_negOnePowCast_smul (e : ℤ) (a : A) :
    e.negOnePow • a = negOnePowCast R e • a := by
  rw [negOnePowCast, Units.smul_def, ← Int.cast_smul_eq_zsmul R]

end

variable {A : Type uA}

/-- The scalar `(-1) ^ e` acts as an involution. -/
@[simp]
theorem negOnePowCast_smul_negOnePowCast_smul [MulAction R A] (e : ℤ) (a : A) :
    negOnePowCast R e • (negOnePowCast R e • a) = a := by
  rw [smul_smul, ← negOnePowCast_add, ← two_mul, negOnePowCast_two_mul, one_smul]

@[simp]
theorem negOnePowCast_smul_eq_zero_iff [AddMonoid A] [DistribMulAction R A] (e : ℤ) (a : A) :
    negOnePowCast R e • a = 0 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← negOnePowCast_smul_negOnePowCast_smul (R := R) e a, h, smul_zero]

end NegOnePowCast

section NegOnePowSMul

variable {A : Type uA} [AddGroup A]

/-- The sign `(-1) ^ e`, acting through the units of `ℤ`, acts as an involution. -/
@[simp]
theorem negOnePow_smul_negOnePow_smul (e : ℤ) (a : A) : e.negOnePow • e.negOnePow • a = a := by
  rw [smul_smul, Int.units_mul_self, one_smul]

end NegOnePowSMul

section Parity

/-- The product of an integer and one minus that integer is even, so its sign is one. -/
@[simp]
theorem _root_.Int.negOnePow_mul_one_sub (n : ℤ) :
    (n * (1 - n)).negOnePow = 1 := by
  rw [Int.negOnePow_eq_one_iff]
  simpa only [← mul_neg, neg_sub] using n.even_mul_pred_self.neg

/-- The product of an integer and two minus that integer has the same parity as the integer. -/
@[simp]
theorem _root_.Int.negOnePow_mul_two_sub (n : ℤ) :
    (n * (2 - n)).negOnePow = n.negOnePow := by
  simp only [mul_sub, mul_comm n 2, Int.negOnePow_sub, Int.negOnePow_two_mul,
    Int.negOnePow_mul_self, one_mul]

/-- Reversing a difference and shifting it by one flips the sign:
`(-1) ^ (a - b - 1) = -(-1) ^ (b - a)`. -/
theorem _root_.Int.negOnePow_sub_sub_one (a b : ℤ) :
    (a - b - 1).negOnePow = -(b - a).negOnePow := by
  rw [← Int.negOnePow_succ, Int.negOnePow_eq_iff]
  exact ⟨a - b - 1, by omega⟩

/-- A product of two signs is the sign of any exponent congruent modulo two to the sum of their
exponents. -/
theorem negOnePow_mul_negOnePow_of_even {a b c : ℤ} (h : Even (a + b - c)) :
    a.negOnePow * b.negOnePow = c.negOnePow := by
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact h

end Parity

section CommRing

variable {R : Type uR} [CommRing R]

/-- The sign of a finite sum is the product of the signs of its terms: the sign character turns
addition into multiplication, so it distributes over `Finset.sum`. -/
theorem negOnePowCast_sum {ι : Type uI} (s : Finset ι) (f : ι → ℤ) :
    negOnePowCast R (∑ i ∈ s, f i) = ∏ i ∈ s, negOnePowCast R (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.prod_cons, negOnePowCast_add, ih]

/-- **Telescoping an alternating sum of products.** The `p`-th summand is
`α 0 ⋯ α (p - 1) · (ε p · β p + α p · ε (p + 1)) · β (p + 1) ⋯ β (n - 1)`, that is, the factor
`β p` of `α 0 ⋯ α (p - 1) · β p ⋯ β (n - 1)` is replaced by `ε p · β p + α p · ε (p + 1)`.
Writing `u q = (-1) ^ q · α 0 ⋯ α (q - 1) · ε q · β q ⋯ β (n - 1)`, the signed `p`-th summand
is `u p - u (p + 1)`, so the alternating sum over `p < n` telescopes to `u 0 - u n`. -/
theorem sum_range_negOnePowCast_telescope (n : ℕ) (α β ε : ℕ → R) :
    ∑ p ∈ Finset.range n, negOnePowCast R (p : ℤ) * ((∏ i ∈ Finset.range p, α i) *
        (ε p * β p + α p * ε (p + 1)) * ∏ i ∈ Finset.Ico (p + 1) n, β i) =
      ε 0 * ∏ i ∈ Finset.range n, β i -
        negOnePowCast R (n : ℤ) * ((∏ i ∈ Finset.range n, α i) * ε n) := by
  set u : ℕ → R := fun q ↦ negOnePowCast R (q : ℤ) *
    ((∏ i ∈ Finset.range q, α i) * ε q * ∏ i ∈ Finset.Ico q n, β i) with hu
  have hterm : ∀ p ∈ Finset.range n, negOnePowCast R (p : ℤ) * ((∏ i ∈ Finset.range p, α i) *
      (ε p * β p + α p * ε (p + 1)) * ∏ i ∈ Finset.Ico (p + 1) n, β i) = u p - u (p + 1) := by
    intro p hp
    simp only [hu, Finset.prod_eq_prod_Ico_succ_bot (Finset.mem_range.1 hp),
      Finset.prod_range_succ, Nat.cast_succ, negOnePowCast_add, negOnePowCast_one]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  simp only [hu, Nat.Ico_zero_eq_range, Finset.prod_range_zero, Finset.Ico_self,
    Finset.prod_empty, Nat.cast_zero, negOnePowCast_zero]
  ring

end CommRing

end TauCeti
