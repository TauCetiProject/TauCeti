/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import TauCeti.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise

/-!
# Primitive recursive binary operations

Primitive recursion certificates for exponentiation, bit inspection, the increasing list of
set bits, and binary bitwise operations. These certificates allow finite sets represented by
binary natural numbers to be used in effective constructions.
-/

public section

namespace Primrec

/-- Natural-number exponentiation is primitive recursive. -/
theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- Inspecting a binary digit is primitive recursive. -/
theorem nat_testBit : Primrec₂ Nat.testBit := by
  refine (Primrec.eq.comp (nat_mod.comp (nat_div.comp fst (nat_pow.comp (const 2) snd))
    (const 2)) (const 1)).decide.of_eq ?_
  intro p
  exact Nat.testBit_eq_decide_div_mod_eq.symm

/-- The increasing list of set bits is primitive recursive. -/
theorem nat_bitIndices : Primrec Nat.bitIndices := by
  have h := (Primrec.eq.comp (nat_testBit.comp snd fst) (const true)).primrecRel.listFilter.comp
    list_range Primrec.id
  exact h.of_eq fun n => by simp [Nat.bitIndices_eq_filter_range]

/-- Binary bitwise operations that send two zero bits to zero are primitive recursive. -/
theorem nat_bitwise (f : Bool → Bool → Bool) (hf : f false false = false) :
    Primrec₂ (Nat.bitwise f) := by
  have hbits : PrimrecRel fun i (p : (ℕ × ℕ) × ℕ) =>
      p.2.testBit i = f (p.1.1.testBit i) (p.1.2.testBit i) :=
    Primrec.eq.comp (nat_testBit.comp (snd.comp snd) fst)
      ((dom_bool₂ f).comp (nat_testBit.comp (fst.comp (fst.comp snd)) fst)
        (nat_testBit.comp (snd.comp (fst.comp snd)) fst))
  refine of_graph ⟨fun p => 2 ^ (p.1 + p.2 + 1),
    nat_pow.comp (const 2) (succ.comp nat_add), fun p => ?_⟩ ?_
  · exact (Nat.bitwise_lt_two_pow
      ((by omega : p.1 ≤ p.1 + p.2 + 1).trans_lt (p.1 + p.2 + 1).lt_two_pow_self)
      ((by omega : p.2 ≤ p.1 + p.2 + 1).trans_lt (p.1 + p.2 + 1).lt_two_pow_self)).le
  · refine PrimrecRel.of_eq (hbits.forall_mem_list.comp
      (list_range.comp (succ.comp (nat_add.comp (nat_add.comp (fst.comp fst)
        (snd.comp fst)) snd))) Primrec.id).primrecRel ?_
    rintro ⟨a, b⟩ c
    simp only [List.mem_range]
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_bitwise hf]
      by_cases hi : i < a + b + c + 1
      · exact (h i hi).symm
      · have ha : a < 2 ^ i := (by omega : a ≤ i).trans_lt i.lt_two_pow_self
        have hb : b < 2 ^ i := (by omega : b ≤ i).trans_lt i.lt_two_pow_self
        have hc : c < 2 ^ i := (by omega : c ≤ i).trans_lt i.lt_two_pow_self
        simp [Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb,
          Nat.testBit_eq_false_of_lt hc, hf]
    · rintro rfl i _
      exact Nat.testBit_bitwise hf _ _ _

/-- Binary union is primitive recursive. -/
theorem nat_lor : Primrec₂ Nat.lor :=
  (nat_bitwise (· || ·) rfl).of_eq fun a b =>
    Nat.eq_of_testBit_eq fun i => by simp

/-- Binary intersection is primitive recursive. -/
theorem nat_land : Primrec₂ Nat.land :=
  (nat_bitwise (· && ·) rfl).of_eq fun a b =>
    Nat.eq_of_testBit_eq fun i => by simp

/-- Binary difference is primitive recursive. -/
theorem nat_ldiff : Primrec₂ Nat.ldiff := nat_bitwise (fun a b => a && !b) rfl

end Primrec
