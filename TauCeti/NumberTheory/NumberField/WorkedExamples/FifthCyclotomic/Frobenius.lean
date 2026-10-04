/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.ArithmeticFrobenius
import Mathlib.Tactic.NormNum.Prime

/-!
# Frobenius elements in the fifth cyclotomic field

The arithmetic Frobenius at `2`, `3`, `7`, and `19` in a fifth cyclotomic field has cyclotomic
exponent `2`, `3`, `2`, and `-1`, respectively. At `11` it is the identity. These are
computations of the automorphisms themselves, complementing the residue degrees and prime
counts in `Cyclotomic.FiveSplitting`.

Each statement applies to every arithmetic Frobenius at the indicated prime. In particular,
the dyadic case uses the same arithmetic normalization as the odd primes.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapters 1 and 2.
-/

public section

open Ideal NumberField IsCyclotomicExtension
open scoped NumberField

namespace TauCeti.NumberField.FifthCyclotomic

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
  {σ : K ≃ₐ[ℚ] K} (Q : Ideal (𝓞 K)) [Q.IsPrime]

/-- At a prime above `2`, arithmetic Frobenius has exponent `2 mod 5`. -/
theorem galEquivZMod_eq_two_of_isArithFrobAt_two [Q.LiesOver (span {(2 : ℤ)})]
    (hσ : IsArithFrobAt ℤ σ Q) :
    (Rat.galEquivZMod 5 K σ : ZMod 5) = 2 := by
  have h := galEquivZMod_eq_unitOfCoprime_of_isArithFrobAt Q
    (by decide : Nat.Coprime 2 5) hσ
  exact (congrArg Units.val h).trans (by decide)

/-- At a prime above `3`, arithmetic Frobenius has exponent `3 mod 5`. -/
theorem galEquivZMod_eq_three_of_isArithFrobAt_three [Q.LiesOver (span {(3 : ℤ)})]
    (hσ : IsArithFrobAt ℤ σ Q) :
    (Rat.galEquivZMod 5 K σ : ZMod 5) = 3 := by
  have h := galEquivZMod_eq_unitOfCoprime_of_isArithFrobAt Q
    (by decide : Nat.Coprime 3 5) hσ
  exact (congrArg Units.val h).trans (by decide)

/-- At a prime above `7`, arithmetic Frobenius has exponent `2 mod 5`. -/
theorem galEquivZMod_eq_two_of_isArithFrobAt_seven [Q.LiesOver (span {(7 : ℤ)})]
    (hσ : IsArithFrobAt ℤ σ Q) :
    (Rat.galEquivZMod 5 K σ : ZMod 5) = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := galEquivZMod_eq_unitOfCoprime_of_isArithFrobAt Q
    (by decide : Nat.Coprime 7 5) hσ
  exact (congrArg Units.val h).trans (by decide)

/-- At a prime above `19`, arithmetic Frobenius has exponent `-1 mod 5`. -/
theorem galEquivZMod_eq_neg_one_of_isArithFrobAt_nineteen [Q.LiesOver (span {(19 : ℤ)})]
    (hσ : IsArithFrobAt ℤ σ Q) : Rat.galEquivZMod 5 K σ = -1 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have h := galEquivZMod_eq_unitOfCoprime_of_isArithFrobAt Q
    (by decide : Nat.Coprime 19 5) hσ
  exact h.trans (Units.ext (by decide))

/-- At a prime above `11`, arithmetic Frobenius is the identity. -/
theorem eq_one_of_isArithFrobAt_eleven [Q.LiesOver (span {(11 : ℤ)})]
    (hσ : IsArithFrobAt ℤ σ Q) : σ = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  apply (Rat.galEquivZMod 5 K).injective
  rw [map_one, galEquivZMod_eq_unitOfCoprime_of_isArithFrobAt Q
    (by decide : Nat.Coprime 11 5) hσ]
  exact Units.ext (by decide)

end TauCeti.NumberField.FifthCyclotomic
