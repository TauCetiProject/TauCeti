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
counts in `TauCeti.NumberTheory.NumberField.Cyclotomic.FiveSplitting`.

Each statement characterizes arithmetic Frobenius at the indicated prime.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapters 1 and 2.
-/

public section

open Ideal NumberField IsCyclotomicExtension
open scoped NumberField

namespace TauCeti.NumberField.FifthCyclotomic

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
  (Q : Ideal (𝓞 K)) [Q.IsPrime] (σ : K ≃ₐ[ℚ] K)

/-- At a prime above `2`, arithmetic Frobenius is characterized by exponent `2 mod 5`. -/
theorem isArithFrobAt_two_iff_galEquivZMod_eq_two [Q.LiesOver (span {(2 : ℤ)})] :
    IsArithFrobAt ℤ σ Q ↔ Rat.galEquivZMod 5 K σ = Units.mk0 (2 : ZMod 5) (by decide) := by
  have h : ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5) =
      Units.mk0 (2 : ZMod 5) (by decide) :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime]; decide)
  rw [isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime Q (by decide : Nat.Coprime 2 5) σ, h]

/-- At a prime above `3`, arithmetic Frobenius is characterized by exponent `3 mod 5`. -/
theorem isArithFrobAt_three_iff_galEquivZMod_eq_three [Q.LiesOver (span {(3 : ℤ)})] :
    IsArithFrobAt ℤ σ Q ↔ Rat.galEquivZMod 5 K σ = Units.mk0 (3 : ZMod 5) (by decide) := by
  have h : ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 5) =
      Units.mk0 (3 : ZMod 5) (by decide) :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime]; decide)
  rw [isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime Q (by decide : Nat.Coprime 3 5) σ, h]

/-- At a prime above `7`, arithmetic Frobenius is characterized by exponent `2 mod 5`. -/
theorem isArithFrobAt_seven_iff_galEquivZMod_eq_two [Q.LiesOver (span {(7 : ℤ)})] :
    IsArithFrobAt ℤ σ Q ↔ Rat.galEquivZMod 5 K σ = Units.mk0 (2 : ZMod 5) (by decide) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h : ZMod.unitOfCoprime 7 (by decide : Nat.Coprime 7 5) =
      Units.mk0 (2 : ZMod 5) (by decide) :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime]; decide)
  rw [isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime Q (by decide : Nat.Coprime 7 5) σ, h]

/-- At a prime above `19`, arithmetic Frobenius is characterized by exponent `-1 mod 5`. -/
theorem isArithFrobAt_nineteen_iff_galEquivZMod_eq_neg_one [Q.LiesOver (span {(19 : ℤ)})] :
    IsArithFrobAt ℤ σ Q ↔ Rat.galEquivZMod 5 K σ = -1 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have h : ZMod.unitOfCoprime 19 (by decide : Nat.Coprime 19 5) = (-1 : (ZMod 5)ˣ) :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime]; decide)
  rw [isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime Q (by decide : Nat.Coprime 19 5) σ, h]

/-- At a prime above `11`, an automorphism is arithmetic Frobenius exactly when it is
the identity. -/
theorem isArithFrobAt_eleven_iff_eq_one [Q.LiesOver (span {(11 : ℤ)})] :
    IsArithFrobAt ℤ σ Q ↔ σ = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h : ZMod.unitOfCoprime 11 (by decide : Nat.Coprime 11 5) = (1 : (ZMod 5)ˣ) :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime]; decide)
  rw [isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime Q (by decide : Nat.Coprime 11 5) σ, h,
    map_eq_one_iff (Rat.galEquivZMod 5 K) (Rat.galEquivZMod 5 K).injective]

end TauCeti.NumberField.FifthCyclotomic
