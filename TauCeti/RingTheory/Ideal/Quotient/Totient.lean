/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Units of the quotient by a power of a maximal ideal

For a maximal ideal `P` of a commutative ring and `e ≠ 0`, the quotient `R ⧸ P ^ e` is a local
ring whose units are the residues outside `P`. This file counts them:
`#(R ⧸ P ^ e)ˣ · #(R ⧸ P) = #(R ⧸ P ^ e) · (#(R ⧸ P) - 1)`, where `#` is `Nat.card`. This is the
local step of Euler's totient for ideals.

## Main results

* `Ideal.card_units_quotient_pow_mul_card_quotient`: `#(R ⧸ P ^ e)ˣ · #(R ⧸ P) =
  #(R ⧸ P ^ e) · (#(R ⧸ P) - 1)` for a maximal ideal `P` and `e ≠ 0`, with no finiteness
  hypothesis.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- **Units of the quotient by a prime power.** For a maximal ideal `P` of a commutative ring and
`e ≠ 0`, `#(R ⧸ P ^ e)ˣ · #(R ⧸ P) = #(R ⧸ P ^ e) · (#(R ⧸ P) - 1)`, where `#` is `Nat.card`,
which is `0` on infinite types. The units of the local ring `R ⧸ P ^ e` are the residues outside
`P`, so when `R ⧸ P ^ e` is finite they make up `1 - 1 / #(R ⧸ P)` of the quotient. When
`R ⧸ P ^ e` is infinite both sides are `0`. -/
theorem card_units_quotient_pow_mul_card_quotient (P : Ideal R) [P.IsMaximal] {e : ℕ}
    (he : e ≠ 0) :
    Nat.card (R ⧸ P ^ e)ˣ * Nat.card (R ⧸ P) =
      Nat.card (R ⧸ P ^ e) * (Nat.card (R ⧸ P) - 1) := by
  classical
  let f : R ⧸ P ^ e →+* R ⧸ P := Ideal.Quotient.factor (Ideal.pow_le_self he)
  have hunit (x : R ⧸ P ^ e) : IsUnit x ↔ ¬ f x = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.isUnit_mk_pow_iff_notMem P he]
    simp [f, Ideal.Quotient.eq_zero_iff_mem]
  have hA : Nat.card (R ⧸ P ^ e) = Nat.card (R ⧸ P) * Nat.card f.toAddMonoidHom.ker := by
    rw [mul_comm]
    exact (AddSubgroup.card_ker_mul_card_of_surjective (f := f.toAddMonoidHom)
      (Ideal.Quotient.factor_surjective (pow_le_self he))).symm
  obtain hfin | hinf := finite_or_infinite (R ⧸ P ^ e)
  · have hU : Nat.card (R ⧸ P ^ e)ˣ + Nat.card f.toAddMonoidHom.ker = Nat.card (R ⧸ P ^ e) := by
      rw [Nat.card_congr (Equiv.sumCompl fun x : R ⧸ P ^ e ↦ IsUnit x).symm, Nat.card_sum,
        Nat.card_congr (Submonoid.unitsTypeEquivIsUnitSubmonoid (M := R ⧸ P ^ e)).toEquiv]
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight (p := (· ∈ f.toAddMonoidHom.ker))
        (q := fun x ↦ ¬ IsUnit x) fun x ↦ by simp [hunit])
    rw [Nat.mul_sub_one]
    exact Nat.eq_sub_of_add_eq (by nth_rw 2 [← hU]; rw [hA]; ring)
  -- If `R ⧸ P ^ e` is infinite, then so is `R ⧸ P` or the kernel `P / P ^ e`, and in the latter
  -- case `x ↦ 1 + x` embeds the kernel into the units.
  rw [Nat.card_eq_zero_of_infinite (α := R ⧸ P ^ e), zero_mul, mul_eq_zero]
  obtain h | h := mul_eq_zero.mp (hA.symm.trans Nat.card_eq_zero_of_infinite)
  · exact .inr h
  have : Infinite f.toAddMonoidHom.ker :=
    (Nat.card_eq_zero.mp h).resolve_left (not_isEmpty_of_nonempty _)
  have h1 (x : f.toAddMonoidHom.ker) : IsUnit (1 + (x : R ⧸ P ^ e)) := by
    have hx : f x = 0 := by simpa using AddMonoidHom.mem_ker.mp x.2
    simp [hunit, hx]
  have : Infinite (R ⧸ P ^ e)ˣ := Infinite.of_injective (fun x ↦ (h1 x).unit)
    fun x y hxy ↦ by simpa using congrArg Units.val hxy
  exact .inl Nat.card_eq_zero_of_infinite

end Ideal
