/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.GroupTheory.Divisible

import TauCeti.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational modules and divisible torsion-free groups

Every module over `ℚ` is a module over `ℚ≥0` by restriction of scalars along
`algebraMap ℚ≥0 ℚ`. This is deliberately not a global instance: Mathlib already builds
`Module ℚ≥0 R` from `DivisionSemiring R`, so a second global path would put two structures on
types such as `ℚ` itself; they agree by `subsingleton_nnrat_module`, but not definitionally.

Consumers activate it where they need it with
`attribute [local instance] TauCeti.moduleNNRat`. The typical use is to obtain Mathlib's
`BinomialRing` instance — which is stated for a `Module ℚ≥0` — on a possibly noncommutative
`ℚ`-algebra such as a universal enveloping algebra, so that `Ring.choose` elaborates there.

Over a semiring that is a `ℚ`-module, scaling by `(n : ℚ)⁻¹` undoes multiplication by a nonzero
natural number `n`. More generally, multiplication by a nonzero integer is bijective on any module
over a division ring of characteristic zero. Conversely, a divisible torsion-free abelian group
admits a rational module structure, unique by `subsingleton_rat_module`.

## Main definitions

* `TauCeti.moduleNNRat`: the `ℚ≥0`-module structure on a `ℚ`-module.

## Main statements

* `TauCeti.nonempty_ratModule`: a divisible torsion-free abelian group admits a rational module
  structure.
* `TauCeti.inv_natCast_smul_natCast_mul`: `(n : ℚ)⁻¹ • (n * x) = x` for `n ≠ 0`.
* `TauCeti.inv_natCast_mul_smul_nsmul`: `((n * m : ℕ) : ℚ)⁻¹ • (n • x) = (m : ℚ)⁻¹ • x` for `n ≠ 0`.
* `TauCeti.bijective_zsmul_of_ne_zero`: multiplication by a nonzero integer is bijective on a module
  over a division ring of characteristic zero.
-/

public section

namespace TauCeti

/-- The nonnegative-rational module structure induced on a rational module. -/
@[instance_reducible]
def moduleNNRat {A : Type*} [AddCommMonoid A] [Module ℚ A] : Module ℚ≥0 A :=
  Module.compHom _ (algebraMap ℚ≥0 ℚ)

/-- Over a semiring that is a `ℚ`-module, `(n : ℚ)⁻¹ •` undoes multiplication by a nonzero natural
number `n`. -/
theorem inv_natCast_smul_natCast_mul {A : Type*} [Semiring A] [Module ℚ A] {n : ℕ} (hn : n ≠ 0)
    (x : A) : (n : ℚ)⁻¹ • ((n : A) * x) = x := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn)]

/-- In a `ℚ`-module, a factor `n ≠ 0` of `n * m` cancels against `n •`:
`((n * m : ℕ) : ℚ)⁻¹ • (n • x) = (m : ℚ)⁻¹ • x`. -/
theorem inv_natCast_mul_smul_nsmul {A : Type*} [AddCommMonoid A] [Module ℚ A] {n m : ℕ}
    (hn : n ≠ 0) (x : A) : ((n * m : ℕ) : ℚ)⁻¹ • (n • x) = (m : ℚ)⁻¹ • x := by
  rw [Nat.cast_mul, mul_inv_rev, mul_smul, ← Nat.cast_smul_eq_nsmul ℚ,
    inv_smul_smul₀ (Nat.cast_ne_zero.2 hn)]

/-- Multiplication by a nonzero integer is bijective on a module over a division ring of
characteristic zero. -/
theorem bijective_zsmul_of_ne_zero (K : Type*) {M : Type*} [DivisionRing K] [CharZero K]
    [AddCommGroup M] [Module K M] {n : ℤ} (hn : n ≠ 0) : Function.Bijective fun x : M ↦ n • x := by
  simpa only [← Int.cast_smul_eq_zsmul K] using
    (Int.cast_ne_zero.mpr hn : (n : K) ≠ 0).isUnit.smul_bijective (β := M)

open scoped nonZeroDivisors

/-- A divisible abelian group with injective multiplication by positive integers has a
rational vector-space structure. It is unique by `subsingleton_rat_module`. -/
theorem nonempty_ratModule (A : Type*) [AddCommGroup A] [DivisibleBy A ℕ] [HasUniqueDiv A] :
    Nonempty (Module ℚ A) := by
  let : DivisibleBy A ℤ := AddGroup.divisibleByIntOfDivisibleByNat A
  let : IsLocalizedModule ℤ⁰ (LinearMap.id : A →ₗ[ℤ] A) :=
    isLocalizedModule_id_of_bijective_smul fun n hn ↦
      ⟨zsmul_right_injective (nonZeroDivisors.ne_zero hn),
        DivisibleBy.surjective_smul A ℤ (nonZeroDivisors.ne_zero hn)⟩
  exact ⟨IsLocalizedModule.module (A := ℚ) ℤ⁰ (LinearMap.id : A →ₗ[ℤ] A)⟩

end TauCeti
