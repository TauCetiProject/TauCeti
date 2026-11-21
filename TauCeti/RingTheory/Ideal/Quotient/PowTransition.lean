/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import TauCeti.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations

/-!
# The decreasing ideal-power filtration and quotient multiplication

The submodules `I ^ (n + 1) • ⊤` form a decreasing filtration (`Ideal.pow_succ_smul_top_antitone`).
For `a : R`, `Ideal.Quotient.mulSpanPowSucc a n : (R ⧸ (a ^ n)) →ₗ[R] (R ⧸ (a ^ (n + 1)))` is
multiplication by `a`, compatible with `Ideal.Quotient.factor` (`mulSpanPowSucc_factor`) and
injective when `a` is left-regular (`mulSpanPowSucc_injective`).
-/

public section

namespace Ideal

variable {A : Type*} [Ring A] (I : Ideal A)
variable (M : Type*) [AddCommGroup M] [Module A M]

/-- The `I`-adic filtration `n ↦ I^{n+1} M` of `M` is decreasing. -/
theorem pow_succ_smul_top_antitone :
    Antitone fun n : ℕ ↦ (I ^ (n + 1) • ⊤ : Submodule A M) :=
  fun _ _ h ↦ Submodule.pow_smul_top_le I M (Nat.add_le_add_right h 1)

end Ideal

namespace Ideal.Quotient

variable {R : Type*} [CommRing R]

/-- Multiplication by `a` induces an `R`-linear map
`(R ⧸ Ideal.span {a ^ n}) →ₗ[R] (R ⧸ Ideal.span {a ^ (n + 1)})`. -/
def mulSpanPowSucc (a : R) (n : ℕ) :
    (R ⧸ Ideal.span {a ^ n}) →ₗ[R] (R ⧸ Ideal.span {a ^ (n + 1)}) :=
  mulLeft a (by rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ'])

/-- Evaluating `Ideal.Quotient.mulSpanPowSucc a n` on the residue class of `r` gives the class of
`a * r`. -/
@[simp, grind =]
theorem mulSpanPowSucc_mk (a : R) (n : ℕ) (r : R) :
    mulSpanPowSucc a n (mk (Ideal.span {a ^ n}) r) = mk (Ideal.span {a ^ (n + 1)}) (a * r) :=
  mulLeft_mk a _ r

/-- Composing `Ideal.Quotient.mulSpanPowSucc a n` with the transition map from `R ⧸ (a ^ (n + 1))`
to `R ⧸ (a ^ n)` is scalar multiplication by `a`. -/
@[simp, grind =]
theorem mulSpanPowSucc_factor (a : R) (n : ℕ)
    (h : Ideal.span {a ^ (n + 1)} ≤ Ideal.span {a ^ n}) (q : R ⧸ Ideal.span {a ^ (n + 1)}) :
    mulSpanPowSucc a n (factor h q) = a • q :=
  mulLeft_factor a _ h q

/-- For any left-regular element `a` of a commutative ring `R`,
`Ideal.Quotient.mulSpanPowSucc a n` is injective. -/
theorem mulSpanPowSucc_injective {a : R} (ha : IsLeftRegular a) (n : ℕ) :
    Function.Injective (mulSpanPowSucc a n) :=
  mulLeft_injective _ (by rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ']) ha

end Ideal.Quotient
