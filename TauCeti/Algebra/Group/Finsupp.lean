/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.GroupTheory.Divisible
public import Mathlib.GroupTheory.PGroup

import Mathlib.Data.Finsupp.SMul

/-!
# Additive group properties of finitely supported functions

Coercion to functions is an injective additive monoid homomorphism `(ι →₀ M) →+ (ι → M)`, so
finitely supported functions have trivial additive units whenever their values do. For a
commutative `M` this says that zero-sum-freeness passes to `ι →₀ M`; it is the coefficientwise
form of zero-sum-freeness for monoid algebras and polynomials.

Finitely supported functions also inherit divisibility by natural numbers and the property of
being an additive `p`-group from their values (`IsAddPGroup.finsupp`).
-/

public section

namespace TauCeti

/-- Finitely supported functions have trivial additive units when their values do. -/
instance instSubsingletonAddUnitsFinsupp {ι M : Type*} [AddMonoid M]
    [Subsingleton (AddUnits M)] : Subsingleton (AddUnits (ι →₀ M)) :=
  (AddUnits.map_injective (f := Finsupp.coeFnAddHom) DFunLike.coe_injective).subsingleton

/-- Finitely supported functions into an additive `p`-group form an additive `p`-group. -/
theorem _root_.IsAddPGroup.finsupp {ι M : Type*} [AddCommGroup M] {p : ℕ}
    (hM : IsAddPGroup p M) : IsAddPGroup p (ι →₀ M) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add i a x _ _ ih =>
    obtain ⟨m, hm⟩ := hM a
    obtain ⟨n, hn⟩ := ih
    refine ⟨m + n, ?_⟩
    rw [smul_add, Finsupp.smul_single, pow_add]
    rw [mul_comm (p ^ m) (p ^ n), ← smul_smul, hm, smul_zero, Finsupp.single_zero,
      zero_add]
    rw [mul_comm, ← smul_smul, hn, smul_zero]

/-- Finitely supported functions into a divisible additive monoid are divisible. -/
noncomputable instance instDivisibleByNatFinsupp {ι M : Type*} [AddMonoid M] [DivisibleBy M ℕ] :
    DivisibleBy (ι →₀ M) ℕ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x ↦ by
    obtain ⟨y, hy⟩ := Finsupp.mapRange_surjective (fun a : M ↦ n • a) (smul_zero n)
      (DivisibleBy.surjective_smul M ℕ hn) x
    exact ⟨y, by ext i; exact congrArg (fun f : ι →₀ M ↦ f i) hy⟩

end TauCeti
