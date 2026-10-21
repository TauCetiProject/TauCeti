/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Basic instances for the `p`-adic numbers

This file provides a direct instance for the nontriviality of `ℚ_[p]`, already implied by
its field structure, and an instance expressing that `2` is invertible. These instances support
finite-dimensional constructions and algebraic trace and norm calculations over the `p`-adic field.

It also records that the scalar action of `ℤ_[p]` on `ℚ_[p]` multiplies norms,
`‖a • x‖ = ‖a‖ * ‖x‖`. In particular the action is contractive, so `ℚ_[p]` itself is a
coefficient ring for Mathlib's Mahler isometry `PadicInt.mahlerEquiv` and for the Amice transform
of measures on `ℤ_p`.
-/

public section

noncomputable section

namespace TauCeti

/-- A direct instance of the existing fact that the `p`-adic field has distinct zero and one. -/
-- Avoid backtracking through Henselian-ring instances during rank and freeness synthesis.
instance (p : ℕ) [Fact (Nat.Prime p)] : Nontrivial ℚ_[p] :=
  @DivisionRing.toNontrivial _ (instFieldPadic p).toDivisionRing

/-- Two is invertible in the `p`-adic field, including when `p = 2`. -/
instance instInvertibleTwoPadic (p : ℕ) [Fact (Nat.Prime p)] : Invertible (2 : ℚ_[p]) :=
  invertibleOfNonzero two_ne_zero

/-- The scalar action of `ℤ_[p]` on `ℚ_[p]` is multiplication by the inclusion, so it multiplies
norms. This also provides the contractive action `IsBoundedSMul ℤ_[p] ℚ_[p]`. -/
instance normSMulClass_padicInt_padic (p : ℕ) [Fact (Nat.Prime p)] :
    NormSMulClass ℤ_[p] ℚ_[p] :=
  ⟨fun a x ↦ by rw [Algebra.smul_def, norm_mul, PadicInt.algebraMap_apply, PadicInt.norm_coe]⟩

end TauCeti
