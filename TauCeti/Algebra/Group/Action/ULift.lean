/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.ULift

/-!
# Faithful actions on universe lifts

The action of `R` on `ULift M`, defined componentwise through `ULift.down`, is faithful whenever
the action of `R` on `M` is. For instance `ℤ` acts faithfully on `ULift ℤ`, the native integral
coefficients of singular homology.
-/

public section

universe u v w

namespace ULift

variable {R : Type u} {M : Type v}

/-- `R` acts faithfully on `ULift M` whenever it acts faithfully on `M`. -/
@[to_additive
  /-- `R` acts faithfully on `ULift M` by addition whenever it acts faithfully on `M`. -/]
instance faithfulSMul [SMul R M] [FaithfulSMul R M] : FaithfulSMul R (ULift.{w} M) :=
  ⟨fun h ↦ FaithfulSMul.eq_of_smul_eq_smul fun m ↦ congrArg ULift.down (h (ULift.up m))⟩

end ULift
