/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Faithful actions on spanning invariant subsets

An additive action commuting with scalar multiplication is determined on the span of an
invariant subset. Consequently, restricting a faithful action to a spanning invariant subset
remains faithful. The acting type needs no monoid structure.
-/

public section

namespace SubMulAction

variable {G R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DistribSMul G M] [SMulCommClass G R M] [FaithfulSMul G M]

/-- A faithful linear action remains faithful on any invariant subset spanning the module. -/
theorem faithfulSMul_of_span_eq_top (p : SubMulAction G M)
    (hp : Submodule.span R (p : Set M) = ⊤) : FaithfulSMul G p where
  eq_of_smul_eq_smul {g h} hgh := by
    apply eq_of_smul_eq_smul (α := M)
    intro x
    have heq : DistribSMul.toLinearMap R M g = DistribSMul.toLinearMap R M h :=
      LinearMap.ext_on hp fun y hy ↦ congrArg Subtype.val (hgh ⟨y, hy⟩)
    exact LinearMap.congr_fun heq x

end SubMulAction
