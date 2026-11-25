/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Faithful actions on invariant subsets

Restricting a faithful action to an invariant subset need not stay faithful. This file records
two cases in which it does.

The stabilizer of a point `a` in a faithful group action acts faithfully on the complement of
`a`, Mathlib's `SubMulAction.ofStabilizer`: its elements are determined by their values away from
`a`, since they all fix `a`.

An additive action commuting with scalar multiplication is determined on the span of an
invariant subset. Consequently, restricting a faithful action to a spanning invariant subset
remains faithful. The acting type needs no monoid structure.

The units of a ring without zero divisors act freely on the nonzero vectors of a torsion-free
module, Mathlib's `Units.nonZeroSubMul`: `a • v = b • v` with `v ≠ 0` forces `a = b`. This covers
the units of a division ring acting on the nonzero vectors of any module.
-/

public section

namespace SubMulAction

/-- The stabilizer of a point in a faithful group action acts faithfully on the complement of
that point. -/
instance ofStabilizer.faithfulSMul {G α : Type*} [Group G] [MulAction G α] [FaithfulSMul G α]
    (a : α) : FaithfulSMul (MulAction.stabilizer G a) (ofStabilizer G a) where
  eq_of_smul_eq_smul {g h} hgh := by
    refine Subtype.ext (eq_of_smul_eq_smul (α := α) fun x ↦ ?_)
    by_cases hx : x = a
    · rw [hx, MulAction.mem_stabilizer_iff.mp g.property, MulAction.mem_stabilizer_iff.mp
        h.property]
    · simpa only [val_smul, MulAction.subgroup_smul_def] using
        congrArg Subtype.val (hgh ⟨x, (mem_ofStabilizer_iff G a).mpr hx⟩)

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

namespace Units

variable {R V : Type*} [Ring R] [IsCancelMulZero R] [AddCommGroup V] [Module R V]
  [Module.IsTorsionFree R V]

/-- The units of a ring without zero divisors act freely on the nonzero vectors of a torsion-free
module, for instance the units of a division ring on the nonzero vectors of any module. -/
instance isCancelSMul_nonZero : IsCancelSMul Rˣ {v : V // v ≠ 0} where
  left_cancel' a v w h := by simpa using h
  right_cancel' a b v h := Units.ext <| smul_left_injective R v.property <| by
    simpa [Units.smul_def] using congrArg Subtype.val h

end Units
