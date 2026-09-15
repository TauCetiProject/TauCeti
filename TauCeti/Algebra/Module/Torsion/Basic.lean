/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in a subgroup of finite order

A subgroup of an additive commutative group consists of torsion points as soon as it is finite:
its cardinality annihilates each of its elements, so a subgroup `H` is contained in the
`Nat.card H`-torsion subgroup. For finite `H` this says that a subgroup with `n` elements is
`n`-torsion; for infinite `H` one has `Nat.card H = 0` and the statement is the trivial
`H ≤ A[0]`.

## Main results

* `AddSubgroup.le_torsionBy_natCard`: a subgroup `H` is contained in the `Nat.card H`-torsion
  subgroup.
-/

public section

namespace AddSubgroup

/-- A subgroup `H` consists of `Nat.card H`-torsion points; for finite `H` this is the statement
that a subgroup with `n` elements is `n`-torsion, and for infinite `H` it is the trivial
`H ≤ A[0]`. -/
theorem le_torsionBy_natCard {A : Type*} [AddCommGroup A] {H : AddSubgroup A} :
    H ≤ A[(Nat.card H : ℤ)] := fun x hx ↦
  torsionBy.nsmul_iff.mpr <| by
    have : Nat.card H • (⟨x, hx⟩ : H) = 0 := card_nsmul_eq_zero'
    exact congrArg Subtype.val this

end AddSubgroup
