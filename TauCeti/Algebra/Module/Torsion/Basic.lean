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
the order of the subgroup annihilates each of its elements, so a subgroup with `n` elements is
contained in the `n`-torsion subgroup `A[n]`.

## Main results

* `AddSubgroup.le_torsionBy_of_natCard_eq`: a subgroup with `n` elements is contained in the
  `n`-torsion subgroup.
-/

public section

namespace AddSubgroup

/-- A subgroup with `n` elements consists of `n`-torsion points. -/
theorem le_torsionBy_of_natCard_eq {A : Type*} [AddCommGroup A] {n : ℕ} {H : AddSubgroup A}
    (hH : Nat.card H = n) : H ≤ A[(n : ℤ)] := fun x hx ↦
  torsionBy.nsmul_iff.mpr <| by
    have : Nat.card H • (⟨x, hx⟩ : H) = 0 := card_nsmul_eq_zero'
    rw [hH] at this
    exact congrArg Subtype.val this

end AddSubgroup
