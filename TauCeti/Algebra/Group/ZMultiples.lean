/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# `ℤ`-multiples of a non-torsion element

For an element `p` of an additive group that is not of finite additive order, the subgroup
`zmultiples p` of its `ℤ`-multiples is infinite cyclic: `n ↦ n • p` is an isomorphism
`ℤ ≃+ zmultiples p`. Mathlib provides `Int.intEquivOfZMultiplesEqTop` only when
`zmultiples p = ⊤`, and `zmultiplesEquivZMod` only in the finite-order case, so this fills the
remaining infinite-order gap.

## Main declarations

* `TauCeti.intEquivZMultiples`: the isomorphism `ℤ ≃+ zmultiples p` for a non-torsion `p`.
-/

namespace TauCeti

open AddSubgroup

variable {G : Type*} [AddGroup G] {p : G}

/-- For an element `p` of infinite additive order, the subgroup `zmultiples p` is infinite
cyclic, identified with `ℤ` by `n ↦ n • p`. -/
noncomputable def intEquivZMultiples (hp : ¬ IsOfFinAddOrder p) : ℤ ≃+ zmultiples p :=
  AddEquiv.ofBijective
    ({ toFun := fun n => ⟨n • p, mem_zmultiples_iff.2 ⟨n, rfl⟩⟩
       map_zero' := by ext; simp
       map_add' := fun n m => by ext; simp [add_zsmul] } : ℤ →+ zmultiples p)
    (by
      refine ⟨fun n m h => ?_, fun a => ?_⟩
      · exact injective_zsmul_iff_not_isOfFinAddOrder.2 hp (congrArg Subtype.val h)
      · obtain ⟨n, hn⟩ := mem_zmultiples_iff.1 a.2
        exact ⟨n, by ext; exact hn⟩)

@[simp]
theorem intEquivZMultiples_apply (hp : ¬ IsOfFinAddOrder p) (n : ℤ) :
    (intEquivZMultiples hp n : G) = n • p :=
  rfl

end TauCeti
