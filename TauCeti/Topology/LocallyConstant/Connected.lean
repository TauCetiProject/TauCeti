/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Locally constant functions on a connected space

On a connected topological space `X`, every locally constant function `X → Y` is constant, and
since `X` is nonempty the constant value is uniquely determined. Thus `LocallyConstant.const X`
is a bijection `Y ≃ LocallyConstant X Y`, and upgrades to multiplicative, additive, and ring
equivalences whenever `Y` carries the corresponding algebraic structure.

## Main definitions

* `LocallyConstant.constEquiv`: `Y ≃ LocallyConstant X Y` on a connected space `X`.
* `LocallyConstant.constMulEquiv` and `LocallyConstant.constAddEquiv`: the multiplicative and
  additive equivalences.
* `LocallyConstant.constRingEquiv`: `Y ≃+* LocallyConstant X Y` for a type `Y` with addition
  and multiplication.
-/

public section

namespace LocallyConstant

variable (X Y : Type*) [TopologicalSpace X] [ConnectedSpace X]

/-- On a connected space, every locally constant function is constant, giving an equivalence
between `Y` and `LocallyConstant X Y`. -/
noncomputable def constEquiv : Y ≃ LocallyConstant X Y where
  toFun := const X
  invFun f := f (Classical.arbitrary X)
  left_inv _ := rfl
  right_inv f := (f.eq_const (Classical.arbitrary X)).symm

@[simp]
theorem constEquiv_apply (y : Y) : constEquiv X Y y = const X y :=
  (rfl)

theorem constEquiv_symm_apply (f : LocallyConstant X Y) (x : X) :
    (constEquiv X Y).symm f = f x :=
  f.apply_eq_of_preconnectedSpace _ x

/-- On a connected space, constant functions identify `Y` multiplicatively with
`LocallyConstant X Y`. -/
@[to_additive
/-- On a connected space, constant functions identify `Y` additively with
`LocallyConstant X Y`. -/]
noncomputable def constMulEquiv [Mul Y] : Y ≃* LocallyConstant X Y where
  toEquiv := constEquiv X Y
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
theorem constMulEquiv_apply [Mul Y] (y : Y) : constMulEquiv X Y y = const X y :=
  (rfl)

@[to_additive]
theorem constMulEquiv_symm_apply [Mul Y] (f : LocallyConstant X Y) (x : X) :
    (constMulEquiv X Y).symm f = f x :=
  constEquiv_symm_apply X Y f x

/-- On a connected space, constant functions give a ring equivalence `Y ≃+* LocallyConstant X Y`. -/
noncomputable def constRingEquiv [Add Y] [Mul Y] : Y ≃+* LocallyConstant X Y where
  toEquiv := constEquiv X Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem constRingEquiv_apply [Add Y] [Mul Y] (y : Y) :
    constRingEquiv X Y y = const X y :=
  (rfl)

theorem constRingEquiv_symm_apply [Add Y] [Mul Y] (f : LocallyConstant X Y) (x : X) :
    (constRingEquiv X Y).symm f = f x :=
  constEquiv_symm_apply X Y f x

@[simp]
theorem constRingEquiv_toRingHom [NonAssocSemiring Y] :
    (constRingEquiv X Y : Y →+* LocallyConstant X Y) = constRingHom :=
  RingHom.ext fun _ ↦ (rfl)

end LocallyConstant
