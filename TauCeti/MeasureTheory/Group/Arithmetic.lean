/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurable arithmetic operations on `SetLike` subobjects

A `SetLike` subobject closed under multiplication (`MulMemClass`) or inversion (`InvMemClass`)
inherits `MeasurableMul`, `MeasurableMul₂`, and `MeasurableInv` (and their additive counterparts)
from the ambient measurable space with respect to the subtype σ-algebra.

## Main declarations

* `MulMemClass.measurableMul`, `AddMemClass.measurableAdd`: separately measurable multiplication
  and addition on `MulMemClass` / `AddMemClass` subobjects.
* `MulMemClass.measurableMul₂`, `AddMemClass.measurableAdd₂`: jointly measurable multiplication and
  addition on `MulMemClass` / `AddMemClass` subobjects.
* `InvMemClass.measurableInv`, `NegMemClass.measurableNeg`: measurable inversion and negation on
  `InvMemClass` / `NegMemClass` subobjects.
-/

public section

@[to_additive]
instance MulMemClass.measurableMul {M S : Type*} [Mul M] [MeasurableSpace M] [MeasurableMul M]
    [SetLike S M] [MulMemClass S M] (s : S) : MeasurableMul s where
  measurable_const_mul c := (measurable_subtype_coe.const_mul (c : M)).subtype_mk
  measurable_mul_const c := (measurable_subtype_coe.mul_const (c : M)).subtype_mk

@[to_additive AddMemClass.measurableAdd₂]
instance MulMemClass.measurableMul₂ {M S : Type*} [Mul M] [MeasurableSpace M] [MeasurableMul₂ M]
    [SetLike S M] [MulMemClass S M] (s : S) : MeasurableMul₂ s where
  measurable_mul := (measurable_fst.subtype_val.mul measurable_snd.subtype_val).subtype_mk

@[to_additive]
instance InvMemClass.measurableInv {G S : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G]
    [SetLike S G] [InvMemClass S G] (s : S) : MeasurableInv s where
  measurable_inv := measurable_subtype_coe.inv.subtype_mk
