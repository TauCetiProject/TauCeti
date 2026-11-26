/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Measurable arithmetic operations on subobjects and groups

On an additive group, measurability of subtraction gives measurability of translations
(`TauCeti.measurableAdd_of_measurableSub`).

A `SetLike` subobject closed under multiplication (`MulMemClass`) or inversion (`InvMemClass`)
inherits `MeasurableMul`, `MeasurableMul₂`, and `MeasurableInv` (and their additive counterparts)
from the ambient measurable space with respect to the subtype σ-algebra. Likewise the restriction of
a jointly measurable action to an invariant subset (a `SubMulAction`) is jointly measurable.

## Main declarations

* `MulMemClass.measurableMul`, `AddMemClass.measurableAdd`: separately measurable multiplication
  and addition on `MulMemClass` / `AddMemClass` subobjects.
* `MulMemClass.measurableMul₂`, `AddMemClass.measurableAdd₂`: jointly measurable multiplication and
  addition on `MulMemClass` / `AddMemClass` subobjects.
* `InvMemClass.measurableInv`, `NegMemClass.measurableNeg`: measurable inversion and negation on
  `InvMemClass` / `NegMemClass` subobjects.
* `SubMulAction.instMeasurableSMul₂`, `SubAddAction.instMeasurableVAdd₂`: the jointly measurable
  action on a `SubMulAction` / `SubAddAction`.
* `TauCeti.measurableAdd_of_measurableSub`: on an additive group, separately measurable
  subtraction gives separately measurable addition.
* `TauCeti.measurableAdd₂_of_measurableSub₂`: on an additive group, jointly measurable subtraction
  gives jointly measurable addition.
* `TauCeti.measurableEmbedding_divLeft₀`: division of a nonzero constant by the variable is a
  measurable embedding on a group with zero.
-/

public section

@[to_additive]
instance MulMemClass.measurableMul {M S : Type*} [Mul M] [MeasurableSpace M] [MeasurableMul M]
    [SetLike S M] [MulMemClass S M] (s : S) : MeasurableMul s where
  measurable_const_mul c := (measurable_subtypeVal.const_mul (c : M)).subtype_mk
  measurable_mul_const c := (measurable_subtypeVal.mul_const (c : M)).subtype_mk

@[to_additive AddMemClass.measurableAdd₂]
instance MulMemClass.measurableMul₂ {M S : Type*} [Mul M] [MeasurableSpace M] [MeasurableMul₂ M]
    [SetLike S M] [MulMemClass S M] (s : S) : MeasurableMul₂ s where
  measurable_mul := (measurable_fst.subtypeVal.mul measurable_snd.subtypeVal).subtype_mk

@[to_additive]
instance InvMemClass.measurableInv {G S : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G]
    [SetLike S G] [InvMemClass S G] (s : S) : MeasurableInv s where
  measurable_inv := measurable_subtypeVal.inv.subtype_mk

/-- The restriction of a jointly measurable action to an invariant subset is jointly
measurable. -/
@[to_additive SubAddAction.instMeasurableVAdd₂
/-- The restriction of a jointly measurable additive action to an invariant subset is
jointly measurable. -/]
instance SubMulAction.instMeasurableSMul₂ {G X : Type*} [SMul G X] [MeasurableSpace G]
    [MeasurableSpace X] [MeasurableSMul₂ G X] (p : SubMulAction G X) : MeasurableSMul₂ G p :=
  ⟨(measurable_smul.comp (measurable_fst.prodMk (measurable_subtypeVal.comp
    measurable_snd))).subtype_mk⟩

namespace TauCeti

/-- On an additive group, separately measurable subtraction gives separately measurable
addition. -/
theorem measurableAdd_of_measurableSub {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableSub G] : MeasurableAdd G :=
  ⟨fun c ↦ by
      have h : Measurable fun x : G ↦ c - (0 - x) :=
        (measurable_const_sub c).comp (measurable_const_sub 0)
      simpa using h,
    fun c ↦ by
      have h : Measurable fun x : G ↦ x - -c := measurable_sub_const (-c)
      simpa using h⟩

/-- On an additive group, jointly measurable subtraction gives jointly measurable addition, by
`x + y = x - (0 - y)`. -/
theorem measurableAdd₂_of_measurableSub₂ {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableSub₂ G] : MeasurableAdd₂ G :=
  ⟨by
    have h : Measurable fun p : G × G ↦ p.1 - (0 - p.2) :=
      measurable_fst.sub (measurable_const.sub measurable_snd)
    simpa using h⟩

/-- On a group with zero with measurable left multiplications and inversion, division of a
nonzero constant by the variable is a measurable embedding. -/
theorem measurableEmbedding_divLeft₀ {G₀ : Type*} [GroupWithZero G₀] [MeasurableSpace G₀]
    [MeasurableConstSMul G₀ G₀] [MeasurableInv G₀] {c : G₀} (hc : c ≠ 0) :
    MeasurableEmbedding (c / ·) := by
  simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
    (measurableEmbedding_const_smul₀ (α := G₀) hc).comp measurableEmbedding_inv

end TauCeti
