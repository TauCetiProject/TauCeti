/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Generator
public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear

/-!
# Time reversal of complex-linear strongly continuous groups

Complex linearity of the forward operators implies complex linearity at negative times by
invertibility. The complex generator of the reflected group is the negative of the original
complex generator, just as for the real generator.

## Main results

* `StronglyContinuousGroup.reflect_isComplexLinear`: time reversal preserves complex linearity.
* `StronglyContinuousGroup.map_smul_of_isComplexLinear`: forward complex linearity extends to all
  real times.
* `StronglyContinuousGroup.complexLinearOperator`: the operator at a real time, bundled as a
  complex continuous linear map.
* `StronglyContinuousGroup.complexLinearOperator_restrictScalars`,
  `StronglyContinuousGroup.complexLinearOperator_zero` and
  `StronglyContinuousGroup.complexLinearOperator_add`: the bundle restricts to `U t` over `ℝ` and
  satisfies the group laws.
* `StronglyContinuousGroup.toSemigroup_complexLinearOperator`: at nonnegative times it agrees
  with the complex-linear bundle of the forward semigroup.
* `StronglyContinuousGroup.reflect_complexGenerator`: time reversal negates the complex generator.
-/

public section

namespace TauCeti.Semigroups.StronglyContinuousGroup

open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If the forward operators of a strongly continuous group are complex linear, so are the
forward operators of its time reversal. -/
theorem reflect_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) : U.reflect.toSemigroup.IsComplexLinear := by
  apply (StronglyContinuousSemigroup.isComplexLinear_iff _).mpr
  intro t z x
  apply (U.bijective (t : ℝ)).injective
  have hcomm := hU.map_smul t z (U (-(t : ℝ)) x)
  simpa only [toSemigroup_apply, reflect_apply, U.map_apply_map_neg_apply] using hcomm.symm

/-- If the forward operators of a strongly continuous group are complex linear, then every
operator of the group is complex linear at all real times. -/
theorem map_smul_of_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ) (z : ℂ) (x : X) :
    U t (z • x) = z • U t x := by
  rcases le_or_gt 0 t with ht | ht
  · rw [← U.toSemigroup_realOperator_of_nonneg ht]
    exact hU.realOperator_map_smul t z x
  · have hneg : 0 ≤ -t := neg_nonneg.mpr ht.le
    have h := (U.reflect_isComplexLinear hU).realOperator_map_smul (-t) z x
    rwa [U.reflect.toSemigroup_realOperator_of_nonneg hneg, reflect_apply, neg_neg] at h

/-- The operator `U t` of a complex-linear strongly continuous group at a real time `t`, bundled
as a complex continuous linear map. -/
noncomputable def complexLinearOperator (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ) : X →L[ℂ] X where
  toFun := U t
  map_add' := (U t).map_add
  map_smul' := U.map_smul_of_isComplexLinear hU t
  cont := (U t).continuous

/-- The complex-linear bundle has the same pointwise action as the group operator. -/
@[simp]
theorem complexLinearOperator_apply (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ) (x : X) :
    U.complexLinearOperator hU t x = U t x :=
  (rfl)

/-- Restricting the complex-linear bundle to real scalars recovers the group operator. -/
@[simp]
theorem complexLinearOperator_restrictScalars (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ) :
    (U.complexLinearOperator hU t).restrictScalars ℝ = U t :=
  ContinuousLinearMap.ext fun x => U.complexLinearOperator_apply hU t x

/-- The complex-linear bundle at time `0` is the identity. -/
@[simp]
theorem complexLinearOperator_zero (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    U.complexLinearOperator hU 0 = ContinuousLinearMap.id ℂ X :=
  ContinuousLinearMap.ext fun x => by
    rw [U.complexLinearOperator_apply hU, U.map_zero_apply, ContinuousLinearMap.id_apply]

/-- The group law for the complex-linear bundle. -/
@[simp]
theorem complexLinearOperator_add (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (s t : ℝ) :
    U.complexLinearOperator hU (s + t) =
      (U.complexLinearOperator hU s).comp (U.complexLinearOperator hU t) :=
  ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, U.complexLinearOperator_apply hU,
      U.complexLinearOperator_apply hU, U.complexLinearOperator_apply hU, U.map_add_apply]

/-- At a nonnegative time, the complex-linear bundle of the forward semigroup agrees with the
complex-linear bundle of the group. -/
theorem toSemigroup_complexLinearOperator (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ≥0) :
    U.toSemigroup.complexLinearOperator hU t = U.complexLinearOperator hU t :=
  ContinuousLinearMap.ext fun x => by
    rw [StronglyContinuousSemigroup.complexLinearOperator_apply, toSemigroup_apply,
      complexLinearOperator_apply]

/-- Time reversal negates the complex generator of a complex-linear strongly continuous group.
The generator domain is preserved. -/
@[simp]
theorem reflect_complexGenerator [CompleteSpace X] (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    U.reflect.toSemigroup.complexGenerator (U.reflect_isComplexLinear hU) =
      -U.toSemigroup.complexGenerator hU := by
  apply LinearPMap.restrictScalars_injective ℝ
  rw [StronglyContinuousSemigroup.complexGenerator_restrictScalars,
    ← generator_def, reflect_generator, LinearPMap.restrictScalars_neg,
    StronglyContinuousSemigroup.complexGenerator_restrictScalars, generator_def]

end TauCeti.Semigroups.StronglyContinuousGroup
