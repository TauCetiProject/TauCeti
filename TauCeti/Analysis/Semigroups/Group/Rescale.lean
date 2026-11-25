/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Generator
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Semigroups.Identity

/-!
# Rescaling the time of a strongly continuous group

For a C₀-group `U` and a real number `s`, the **rescaled group** `U.rescale s` runs `U` at speed
`s`: it is the C₀-group `t ↦ U (s * t)`. Every real `s` is allowed, including negative ones, which
also reverse time (`U.rescale (-1)` is the time reversal `U.reflect`), and `0`, which gives the
constant group `t ↦ 1`.

For `s ≠ 0` the rescaled group has the same generator domain and the generator `s • A`, where `A`
is the generator of `U`: the orbit `t ↦ U (s * t) x` of a domain vector has derivative `s • A x`
at `0` by the chain rule, and rescaling by `s⁻¹` undoes rescaling by `s`. For `s = 0` the generator
is the zero operator on the whole space. The two-sided derivative of the orbits of a C₀-group
(`TauCeti.Semigroups.StronglyContinuousGroup.hasDerivAt_zero`) is what makes negative speeds
accessible, so the laws for `s ≠ 0` assume completeness.

The rescaled group is how a strongly continuous representation of a Lie group sees the scaling of
its Lie algebra: the one-parameter group of `s • X` is the one-parameter group of `X` rescaled by
`s`.

## Main definitions

* `TauCeti.Semigroups.StronglyContinuousGroup.rescale`: the C₀-group `t ↦ U (s * t)`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.rescale_rescale`: rescaling twice multiplies the
  speeds.
* `TauCeti.Semigroups.StronglyContinuousGroup.rescale_neg_one`: rescaling by `-1` is time
  reversal.
* `TauCeti.Semigroups.StronglyContinuousGroup.rescale_reflect` and
  `TauCeti.Semigroups.StronglyContinuousGroup.reflect_rescale`: time reversal turns rescaling by
  `s` into rescaling by `-s`.
* `TauCeti.Semigroups.StronglyContinuousGroup.rescale_domain`: for `s ≠ 0`, rescaling does not
  change the generator domain.
* `TauCeti.Semigroups.StronglyContinuousGroup.rescale_generator`: for `s ≠ 0`, the generator of
  `t ↦ U (s * t)` is `s • A`.
* `TauCeti.Semigroups.StronglyContinuousGroup.rescale_zero_generator` and
  `TauCeti.Semigroups.StronglyContinuousGroup.rescale_zero_domain`: the generator of the
  constant group `U.rescale 0` is `0`, defined on the whole space.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups).
-/

public section

noncomputable section

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The C₀-group `t ↦ U (s * t)`: the group `U` run at speed `s`. -/
def rescale (U : StronglyContinuousGroup X) (s : ℝ) : StronglyContinuousGroup X where
  toFun t := U (s * t)
  map_zero' := by rw [mul_zero, U.map_zero]
  map_add' a b := by rw [mul_add, U.map_add]
  continuousAt_zero' x :=
    ContinuousAt.comp_of_eq (U.continuousAt_zero' x)
      (by fun_prop : Continuous fun t : ℝ => s * t).continuousAt (mul_zero s)

@[simp]
theorem rescale_apply (U : StronglyContinuousGroup X) (s t : ℝ) : U.rescale s t = U (s * t) := by
  rw [rescale]
  rfl

/-- Rescaling by `1` does nothing. -/
@[simp]
theorem rescale_one (U : StronglyContinuousGroup X) : U.rescale 1 = U :=
  ext fun t => by rw [rescale_apply, one_mul]

/-- Rescaling twice multiplies the speeds. -/
@[simp]
theorem rescale_rescale (U : StronglyContinuousGroup X) (s r : ℝ) :
    (U.rescale s).rescale r = U.rescale (s * r) :=
  ext fun t => by rw [rescale_apply, rescale_apply, rescale_apply, mul_assoc]

/-- Rescaling by `-1` is time reversal. -/
@[simp]
theorem rescale_neg_one (U : StronglyContinuousGroup X) : U.rescale (-1) = U.reflect :=
  ext fun t => by rw [rescale_apply, reflect_apply, neg_one_mul]

/-- Rescaling the time reversal by `s` is rescaling by `-s`. -/
@[simp]
theorem rescale_reflect (U : StronglyContinuousGroup X) (s : ℝ) :
    U.reflect.rescale s = U.rescale (-s) :=
  ext fun t => by rw [rescale_apply, reflect_apply, rescale_apply, neg_mul]

/-- The time reversal of the group rescaled by `s` is the group rescaled by `-s`. -/
@[simp]
theorem reflect_rescale (U : StronglyContinuousGroup X) (s : ℝ) :
    (U.rescale s).reflect = U.rescale (-s) :=
  ext fun t => by rw [reflect_apply, rescale_apply, rescale_apply, mul_neg, neg_mul]

/-- The constant group `U.rescale 0`, restricted to nonnegative times, is the identity
semigroup. -/
private theorem rescale_zero_toSemigroup (U : StronglyContinuousGroup X) :
    (U.rescale 0).toSemigroup = StronglyContinuousSemigroup.id X :=
  StronglyContinuousSemigroup.ext fun t => by
    rw [toSemigroup_apply, rescale_apply, zero_mul, U.map_zero,
      StronglyContinuousSemigroup.id_apply]

/-- The generator of the constant group `U.rescale 0` is the zero operator, defined on the whole
space. -/
@[simp]
theorem rescale_zero_generator (U : StronglyContinuousGroup X) : (U.rescale 0).generator = 0 := by
  rw [generator_def, rescale_zero_toSemigroup, StronglyContinuousSemigroup.id_generator_eq_zero]

/-- The generator domain of the constant group `U.rescale 0` is the whole space. -/
@[simp]
theorem rescale_zero_domain (U : StronglyContinuousGroup X) : (U.rescale 0).domain = ⊤ := by
  rw [domain_def, rescale_zero_toSemigroup, StronglyContinuousSemigroup.id_domain_eq_top]

variable [CompleteSpace X]

/-- The orbit of `U.rescale s` through a domain vector `x` of `U` has derivative `s • A x` at `0`,
where `A` is the generator of `U`. -/
private theorem hasDerivAt_rescale_zero (U : StronglyContinuousGroup X) (s : ℝ)
    (x : U.domain) :
    HasDerivAt (fun t : ℝ => U.rescale s t (x : X))
      (s • U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩) 0 := by
  have h := (U.hasDerivAt_zero x).scomp_of_eq 0 (HasDerivAt.const_mul s (hasDerivAt_id (0 : ℝ)))
    (mul_zero s).symm
  simpa only [mul_one, Function.comp_def, id, rescale_apply] using h

/-- The generator domain of `U` is contained in that of every rescaled group. -/
private theorem domain_le_rescale_domain (U : StronglyContinuousGroup X) (s : ℝ) :
    U.domain ≤ (U.rescale s).domain :=
  fun x hx => (U.rescale s).mem_domain_of_hasDerivAt_zero (U.hasDerivAt_rescale_zero s ⟨x, hx⟩)

/-- **Rescaling by a nonzero speed does not change the generator domain.** -/
@[simp]
theorem rescale_domain (U : StronglyContinuousGroup X) {s : ℝ} (hs : s ≠ 0) :
    (U.rescale s).domain = U.domain := by
  refine le_antisymm ?_ (U.domain_le_rescale_domain s)
  have h := (U.rescale s).domain_le_rescale_domain s⁻¹
  rwa [rescale_rescale, mul_inv_cancel₀ hs, rescale_one] at h

/-- **The generator of a rescaled group.** For `s ≠ 0` the generator of `t ↦ U (s * t)` is
`s • A`, on the domain of the generator `A` of `U`. -/
@[simp]
theorem rescale_generator (U : StronglyContinuousGroup X) {s : ℝ} (hs : s ≠ 0) :
    (U.rescale s).generator = s • U.generator := by
  refine LinearPMap.ext ?_ fun x _ hx => ?_
  · rw [generator_domain, LinearPMap.smul_domain, generator_domain, U.rescale_domain hs]
  · rw [LinearPMap.smul_domain, generator_domain] at hx
    rw [LinearPMap.smul_apply]
    exact (U.rescale s).generator_eq_of_hasDerivAt_zero (U.hasDerivAt_rescale_zero s ⟨x, hx⟩)

end StronglyContinuousGroup

end TauCeti.Semigroups
