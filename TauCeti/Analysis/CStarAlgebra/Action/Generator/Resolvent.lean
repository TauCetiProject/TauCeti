/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic
import TauCeti.Analysis.Semigroups.Group.Resolvent

/-!
# Resolvents of generators of C⋆-algebra actions

The generator of a point-norm continuous real C⋆-action has every complex parameter
with nonzero real part in its resolvent set. Its resolvent is the forward Laplace
integral in the right half-plane and the negative backward Laplace integral in the
left half-plane, with norm bounded by the reciprocal of the absolute real part.
Taking star conjugates the spectral parameter.

The Laplace integrals use the complex semigroup resolvent of
`StronglyContinuousSemigroup.resolvent_complexGenerator_apply`; time reversal supplies
the left half-plane. These formulas apply also to nonunital and zero algebras.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*,
second edition, Section 3.1, Proposition 3.1.6 and the following group discussion
(pp. 166--169), for the Laplace resolvent formula and growth bound. Section 3.2.4,
Theorem 3.2.50(A1), gives the generator's star identity; resolvent star compatibility
then follows from the inverse identities.
-/

public section

noncomputable section

open MeasureTheory
open TauCeti.Semigroups

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A]

private theorem generator_group_growthBound (α : CStarAction (Multiplicative ℝ) A) :
    α.toStronglyContinuousGroup.HasGrowthBound 0 1 := by
  apply (StronglyContinuousGroup.hasGrowthBound_zero_one_iff _).mpr
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simp only [one_mul, toStronglyContinuousGroup_apply, StarAlgEquiv.norm_map, le_refl]

/-- Every parameter off the imaginary axis belongs to the generator's complex resolvent set. -/
theorem mem_resolventSet_generator (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re ≠ 0) : z ∈ LinearPMap.resolventSet α.generator := by
  rw [generator_def]
  exact α.toStronglyContinuousGroup.mem_resolventSet_complexGenerator
    α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound
    (abs_pos.mpr hz)

/-- In the right half-plane the resolvent is the forward Laplace integral of the action. -/
theorem resolvent_generator_apply_of_re_pos (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : 0 < z.re) (a : A) :
    LinearPMap.resolvent α.generator z a =
      ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(z * t)) • α (Multiplicative.ofAdd t) a := by
  rw [generator_def,
    α.toStronglyContinuousGroup.resolvent_complexGenerator_apply_of_re_gt
      α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound hz]
  simp only [toStronglyContinuousGroup_apply]

/-- In the left half-plane the resolvent is the negative backward Laplace integral. -/
theorem resolvent_generator_apply_of_re_neg (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re < 0) (a : A) :
    LinearPMap.resolvent α.generator z a =
      -(∫ t in Set.Ioi (0 : ℝ), Complex.exp (z * t) • α (Multiplicative.ofAdd (-t)) a) := by
  rw [generator_def,
    α.toStronglyContinuousGroup.resolvent_complexGenerator_apply_of_re_lt_neg
      α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound
      (by simpa using hz)]
  simp only [toStronglyContinuousGroup_apply]

/-- The norm of the resolvent is at most the reciprocal distance to the imaginary axis. -/
theorem norm_resolvent_generator_le (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re ≠ 0) :
    ‖LinearPMap.resolvent α.generator z‖ ≤ 1 / |z.re| := by
  rw [generator_def]
  simpa using α.toStronglyContinuousGroup.norm_resolvent_complexGenerator_le
    α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound (abs_pos.mpr hz)

/-- Taking star of a resolvent value conjugates the spectral parameter. -/
@[simp]
theorem star_resolvent_generator (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re ≠ 0) (a : A) :
    star (LinearPMap.resolvent α.generator z a) =
      LinearPMap.resolvent α.generator (star z) (star a) := by
  have hmem := α.mem_resolventSet_generator hz
  have hc := α.mem_resolventSet_generator (z := star z) (by simpa using hz)
  have hr := LinearPMap.smul_sub_apply_resolvent hmem a
  have hstar := congrArg star hr
  rw [star_sub, star_smul, ← α.generator_star] at hstar
  have hleft := LinearPMap.resolvent_smul_sub_apply hc
    ⟨star (LinearPMap.resolvent α.generator z a),
      α.star_mem_generator_domain (LinearPMap.resolvent_mem_domain hmem a)⟩
  rw [hstar] at hleft
  exact hleft.symm

end TauCeti.CStarAction
