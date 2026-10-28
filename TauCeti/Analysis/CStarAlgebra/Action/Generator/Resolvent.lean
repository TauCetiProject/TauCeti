/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic
import TauCeti.Analysis.Semigroups.Resolvent.Complex

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

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
second edition, Section 5.3, for generators of one-parameter automorphism groups.
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

private theorem reflect_isComplexLinear (α : CStarAction (Multiplicative ℝ) A) :
    α.toStronglyContinuousGroup.reflect.toSemigroup.IsComplexLinear := by
  apply (StronglyContinuousSemigroup.isComplexLinear_iff _).mpr
  intro t z a
  simp [StronglyContinuousGroup.reflect_apply, map_smul]

private theorem reflect_complexGenerator (α : CStarAction (Multiplicative ℝ) A) :
    α.toStronglyContinuousGroup.reflect.toSemigroup.complexGenerator
      α.reflect_isComplexLinear = -α.generator := by
  apply LinearPMap.restrictScalars_injective ℝ
  rw [StronglyContinuousSemigroup.complexGenerator_restrictScalars,
    ← StronglyContinuousGroup.generator_def, StronglyContinuousGroup.reflect_generator,
    LinearPMap.restrictScalars_neg, generator_restrictScalars]

private theorem reflected_resolvent (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re < 0) :
    LinearPMap.IsResolventAt α.generator z
      (-LinearPMap.resolvent
        (α.toStronglyContinuousGroup.reflect.toSemigroup.complexGenerator
          α.reflect_isComplexLinear) (-z)) := by
  have hmem := α.toStronglyContinuousGroup.reflect.toSemigroup.mem_resolventSet_complexGenerator
    α.reflect_isComplexLinear α.generator_group_growthBound.reflect.toSemigroup
    (lambda := -z) (by simpa using neg_pos.mpr hz)
  rw [α.reflect_complexGenerator] at hmem ⊢
  have h := LinearPMap.isResolventAt_resolvent hmem
  refine ⟨fun a => α.generator.domain.neg_mem (h.mem_domain a), fun a => ?_, fun a => ?_⟩
  · have hg : α.generator ⟨-LinearPMap.resolvent (-α.generator) (-z) a,
        α.generator.domain.neg_mem (h.mem_domain a)⟩ =
        -α.generator ⟨LinearPMap.resolvent (-α.generator) (-z) a, h.mem_domain a⟩ :=
      α.generator.map_neg ⟨_, h.mem_domain a⟩
    simpa only [neg_apply, hg, LinearPMap.neg_apply, neg_smul,
      smul_neg, sub_neg_eq_add] using h.smul_sub_apply a
  · have heq : (-z) • (a : A) - (-α.generator) ⟨a, a.property⟩ =
        -(z • (a : A) - α.generator a) := by
      simp only [LinearPMap.neg_apply, neg_smul]
      abel
    have hleft := h.apply_smul_sub ⟨a, a.property⟩
    rw [heq, map_neg] at hleft
    exact hleft

/-- Every parameter off the imaginary axis belongs to the generator's complex resolvent set. -/
theorem mem_resolventSet_generator (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re ≠ 0) : z ∈ LinearPMap.resolventSet α.generator := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · exact (α.reflected_resolvent hz).mem_resolventSet
  · rw [generator_def]
    exact α.toStronglyContinuousGroup.toSemigroup.mem_resolventSet_complexGenerator
      α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound.toSemigroup hz

/-- In the right half-plane the resolvent is the forward Laplace integral of the action. -/
theorem resolvent_generator_apply_of_re_pos (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : 0 < z.re) (a : A) :
    LinearPMap.resolvent α.generator z a =
      ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(z * t)) • α (Multiplicative.ofAdd t) a := by
  rw [generator_def]
  rw [α.toStronglyContinuousGroup.toSemigroup.resolvent_complexGenerator_apply
    α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound.toSemigroup hz]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [α.toStronglyContinuousGroup.toSemigroup_realOperator_of_nonneg (le_of_lt ht),
    toStronglyContinuousGroup_apply]

/-- In the left half-plane the resolvent is the negative backward Laplace integral. -/
theorem resolvent_generator_apply_of_re_neg (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re < 0) (a : A) :
    LinearPMap.resolvent α.generator z a =
      -(∫ t in Set.Ioi (0 : ℝ), Complex.exp (z * t) • α (Multiplicative.ofAdd (-t)) a) := by
  rw [LinearPMap.resolvent_eq_of_isResolventAt (α.reflected_resolvent hz),
    neg_apply]
  rw [α.toStronglyContinuousGroup.reflect.toSemigroup.resolvent_complexGenerator_apply
    α.reflect_isComplexLinear α.generator_group_growthBound.reflect.toSemigroup
    (by simpa using neg_pos.mpr hz)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [α.toStronglyContinuousGroup.reflect_toSemigroup_realOperator_of_nonneg (le_of_lt ht),
    toStronglyContinuousGroup_apply, neg_mul, neg_neg]

/-- The norm of the resolvent is at most the reciprocal distance to the imaginary axis. -/
theorem norm_resolvent_generator_le (α : CStarAction (Multiplicative ℝ) A)
    {z : ℂ} (hz : z.re ≠ 0) :
    ‖LinearPMap.resolvent α.generator z‖ ≤ 1 / |z.re| := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · rw [LinearPMap.resolvent_eq_of_isResolventAt (α.reflected_resolvent hz), norm_neg,
      abs_of_neg hz]
    simpa using α.toStronglyContinuousGroup.reflect.toSemigroup.norm_resolvent_complexGenerator_le
      α.reflect_isComplexLinear α.generator_group_growthBound.reflect.toSemigroup
      (lambda := -z) (by simpa using neg_pos.mpr hz)
  · rw [generator_def, abs_of_pos hz]
    simpa using α.toStronglyContinuousGroup.toSemigroup.norm_resolvent_complexGenerator_le
      α.toStronglyContinuousGroup_isComplexLinear α.generator_group_growthBound.toSemigroup hz

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
