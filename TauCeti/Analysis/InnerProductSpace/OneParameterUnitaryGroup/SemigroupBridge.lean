/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Basic
public import TauCeti.Analysis.Semigroups.Generator.Basic

/-!
# A one-parameter unitary group is a strongly continuous semigroup

`TauCeti.Semigroups.StronglyContinuousSemigroup` and
`TauCeti.OneParameterUnitaryGroup` describe the same subject from two sides:
`ℝ≥0`-indexed contractions on a real Banach space with generator
`A x = lim_{t→0⁺} (S t x - x)/t`, against `ℝ`-indexed unitaries on a complex
Hilbert space with generator `A x = lim_{t→0} (U t x - x)/(i t)`.  Carrying both
as independent stacks is what convergence Wave 3 exists to stop.

This module makes the second a *specialization* of the first:

* `toSemigroup U` — restrict a unitary group to `t ≥ 0` and forget the complex
  structure;
* `generator_toSemigroup` — its semigroup generator is `i` times the group
  generator, on the group's domain.

The factor `i` is not an artefact of the encoding.  It is the Stone convention:
a one-parameter unitary group is `U t = exp (i t A)` with `A` **self-adjoint**,
so the semigroup generator `i A` is skew-adjoint, which is exactly what
generates a unitary semigroup.  Stating the bridge with the factor visible is
the point — it is where the two conventions are reconciled.

## Generator domains

The forward domain inclusion is established here. The reverse inclusion and domain
equality for unitary groups are proved downstream in `OneParameterUnitaryGroup.Stone`.

## Provenance

*New.*  `TauCeti.OneParameterUnitaryGroup` is Spectra's structure, ported in
`OneParameterUnitaryGroup/Basic.lean`; `StronglyContinuousSemigroup` is upstream
Tau Ceti's.  The bridge between them is neither's.

This is the first `ForTauCeti` module to import `TauCeti`, which the dependency
policy has always allowed (`ForTauCeti` may import Mathlib / TauCeti /
ForTauCeti) but which nothing had needed until convergence work began.
-/

public section

open scoped InnerProductSpace NNReal
open Filter Topology Complex

namespace TauCeti
namespace OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A one-parameter unitary group, restricted to nonnegative time, is a
strongly continuous semigroup** over the underlying real Banach space. -/
noncomputable def toSemigroup (U : OneParameterUnitaryGroup H) :
    Semigroups.StronglyContinuousSemigroup H where
  toFun t := (U.U (t : ℝ)).restrictScalars ℝ
  map_zero' := by
    ext x
    simp [U.identity]
  map_add' s t := by
    ext x
    simp [NNReal.coe_add, U.group_law]
  continuousAt_zero' x := by
    have hcont : Continuous fun t : ℝ≥0 => U.U (t : ℝ) x :=
      (U.strong_continuous x).comp NNReal.continuous_coe
    exact hcont.continuousAt

/-- The derived semigroup acts as the group at nonnegative times. -/
@[simp] theorem toSemigroup_apply (U : OneParameterUnitaryGroup H) (t : ℝ≥0) (x : H) :
    (toSemigroup U) t x = U.U (t : ℝ) x := (rfl)
/-- The nonnegative-time semigroup is contractive, including on the zero space. -/
theorem norm_toSemigroup_le (U : OneParameterUnitaryGroup H) (t : ℝ≥0) :
    ‖(toSemigroup U) t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, toSemigroup_apply, norm_preserving]

/-- Its underlying operator is the group's. -/
@[simp] theorem toSemigroup_realOperator (U : OneParameterUnitaryGroup H)
    {t : ℝ} (ht : 0 ≤ t) (x : H) :
    (toSemigroup U).realOperator t x = U.U t x := by
  have ht' : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  calc (toSemigroup U).realOperator t x
      = (toSemigroup U).realOperator ((t.toNNReal : ℝ≥0) : ℝ) x := by rw [ht']
    _ = (toSemigroup U) t.toNNReal x := by
        rw [Semigroups.StronglyContinuousSemigroup.realOperator_coe]
    _ = U.U ((t.toNNReal : ℝ≥0) : ℝ) x := (rfl)
    _ = U.U t x := by rw [ht']

/-- The semigroup difference quotient is `i` times the group difference
quotient.  Both are the same vector; the group convention divides by `i t`. -/
theorem realQuot_eq_smul_genDiffQuot (U : OneParameterUnitaryGroup H) (x : H)
    {t : ℝ} (ht : 0 < t) :
    (1 / t) • ((toSemigroup U).realOperator t x - x)
      = Complex.I • genDiffQuot U x t := by
  rw [toSemigroup_realOperator U ht.le, genDiffQuot_apply, smul_smul]
  have hI : Complex.I * (Complex.I * (t : ℂ))⁻¹ = ((1 / t : ℝ) : ℂ) := by
    field_simp
    push_cast
    ring
  rw [hI]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

/-- **The generator bridge.**  A vector in the domain of the group generator is
in the domain of the semigroup generator, and there the semigroup generator is
`i` times the group generator. -/
theorem mem_domain_toSemigroup (U : OneParameterUnitaryGroup H) {x : H}
    (hx : x ∈ generatorDomain U) : x ∈ (toSemigroup U).domain := by
  obtain ⟨η, hη⟩ := mem_generatorDomain.mp hx
  refine ((toSemigroup U).mem_domain_iff_tendsto x).mpr ⟨Complex.I • η, ?_⟩
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 fun t ht => ne_of_gt ht
  have hquot : Tendsto (fun t : ℝ => Complex.I • genDiffQuot U x t) (𝓝[>] 0)
      (nhds (Complex.I • η)) :=
    (hη.mono_left hsub).const_smul Complex.I
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realQuot_eq_smul_genDiffQuot U x ht).symm

/-- **The generators agree.**  Restricting a one-parameter unitary group to `t ≥ 0` gives a
strongly continuous semigroup whose generator is the original one, up to the factor `i`.  This is
what makes the unitary-group layer a specialization of the semigroup theory rather than a parallel
stack. -/
theorem generator_toSemigroup (U : OneParameterUnitaryGroup H) {x : H}
    (hx : x ∈ generatorDomain U) :
    (toSemigroup U).generator ⟨x, by
        rw [Semigroups.StronglyContinuousSemigroup.generator_domain]
        exact mem_domain_toSemigroup U hx⟩
      = Complex.I • (generator U ⟨x, hx⟩) := by
  refine (toSemigroup U).generator_eq_of_tendsto (mem_domain_toSemigroup U hx) ?_
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 fun t ht => ne_of_gt ht
  have hquot : Tendsto (fun t : ℝ => Complex.I • genDiffQuot U x t) (𝓝[>] 0)
      (nhds (Complex.I • (generator U ⟨x, hx⟩))) :=
    ((generator_tendsto U ⟨x, hx⟩).mono_left hsub).const_smul Complex.I
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (realQuot_eq_smul_genDiffQuot U x ht).symm

end OneParameterUnitaryGroup
end TauCeti
