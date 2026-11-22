/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.ComplexLinear
public import TauCeti.Analysis.Semigroups.Group.Unitary
public import TauCeti.Analysis.Semigroups.PhaseShift
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Phase shifts of a complex-linear strongly continuous group

For a strongly continuous one-parameter group `U` on a complex normed space whose forward
semigroup is complex linear (and hence every group operator is complex linear by
`StronglyContinuousGroup.map_smul_of_isComplexLinear`) and a real frequency `b`, the
**phase shift** is the C₀-group

`(U.phaseShift hU b) t = exp (-i b t) • U t`.

This is the two-sided counterpart of `StronglyContinuousSemigroup.phaseShift` in
`TauCeti/Analysis/Semigroups/PhaseShift.lean`. Its forward semigroup is the semigroup phase shift,
time reversal negates the frequency, and phase shifting preserves unitarity on a complex inner
product space. In mean ergodic theory, phase shifting turns twisted averages
`T⁻¹ ∫₀ᵀ exp (-i b t) U t v dt` into untwisted averages of the shifted unitary group.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift`: the phase-shifted C₀-group
  `t ↦ exp (-i b t) • U t`.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_toSemigroup` and
  `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_reflect`: compatibility with the forward
  semigroup and time reversal.
* `TauCeti.Semigroups.StronglyContinuousGroup.norm_phaseShift` and
  `TauCeti.Semigroups.StronglyContinuousGroup.HasGrowthBound.phaseShift`: a phase shift preserves
  pointwise norms, operator norms, and exponential growth bounds.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.phaseShift`: a phase shift of a unitary
  C₀-group is again unitary.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups).
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.Semigroups.StronglyContinuousGroup

section ComplexNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private theorem phaseShift_comp_reflect_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) (t : ℝ≥0) :
    (U.toSemigroup.phaseShift hU b t).comp
      (U.reflect.toSemigroup.phaseShift (U.reflect_isComplexLinear hU) (-b) t) =
      ContinuousLinearMap.id ℝ X := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    StronglyContinuousSemigroup.phaseShift_apply_apply, toSemigroup_apply, reflect_apply]
  rw [U.map_smul_of_isComplexLinear hU, U.map_apply_map_neg_apply, smul_smul, ← Complex.exp_add]
  have hzero : -((b : ℂ) * (t : ℝ)) * Complex.I + -((-b : ℝ) * (t : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast; ring
  rw [show -((b : ℂ) * (t : ℝ)) * Complex.I + -(((-b : ℝ) : ℂ) * (t : ℝ)) * Complex.I = 0 from
    hzero, Complex.exp_zero, one_smul]

private theorem reflect_phaseShift_comp_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) (t : ℝ≥0) :
    (U.reflect.toSemigroup.phaseShift (U.reflect_isComplexLinear hU) (-b) t).comp
      (U.toSemigroup.phaseShift hU b t) =
      ContinuousLinearMap.id ℝ X := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    StronglyContinuousSemigroup.phaseShift_apply_apply, toSemigroup_apply, reflect_apply]
  rw [U.map_smul_of_isComplexLinear hU, U.map_neg_apply_map_apply, smul_smul, ← Complex.exp_add]
  have hzero : -((-b : ℝ) * (t : ℝ) : ℂ) * Complex.I + -((b : ℂ) * (t : ℝ)) * Complex.I = 0 := by
    push_cast; ring
  rw [show -(((-b : ℝ) : ℂ) * (t : ℝ)) * Complex.I + -((b : ℂ) * (t : ℝ)) * Complex.I = 0 from
    hzero, Complex.exp_zero, one_smul]

/-- The phase shift of a complex-linear C₀-group by `b : ℝ`: the group
`t ↦ exp (-i b t) • U t`, obtained by gluing the forward phase shift by `b` and the reflected
phase shift by `-b`. -/
def phaseShift (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    StronglyContinuousGroup X :=
  (U.toSemigroup.phaseShift hU b).toGroupOfInverse
    (U.reflect.toSemigroup.phaseShift (U.reflect_isComplexLinear hU) (-b))
    (U.phaseShift_comp_reflect_phaseShift hU b)
    (U.reflect_phaseShift_comp_phaseShift hU b)

/-- The operator at time `t` of a phase-shifted C₀-group. -/
@[simp]
theorem phaseShift_apply (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b t : ℝ) : U.phaseShift hU b t = Complex.exp (-(b * t * Complex.I)) • U t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [phaseShift, StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonneg _ _ _ _ ht,
      StronglyContinuousSemigroup.phaseShift_realOperator_of_nonneg _ _ _ _ ht,
      U.toSemigroup_realOperator_of_nonneg ht]
    congr 2
    ring
  · have hneg : 0 ≤ -t := neg_nonneg.mpr ht.le
    rw [phaseShift, StronglyContinuousSemigroup.toGroupOfInverse_apply_of_nonpos _ _ _ _ ht.le,
      StronglyContinuousSemigroup.phaseShift_realOperator_of_nonneg _ _ _ _ hneg,
      U.reflect_toSemigroup_realOperator_of_nonneg hneg, neg_neg]
    congr 2
    push_cast
    ring

/-- Pointwise form of `StronglyContinuousGroup.phaseShift_apply`. -/
theorem phaseShift_apply_apply (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b t : ℝ) (x : X) :
    U.phaseShift hU b t x = Complex.exp (-(b * t * Complex.I)) • U t x := by
  rw [phaseShift_apply, smul_apply]

/-- The forward semigroup of a phase-shifted C₀-group is the semigroup phase shift. -/
@[simp]
theorem phaseShift_toSemigroup (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).toSemigroup = U.toSemigroup.phaseShift hU b :=
  StronglyContinuousSemigroup.toGroupOfInverse_toSemigroup _ _ _ _

private theorem phaseShift_reflect_toSemigroup (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).reflect.toSemigroup =
      U.reflect.toSemigroup.phaseShift (U.reflect_isComplexLinear hU) (-b) :=
  StronglyContinuousSemigroup.toGroupOfInverse_reflect_toSemigroup _ _ _ _

private theorem semigroup_phaseShift_congr {S₁ S₂ : StronglyContinuousSemigroup X} (h : S₁ = S₂)
    (h₁ : S₁.IsComplexLinear) (h₂ : S₂.IsComplexLinear) {b₁ b₂ : ℝ} (hb : b₁ = b₂) :
    S₁.phaseShift h₁ b₁ = S₂.phaseShift h₂ b₂ := by
  subst h hb
  rfl

/-- A phase shift of a complex-linear C₀-group has a complex-linear forward semigroup. -/
theorem phaseShift_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).toSemigroup.IsComplexLinear := by
  rw [phaseShift_toSemigroup]
  exact hU.phaseShift b

/-- The zero phase shift is the original C₀-group. -/
@[simp]
theorem phaseShift_zero (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    U.phaseShift hU 0 = U :=
  ((U.phaseShift hU 0).eq_toGroupOfInverse
    (by rw [phaseShift_toSemigroup, StronglyContinuousSemigroup.phaseShift_zero])
    (by rw [phaseShift_reflect_toSemigroup, neg_zero,
      StronglyContinuousSemigroup.phaseShift_zero])).trans
    U.toGroupOfInverse_toSemigroup_reflect_toSemigroup

/-- Successive phase shifts add their frequencies. -/
@[simp]
theorem phaseShift_phaseShift (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b c : ℝ) :
    (U.phaseShift hU b).phaseShift (U.phaseShift_isComplexLinear hU b) c =
      U.phaseShift hU (b + c) := by
  refine (((U.phaseShift hU b).phaseShift (U.phaseShift_isComplexLinear hU b) c).eq_toGroupOfInverse
    ?_ ?_).trans (U.phaseShift hU (b + c)).toGroupOfInverse_toSemigroup_reflect_toSemigroup
  · conv_lhs => rw [phaseShift_toSemigroup]
    conv_rhs => rw [phaseShift_toSemigroup]
    exact (semigroup_phaseShift_congr (U.phaseShift_toSemigroup hU b) _ _ rfl).trans
      (StronglyContinuousSemigroup.phaseShift_phaseShift U.toSemigroup hU b c)
  · conv_lhs => rw [phaseShift_reflect_toSemigroup]
    conv_rhs => rw [phaseShift_reflect_toSemigroup]
    exact (semigroup_phaseShift_congr (U.phaseShift_reflect_toSemigroup hU b) _ _ rfl).trans
      ((StronglyContinuousSemigroup.phaseShift_phaseShift U.reflect.toSemigroup
        (U.reflect_isComplexLinear hU) (-b) (-c)).trans
        (by rw [← neg_add]))

/-- Time reversal commutes with phase shift by negating the frequency. -/
@[simp]
theorem phaseShift_reflect (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b : ℝ) :
    (U.phaseShift hU b).reflect = U.reflect.phaseShift (U.reflect_isComplexLinear hU) (-b) := by
  refine ((U.phaseShift hU b).reflect.eq_toGroupOfInverse ?_ ?_).trans
    (U.reflect.phaseShift (U.reflect_isComplexLinear hU)
      (-b)).toGroupOfInverse_toSemigroup_reflect_toSemigroup
  · rw [phaseShift_reflect_toSemigroup, phaseShift_toSemigroup]
  · rw [reflect_reflect, phaseShift_toSemigroup, phaseShift_reflect_toSemigroup]
    exact semigroup_phaseShift_congr (congrArg toSemigroup U.reflect_reflect.symm) _ _
      (neg_neg b).symm

/-- A phase shift preserves pointwise norms. -/
theorem norm_phaseShift_apply (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b t : ℝ) (x : X) : ‖U.phaseShift hU b t x‖ = ‖U t x‖ := by
  rw [phaseShift_apply_apply, norm_smul, Complex.norm_exp]
  simp

/-- A phase shift preserves operator norms. -/
theorem norm_phaseShift (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b t : ℝ) : ‖U.phaseShift hU b t‖ = ‖U t‖ := by
  rw [phaseShift_apply, norm_smul, Complex.norm_exp]
  simp

/-- A phase shift preserves every two-sided exponential growth bound. -/
theorem HasGrowthBound.phaseShift {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).HasGrowthBound ω M :=
  hasGrowthBound_of_bound hb.one_le fun t => by
    rw [norm_phaseShift]
    exact hb.bound t

end ComplexNormed

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A phase shift multiplies each operator by a unimodular scalar, so it preserves unitarity. -/
theorem IsUnitary.phaseShift {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (b : ℝ) :
    (U.phaseShift hU.isComplexLinear b).IsUnitary :=
  isUnitary_of_isComplexLinear_of_opNorm_le_one _
    (U.phaseShift_isComplexLinear hU.isComplexLinear b) fun t => by
      rw [norm_phaseShift]
      exact hU.opNorm_le_one t

end Unitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
