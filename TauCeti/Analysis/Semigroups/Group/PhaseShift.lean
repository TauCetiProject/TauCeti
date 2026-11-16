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

For a complex-linear C₀-group `U` on a complex normed space and a real frequency `b`, the
*phase shift* is the C₀-group

`(U.phaseShift hU b) t = exp (-i b t) • U t`.

Its forward semigroup is the semigroup phase shift
`TauCeti.Semigroups.StronglyContinuousSemigroup.phaseShift`, its time reversal shifts by `-b`,
and because `exp (-i b t)` is unimodular it preserves operator norms, two-sided growth bounds,
and unitarity while shifting the complex generator by `-i b`.

Phase shifts convert frequency-`b` eigenspaces and twisted Cesàro averages into fixed-point
subspaces and untwisted Cesàro averages for the shifted group.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.map_smul_of_isComplexLinear`: complex linearity of
  the forward semigroup extends to every real time.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift`: the phase-shifted C₀-group
  `t ↦ exp (-i b t) • U t`.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_toSemigroup`,
  `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_zero`,
  `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_phaseShift`,
  `TauCeti.Semigroups.StronglyContinuousGroup.reflect_phaseShift`: algebraic compatibility.
* `TauCeti.Semigroups.StronglyContinuousGroup.HasGrowthBound.phaseShift` and
  `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.phaseShift`: preservation of two-sided
  growth bounds and unitarity.
* `TauCeti.Semigroups.StronglyContinuousGroup.complexGenerator_phaseShift`: the complex generator
  of a phase-shifted unitary group is `A - i b`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups).
-/

public section

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

section ComplexBanach

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If the forward semigroup of a C₀-group is complex linear, then every group operator commutes
with complex scalar multiplication at every real time, positive or negative. -/
theorem map_smul_of_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (t : ℝ) (z : ℂ) (x : X) :
    U t (z • x) = z • U t x := by
  rcases le_or_gt 0 t with ht | ht
  · rw [← U.toSemigroup_realOperator_of_nonneg ht]
    exact hU.realOperator_map_smul t z x
  · have hnt : 0 ≤ -t := neg_nonneg.mpr ht.le
    have h := (U.reflect_isComplexLinear hU).realOperator_map_smul (-t) z x
    rwa [U.reflect_toSemigroup_realOperator_of_nonneg hnt, neg_neg] at h

/-- The phase shift of a complex-linear C₀-group by `b : ℝ`: the C₀-group
`t ↦ exp (-i b t) • U t`. -/
def phaseShift (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    StronglyContinuousGroup X where
  toFun t := Complex.exp (-(b * t) * Complex.I) • U t
  map_zero' := by
    simp
  map_add' s t := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, smul_apply]
    rw [U.map_add_apply, U.map_smul_of_isComplexLinear hU, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  continuousAt_zero' x := by
    have hphase :
        Tendsto (fun t : ℝ ↦ Complex.exp (-(b * t) * Complex.I)) (𝓝 0) (𝓝 1) := by
      have hcont : ContinuousAt (fun t : ℝ ↦ Complex.exp (-(b * t) * Complex.I)) 0 := by fun_prop
      simpa using hcont.tendsto
    have horbit : Tendsto (fun t : ℝ ↦ U t x) (𝓝 0) (𝓝 x) := by
      simpa [ContinuousAt, U.map_zero_apply] using (U.continuous_orbit x).continuousAt (x := 0)
    simpa [ContinuousAt, U.map_zero_apply] using hphase.smul horbit

/-- The operator of a phase-shifted C₀-group at time `t`. -/
@[simp]
theorem phaseShift_apply (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b t : ℝ) :
    U.phaseShift hU b t = Complex.exp (-(b * t) * Complex.I) • U t := by
  rw [phaseShift]
  rfl

/-- Pointwise form of `StronglyContinuousGroup.phaseShift_apply`. -/
theorem phaseShift_apply_apply (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b t : ℝ) (x : X) :
    U.phaseShift hU b t x = Complex.exp (-(b * t) * Complex.I) • U t x := by
  rw [phaseShift_apply, smul_apply]

/-- The forward semigroup of a group phase shift is the semigroup phase shift. -/
@[simp]
theorem phaseShift_toSemigroup (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).toSemigroup = U.toSemigroup.phaseShift hU b := by
  ext t x
  simp

/-- A phase-shifted C₀-group has a complex-linear forward semigroup. -/
theorem phaseShift_isComplexLinear (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).toSemigroup.IsComplexLinear := by
  rw [phaseShift_toSemigroup]
  exact hU.phaseShift b

/-- The zero phase shift is the original C₀-group. -/
@[simp]
theorem phaseShift_zero (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    U.phaseShift hU 0 = U := by
  ext t x
  simp

/-- Successive phase shifts add their parameters. -/
@[simp]
theorem phaseShift_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b c : ℝ) :
    (U.phaseShift hU b).phaseShift (U.phaseShift_isComplexLinear hU b) c =
      U.phaseShift hU (b + c) := by
  ext t x
  simp only [phaseShift_apply_apply]
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Reversing time negates the phase-shift frequency. -/
@[simp]
theorem reflect_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).reflect =
      U.reflect.phaseShift (U.reflect_isComplexLinear hU) (-b) := by
  ext t x
  simp only [reflect_apply, phaseShift_apply_apply]
  congr 2
  push_cast
  ring

/-- A phase shift multiplies by a unimodular scalar, so it preserves operator norms. -/
theorem norm_phaseShift_apply (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b t : ℝ) :
    ‖U.phaseShift hU b t‖ = ‖U t‖ := by
  have hnorm (c : ℝ) : ‖Complex.exp (-(c * t) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  refine le_antisymm ?_ ?_
  · rw [phaseShift_apply]
    calc
      ‖Complex.exp (-(b * t) * Complex.I) • U t‖
          ≤ ‖Complex.exp (-(b * t) * Complex.I)‖ * ‖U t‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = ‖U t‖ := by rw [hnorm b, one_mul]
  · have hundo : U t = Complex.exp (-((-b : ℝ) * t) * Complex.I) • U.phaseShift hU b t := by
      rw [← phaseShift_apply (U.phaseShift hU b) (U.phaseShift_isComplexLinear hU b) (-b) t,
        phaseShift_phaseShift, add_neg_cancel, phaseShift_zero]
    rw [hundo]
    calc
      ‖Complex.exp (-((-b : ℝ) * t) * Complex.I) • U.phaseShift hU b t‖
          ≤ ‖Complex.exp (-((-b : ℝ) * t) * Complex.I)‖ * ‖U.phaseShift hU b t‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = ‖U.phaseShift hU b t‖ := by rw [hnorm (-b), one_mul]

/-- A phase shift preserves every two-sided exponential growth bound. -/
theorem HasGrowthBound.phaseShift {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).HasGrowthBound ω M :=
  hasGrowthBound_of_bound hb.one_le fun t ↦ by
    rw [U.norm_phaseShift_apply hU b t]
    exact hb.bound t

/-- A phase shift preserves the infinitesimal generator domain. -/
@[simp]
theorem phaseShift_domain (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).domain = U.domain := by
  rw [domain_def, domain_def, phaseShift_toSemigroup,
    StronglyContinuousSemigroup.phaseShift_domain]

end ComplexBanach

section ComplexHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A phase shift of a unitary C₀-group is again unitary. -/
theorem IsUnitary.phaseShift {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (b : ℝ) :
    (U.phaseShift hU.isComplexLinear b).IsUnitary := by
  refine IsUnitary.intro fun t x y ↦ ?_
  rw [phaseShift_apply_apply, phaseShift_apply_apply, inner_smul_left, inner_smul_right,
    hU.inner_map_map, ← mul_assoc, RCLike.conj_mul, Complex.norm_exp]
  simp

/-- The complex generator of a phase-shifted unitary C₀-group is `A - i b`, where `A` is the
complex generator of `U`. -/
theorem complexGenerator_phaseShift (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (b : ℝ) :
    (U.phaseShift hU.isComplexLinear b).complexGenerator (hU.phaseShift b) =
      LinearPMap.subScalar (U.complexGenerator hU) (b * Complex.I) := by
  rw [complexGenerator_def, complexGenerator_def]
  simpa only [phaseShift_toSemigroup] using
    U.toSemigroup.complexGenerator_phaseShift hU.isComplexLinear b

end ComplexHilbert

end TauCeti.Semigroups.StronglyContinuousGroup

end
