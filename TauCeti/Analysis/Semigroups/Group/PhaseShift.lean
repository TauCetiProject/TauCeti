/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.ComplexLinear
public import TauCeti.Analysis.Semigroups.Group.Unitary
public import TauCeti.Analysis.Semigroups.PhaseShift

/-!
# Phase shifts of a complex-linear strongly continuous group

For a C₀-group `U` on a complex normed space whose forward semigroup is complex linear and a real
frequency `b`, the *phase shift* is the two-sided C₀-group

`(U.phaseShift hU b) t = exp (-(b * t) * I) • U t`.

Its restriction to `[0, ∞)` agrees with the semigroup phase shift
`TauCeti.Semigroups.StronglyContinuousSemigroup.phaseShift`, and time reversal negates the shift
parameter. Because multiplication by `exp (-(b * t) * I)` is unimodular and commutes with every
complex-linear operator, a phase shift preserves complex linearity, every two-sided growth bound,
and unitarity on a complex Hilbert space.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift`: the phase-shifted C₀-group
  `t ↦ exp (-(b * t) * I) • U t`.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_toSemigroup`: compatibility with the
  forward semigroup phase shift.
* `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_reflect`: time reversal negates the phase
  parameter.
* `TauCeti.Semigroups.StronglyContinuousGroup.isComplexLinear_phaseShift`: a phase shift remains
  complex linear.
* `TauCeti.Semigroups.StronglyContinuousGroup.HasGrowthBound.phaseShift`: a phase shift preserves
  two-sided growth bounds.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.phaseShift`: a phase shift of a unitary
  C₀-group is unitary.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups) and Section II.3.11 (strongly continuous groups).
-/

public section

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The phase shift of a complex-linear C₀-group by `b : ℝ`: the C₀-group
`t ↦ exp (-(b * t) * I) • U t`. -/
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
    have h_phase : Tendsto (fun t : ℝ ↦ Complex.exp (-(b * t) * Complex.I)) (𝓝 0) (𝓝 1) := by
      have h_cont : ContinuousAt (fun t : ℝ ↦ Complex.exp (-(b * t) * Complex.I)) 0 := by fun_prop
      simpa using h_cont.tendsto
    have h_orbit : Tendsto (fun t : ℝ ↦ U t x) (𝓝 0) (𝓝 x) := by
      simpa [U.map_zero_apply] using ((U.continuous_orbit x).continuousAt (x := 0)).tendsto
    simpa [ContinuousAt, U.map_zero_apply] using h_phase.smul h_orbit

/-- The operator at real time `t` of a phase-shifted C₀-group. -/
@[simp]
theorem phaseShift_apply (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b t : ℝ) : U.phaseShift hU b t = Complex.exp (-(b * t) * Complex.I) • U t := by
  rw [phaseShift]; rfl

/-- Pointwise form of `StronglyContinuousGroup.phaseShift_apply`. -/
theorem phaseShift_apply_apply (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (b t : ℝ) (x : X) :
    U.phaseShift hU b t x = Complex.exp (-(b * t) * Complex.I) • U t x := by
  rw [phaseShift_apply, smul_apply]

/-- The forward semigroup of a phase-shifted C₀-group is the phase shift of its forward
semigroup. -/
@[simp]
theorem phaseShift_toSemigroup (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).toSemigroup = U.toSemigroup.phaseShift hU b := by
  ext t x
  simp

/-- Time reversal negates the shift parameter of a phase-shifted C₀-group. -/
@[simp]
theorem phaseShift_reflect (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).reflect = U.reflect.phaseShift (U.reflect_isComplexLinear hU) (-b) := by
  ext t x
  simp

/-- A phase shift of a complex-linear C₀-group is again complex linear. -/
theorem isComplexLinear_phaseShift (U : StronglyContinuousGroup X)
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
    (U.phaseShift hU b).phaseShift (U.isComplexLinear_phaseShift hU b) c =
      U.phaseShift hU (b + c) := by
  ext t x
  simp only [phaseShift_apply_apply, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

namespace HasGrowthBound

/-- A phase shift multiplies by a unimodular scalar, so it preserves every two-sided growth
bound. -/
theorem phaseShift {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.phaseShift hU b).HasGrowthBound ω M := by
  refine hasGrowthBound_of_bound hb.one_le fun t ↦ ?_
  rw [phaseShift_apply]
  have hnorm : ‖Complex.exp (-(b * t) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc ‖Complex.exp (-(b * t) * Complex.I) • U t‖
      ≤ ‖Complex.exp (-(b * t) * Complex.I)‖ * ‖U t‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = ‖U t‖ := by rw [hnorm, one_mul]
    _ ≤ M * Real.exp (ω * |t|) := hb.bound t

end HasGrowthBound

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A phase shift of a unitary C₀-group is again unitary. -/
theorem IsUnitary.phaseShift {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (b : ℝ) :
    (U.phaseShift hU.isComplexLinear b).IsUnitary := by
  refine IsUnitary.intro fun t x y ↦ ?_
  rw [phaseShift_apply_apply, phaseShift_apply_apply, inner_smul_left, inner_smul_right,
    hU.inner_map_map, ← mul_assoc, Complex.conj_mul']
  have hnorm : ‖Complex.exp (-(b * t) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm]
  simp

end Unitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
