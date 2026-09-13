/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear
public import TauCeti.Analysis.Semigroups.GrowthBound
public import TauCeti.LinearAlgebra.LinearPMap.Shift
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Phase shifts of a complex-linear strongly continuous semigroup

For a C₀-semigroup `S` acting by complex-linear operators on a complex Banach space and a real
number `b`, the *phase shift* is the semigroup

`(S.phaseShift hS b) t = exp (-i b t) • S t`.

Unlike the exponential shift `t ↦ exp (-omega t) • S t` of
`TauCeti/Analysis/Semigroups/ExponentialShift.lean`, which damps the semigroup and moves its
growth exponent, a phase shift multiplies by a unimodular scalar: it preserves every growth
bound `(omega, M)` exactly, and it subtracts `i b` from the generator. Composing the two shifts
realizes `t ↦ exp (-lambda t) • S t` for an arbitrary complex `lambda`.

This is the device that moves a spectral parameter parallel to the imaginary axis. Since the
Laplace-transform resolvent of a C₀-semigroup is a *real*-variable construction, it only ever
produces real points of the resolvent set; the phase shift converts a real point for the shifted
semigroup into the point `lambda = mu + i b` for `S`, which is how the complex resolvent set of
the complex generator is reached in
`TauCeti/Analysis/Semigroups/Resolvent/Complex.lean`.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.phaseShift`: the semigroup
  `t ↦ exp (-i b t) • S t`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.IsComplexLinear.phaseShift` and
  `TauCeti.Semigroups.StronglyContinuousSemigroup.HasGrowthBound.phaseShift`: a phase shift is
  again complex linear, and has the same growth bounds.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.phaseShift_domain`: a phase shift does not
  change the generator domain.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.complexGenerator_phaseShift`: the complex
  generator of `t ↦ exp (-i b t) • S t` is `A - i b`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.2 (rescaled semigroups).
-/

public section

noncomputable section

open Filter
open scoped NNReal Topology

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The phase shift of a complex-linear C₀-semigroup by `b : ℝ`: the semigroup
`t ↦ exp (-i b t) • S t`. -/
def phaseShift (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear) (b : ℝ) :
    StronglyContinuousSemigroup X where
  toFun t := Complex.exp (-(b * (t : ℝ)) * Complex.I) • S t
  map_zero' := by
    simp
  map_add' s t := by
    ext x
    simp only [NNReal.coe_add, ContinuousLinearMap.comp_apply, smul_apply]
    rw [S.map_add_apply, hS.map_smul, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  continuousAt_zero' x := by
    have h_phase : Tendsto (fun t : ℝ≥0 => Complex.exp (-(b * (t : ℝ)) * Complex.I))
        (nhds 0) (nhds 1) := by
      have h_cont : ContinuousAt
          (fun t : ℝ≥0 => Complex.exp (-(b * (t : ℝ)) * Complex.I)) 0 := by fun_prop
      simpa using h_cont.tendsto
    have h_orbit := S.continuousAt_zero_tendsto x
    simpa [ContinuousAt, S.map_zero_apply] using h_phase.smul h_orbit

omit [CompleteSpace X] in
/-- The native nonnegative-time operator of a phase shift. -/
@[simp]
theorem phaseShift_apply (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear) (b : ℝ)
    (t : ℝ≥0) : S.phaseShift hS b t = Complex.exp (-(b * (t : ℝ)) * Complex.I) • S t := by
  rw [phaseShift]; rfl

omit [CompleteSpace X] in
/-- Pointwise form of `StronglyContinuousSemigroup.phaseShift_apply`. -/
theorem phaseShift_apply_apply (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear)
    (b : ℝ) (t : ℝ≥0) (x : X) :
    S.phaseShift hS b t x = Complex.exp (-(b * (t : ℝ)) * Complex.I) • S t x := by
  rw [phaseShift_apply, smul_apply]

omit [CompleteSpace X] in
/-- Real-time form of a phase-shifted operator at nonnegative times. -/
theorem phaseShift_realOperator_of_nonneg (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (b t : ℝ) (ht : 0 ≤ t) :
    (S.phaseShift hS b).realOperator t
      = Complex.exp (-(b * t) * Complex.I) • S.realOperator t := by
  have ht_coe : ((t.toNNReal : ℝ) = t) := Real.coe_toNNReal t ht
  rw [← ht_coe, realOperator_coe, realOperator_coe, phaseShift_apply]

omit [CompleteSpace X] in
/-- Pointwise real-time form of a phase-shifted operator at nonnegative times. -/
theorem phaseShift_realOperator_apply_of_nonneg (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (b t : ℝ) (ht : 0 ≤ t) (x : X) :
    (S.phaseShift hS b).realOperator t x
      = Complex.exp (-(b * t) * Complex.I) • S.realOperator t x := by
  rw [S.phaseShift_realOperator_of_nonneg hS b t ht, smul_apply]

omit [CompleteSpace X] in
/-- A phase shift is again complex linear. -/
theorem IsComplexLinear.phaseShift {S : StronglyContinuousSemigroup X} (hS : S.IsComplexLinear)
    (b : ℝ) : (S.phaseShift hS b).IsComplexLinear := by
  rw [isComplexLinear_iff]
  intro t z x
  rw [phaseShift_apply_apply, phaseShift_apply_apply, hS.map_smul, smul_comm]

omit [CompleteSpace X] in
/-- The zero phase shift is the original semigroup. -/
@[simp]
theorem phaseShift_zero (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear) :
    S.phaseShift hS 0 = S := by
  ext t x
  simp

omit [CompleteSpace X] in
/-- Successive phase shifts add their parameters. -/
@[simp]
theorem phaseShift_phaseShift (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear)
    (b c : ℝ) :
    (S.phaseShift hS b).phaseShift (hS.phaseShift b) c = S.phaseShift hS (b + c) := by
  ext t x
  simp only [phaseShift_apply_apply]
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

namespace HasGrowthBound

omit [CompleteSpace X] in
/-- A phase shift multiplies by a unimodular scalar, so it preserves every growth bound. -/
theorem phaseShift {S : StronglyContinuousSemigroup X} {omega M : ℝ}
    (hb : S.HasGrowthBound omega M) (hS : S.IsComplexLinear) (b : ℝ) :
    (S.phaseShift hS b).HasGrowthBound omega M := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound hb.one_le (fun t ht => ?_)
  rw [S.phaseShift_realOperator_of_nonneg hS b t ht]
  calc ‖Complex.exp (-(b * t) * Complex.I) • S.realOperator t‖
      ≤ ‖Complex.exp (-(b * t) * Complex.I)‖ * ‖S.realOperator t‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = ‖S.realOperator t‖ := by
        rw [Complex.norm_exp]
        simp
    _ ≤ M * Real.exp (omega * t) := hb.bound t ht

end HasGrowthBound

/-! ## The generator of a phase shift -/

omit [CompleteSpace X] in
/-- The phase `t ↦ exp (-i b t)` has derivative `-i b` at `0`, in difference-quotient form along
the positive reals. -/
private theorem tendsto_phase_slope (b : ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ • (Complex.exp (-(b * t) * Complex.I) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(b * Complex.I))) := by
  have hderiv : HasDerivAt (fun t : ℝ => Complex.exp (-(b * t) * Complex.I))
      (-(b * Complex.I)) 0 := by
    have h : HasDerivAt (fun t : ℝ => (-(b * (t : ℂ)) * Complex.I)) (-(b * Complex.I)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (-(b : ℂ))).mul_const Complex.I
    simpa using h.cexp
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  refine (hslope.mono_left (nhdsWithin_mono _ ?_)).congr ?_
  · intro t ht
    exact ne_of_gt ht
  · intro t
    simp [slope_def_module]

omit [CompleteSpace X] in
/-- Phase shifting a semigroup shifts the limit of a generator difference quotient by `-i b`. -/
private theorem tendsto_phaseShift_genQuot (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (b : ℝ) {x Ax : X}
    (hgen : Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t x - x))
      (𝓝[>] (0 : ℝ)) (𝓝 Ax)) :
    Tendsto (fun t : ℝ => (1 / t) • ((S.phaseShift hS b).realOperator t x - x))
      (𝓝[>] (0 : ℝ)) (𝓝 (Ax - (b * Complex.I) • x)) := by
  have hphase : Tendsto (fun t : ℝ => Complex.exp (-(b * t) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => Complex.exp (-(b * t) * Complex.I)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsum := (hphase.smul hgen).add ((tendsto_phase_slope b).smul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 x)))
  have hsum' : Tendsto
      (fun t : ℝ => Complex.exp (-(b * t) * Complex.I) • ((1 / t) • (S.realOperator t x - x)) +
        (t⁻¹ • (Complex.exp (-(b * t) * Complex.I) - 1)) • x)
      (𝓝[>] (0 : ℝ)) (𝓝 (Ax - (b * Complex.I) • x)) := by
    simpa only [one_smul, neg_smul, sub_eq_add_neg] using hsum
  refine hsum'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [S.phaseShift_realOperator_apply_of_nonneg hS b t (le_of_lt ht), smul_comm, smul_assoc,
    one_div, ← smul_add]
  congr 1
  rw [sub_smul, one_smul, smul_sub]
  abel

omit [CompleteSpace X] in
/-- A vector of the generator domain stays in the domain after a phase shift. -/
private theorem mem_domain_phaseShift (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (b : ℝ) {x : X} (hx : x ∈ S.domain) :
    x ∈ (S.phaseShift hS b).domain :=
  ((S.phaseShift hS b).mem_domain_iff_tendsto x).mpr
    ⟨_, tendsto_phaseShift_genQuot S hS b (S.generator_tendsto ⟨x, hx⟩)⟩

omit [CompleteSpace X] in
/-- A phase shift does not change the generator domain. -/
@[simp]
theorem phaseShift_domain (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear) (b : ℝ) :
    (S.phaseShift hS b).domain = S.domain := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_domain_phaseShift S hS b hx)
  have h := mem_domain_phaseShift (S.phaseShift hS b) (hS.phaseShift b) (-b) hx
  rwa [phaseShift_phaseShift, add_neg_cancel, phaseShift_zero] at h

omit [CompleteSpace X] in
/-- The generator of a phase-shifted semigroup acts as `A - i b`. -/
theorem generator_phaseShift_apply (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear)
    (b : ℝ) {x : X} (hx : x ∈ S.domain) :
    (S.phaseShift hS b).generator ⟨x, by rw [generator_domain, phaseShift_domain]; exact hx⟩
      = S.generator ⟨x, by rwa [generator_domain]⟩ - (b * Complex.I) • x :=
  (S.phaseShift hS b).generator_eq_of_tendsto (by rw [phaseShift_domain]; exact hx)
    (tendsto_phaseShift_genQuot S hS b (S.generator_tendsto ⟨x, hx⟩))

omit [CompleteSpace X] in
/-- **The generator of a phase shift.** The complex generator of `t ↦ exp (-i b t) • S t` is
`A - i b`, where `A` is the complex generator of `S`. -/
theorem complexGenerator_phaseShift (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear)
    (b : ℝ) :
    (S.phaseShift hS b).complexGenerator (hS.phaseShift b)
      = TauCeti.LinearPMap.subScalar (S.complexGenerator hS) (b * Complex.I) := by
  have hdom : ∀ x : X, x ∈ (S.phaseShift hS b).complexDomain (hS.phaseShift b) ↔
      x ∈ S.complexDomain hS := by
    intro x
    rw [mem_complexDomain_iff, mem_complexDomain_iff, phaseShift_domain]
  refine LinearPMap.ext ?_ ?_
  · rw [complexGenerator_domain, TauCeti.LinearPMap.subScalar_domain, complexGenerator_domain]
    exact Submodule.ext hdom
  · intro x hx _
    rw [complexGenerator_domain] at hx
    have hxS : x ∈ S.domain := (mem_complexDomain_iff _ _ _).mp ((hdom x).mp hx)
    rw [complexGenerator_apply, TauCeti.LinearPMap.subScalar_apply, complexGenerator_apply,
      generator_phaseShift_apply S hS b hxS]

end TauCeti.Semigroups.StronglyContinuousSemigroup

end
