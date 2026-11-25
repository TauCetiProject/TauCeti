/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.Semigroups.Group.MeanErgodic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener

/-!
# Spectral atomic-mass identity for unitary C₀-groups

When `U` is a unitary C₀-group on a complete complex Hilbert space `H` and `σ` is a finite Borel
measure on `ℝ` representing `t ↦ ⟪v, U t v⟫_ℂ` as `charFun σ`, combining the twisted mean ergodic
theorem (`IsUnitary.tendsto_twistedAverage_starProjection`) with atomic-mass inversion for
characteristic functions (`TauCeti.tendsto_average_cexp_mul_charFun`) identifies the squared
norm of the eigenprojection onto `U.eigenspace hU.isComplexLinear ω` as the spectral atomic mass
`σ.real {ω}`.

## Main results

* `IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`:
  `‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω}`.
* `IsUnitary.exists_tendsto_twistedAverage`: existence of the twisted mean ergodic limit `w`
  at frequency `a` (`ω = 2πa`) together with its eigenfunction, orthogonality, and spectral
  atomic-mass properties.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U : StronglyContinuousGroup H}

/-- **Spectral atomic-mass identity.** For a unitary C₀-group `U` on a complete complex Hilbert
space `H`, an angular frequency `ω : ℝ`, a vector `v : H`, and any finite Borel measure `σ` on `ℝ`
representing `t ↦ ⟪v, U t v⟫_ℂ` as `charFun σ`, the squared norm of the orthogonal projection of
`v` onto `U.eigenspace hU.isComplexLinear ω` equals `σ.real {ω}`. -/
theorem norm_starProjection_eigenspace_sq_eq_measureReal_singleton [CompleteSpace H]
    (hU : U.IsUnitary) (ω : ℝ) (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω} := by
  set P := (U.eigenspace hU.isComplexLinear ω).starProjection
  have hlim₁ : Tendsto (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ)
      atTop (𝓝 ⟪v, P v⟫_ℂ) :=
    ((innerSL ℂ v).continuous.continuousAt.tendsto).comp
      (hU.tendsto_twistedAverage_starProjection ω v)
  have hlim₂ : Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t)
      atTop (𝓝 (σ.real {ω} : ℂ)) :=
    by simpa only [neg_mul] using TauCeti.tendsto_average_cexp_mul_charFun σ ω
  have hfun : (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ) =
      fun T : ℝ ↦
        (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t := by
    funext T
    have horbit : (fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I)) • U t v) =
        fun t : ℝ ↦ U.phaseShift hU.isComplexLinear ω t v :=
      funext fun t ↦ by rw [U.phaseShift_apply_apply, neg_mul]
    rw [horbit, inner_smul_right_eq_smul, Complex.real_smul, Complex.ofReal_inv,
      (U.phaseShift hU.isComplexLinear ω).inner_intervalIntegral_orbit]
    congr 2
    ext t
    rw [phaseShift_apply_apply, neg_mul, inner_smul_right, hσ]
  rw [hfun] at hlim₁
  have heq : ⟪v, P v⟫_ℂ = (σ.real {ω} : ℂ) := tendsto_nhds_unique hlim₁ hlim₂
  have hre := congrArg RCLike.re heq
  simpa [P, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.re_inner_starProjection_eq_normSq] using hre

/-- **Continuous-time twisted mean ergodic theorem with spectral atomic mass.** For a unitary
C₀-group `U` on a complete complex Hilbert space `H`, a frequency `a : ℝ`, and `v : H`, the
twisted time averages `(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • U t v`
converge in norm as `T → ∞` to a vector `w` satisfying `U t w = exp (2 * π * a * t * I) • w` for
all `t`, orthogonal to `v - w` against every vector with the same eigenvalue behavior, and
satisfying `‖w‖ ^ 2 = σ.real {2 * π * a}` for every finite Borel measure `σ` with
`⟪v, U t v⟫_ℂ = charFun σ t`. -/
theorem exists_tendsto_twistedAverage [CompleteSpace H] (hU : U.IsUnitary) (a : ℝ) (v : H) :
    ∃ w : H, (∀ t : ℝ, U t w = Complex.exp (2 * Real.pi * a * t * Complex.I) • w) ∧
      (∀ u : H, (∀ t : ℝ, U t u = Complex.exp (2 * Real.pi * a * t * Complex.I) • u) →
        ⟪u, v - w⟫_ℂ = 0) ∧
      Tendsto (fun T : ℝ ↦ (T⁻¹ : ℂ) •
          ∫ t in (0 : ℝ)..T, Complex.exp (-(2 * Real.pi * a * t * Complex.I)) • U t v)
        atTop (𝓝 w) ∧
      ∀ σ : Measure ℝ, IsFiniteMeasure σ →
        (∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) →
        ‖w‖ ^ 2 = σ.real {2 * Real.pi * a} := by
  let ω : ℝ := 2 * Real.pi * a
  let E := U.eigenspace hU.isComplexLinear ω
  let w : H := E.starProjection v
  have hcast (t : ℝ) : (ω : ℂ) * (t : ℂ) * Complex.I = 2 * Real.pi * a * t * Complex.I := by
    dsimp only [ω]
    push_cast
    ring
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · have hw : w ∈ E := by
      dsimp only [w]
      rw [Submodule.starProjection_apply]
      exact Submodule.coe_mem _
    rw [U.mem_eigenspace_iff hU.isComplexLinear ω w] at hw
    simpa only [hcast] using hw
  · intro u hu
    have hu_mem : u ∈ E := by
      rw [U.mem_eigenspace_iff hU.isComplexLinear ω u]
      simpa only [hcast] using hu
    have horth := Submodule.sub_starProjection_mem_orthogonal (K := E) v
    rw [Submodule.mem_orthogonal] at horth
    exact horth u hu_mem
  · have hlim := hU.tendsto_twistedAverage_starProjection ω v
    refine hlim.congr fun T ↦ ?_
    conv_rhs => rw [← Complex.ofReal_inv, Complex.coe_smul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [hcast]
  · intro σ _ hσ
    exact hU.norm_starProjection_eigenspace_sq_eq_measureReal_singleton ω v hσ

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
