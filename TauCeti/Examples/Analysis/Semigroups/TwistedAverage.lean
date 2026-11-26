/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Atoms
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Semigroups.Group.Stone.Basic

/-!
# Checks: twisted averages of the identity group

Checks for the continuous-time mean ergodic projection
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.exists_tendsto_twistedAverage`) on the
identity group `U_t = 1`, realised as `StronglyContinuousGroup.ofBounded 0`, of a complete complex
Hilbert space `H`:

* every vector is fixed, so the projection onto the fixed space is `P₀ v = v`;
* the measure `σ_v = ‖v‖² δ₀` represents `t ↦ ⟪v, U_t v⟫ = ‖v‖²`, and the atomic-mass identity
  reads `‖P₀ v‖² = ‖v‖² = σ_v({0})`;
* for `a ≠ 0` the eigenspace `E_a` is `{0}`, the twisted average is
  `A_T^a v = ((1 − exp(−2πiaT)) / (2πiaT)) v`, which tends to `0`, and both sides of the mass
  identity vanish.
-/

public section

noncomputable section

open Filter MeasureTheory Complex TauCeti.Semigroups StronglyContinuousGroup
open scoped InnerProductSpace Topology Real NNReal

namespace TauCeti.Examples.TwistedAverageChecks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The identity group `ofBounded 0` is unitary, being the bounded Stone group `ofBoundedExp 0`. -/
theorem isUnitary_ofBounded_zero : (ofBounded (0 : H →L[ℝ] H)).IsUnitary := by
  have h : ofBoundedExp (0 : H →L[ℂ] H) = ofBounded 0 := by
    ext t v
    simp
  exact h ▸ isUnitary_ofBoundedExp 0 (.zero _)

/-- Every vector is fixed: the eigenspace of the identity group at frequency `0` is everything. -/
theorem eigenspace_ofBounded_zero_zero :
    (ofBounded (0 : H →L[ℝ] H)).eigenspace isUnitary_ofBounded_zero.isComplexLinear 0 = ⊤ := by
  ext v
  simp

/-- At a nonzero frequency the eigenspace of the identity group is `⊥`. -/
theorem eigenspace_ofBounded_zero_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
    (ofBounded (0 : H →L[ℝ] H)).eigenspace isUnitary_ofBounded_zero.isComplexLinear ω = ⊥ := by
  ext v
  simp only [mem_eigenspace_iff, ofBounded_zero_apply, one_apply_eq_self, Submodule.mem_bot]
  refine ⟨fun h => ?_, fun h t => by simp [h]⟩
  have h' := h (Real.pi / ω)
  have hexp : exp (ω * ((Real.pi / ω : ℝ) : ℂ) * I) = -1 := by
    rw [ofReal_div, mul_div_cancel₀ _ (ofReal_ne_zero.2 hω), exp_pi_mul_I]
  rw [hexp] at h'
  linear_combination (norm := module) (1 / 2 : ℂ) • h'

/-- The projection onto the fixed space of the identity group is the identity, `P₀ v = v`. -/
theorem starProjection_eigenspace_ofBounded_zero_zero (v : H) :
    ((ofBounded (0 : H →L[ℝ] H)).eigenspace isUnitary_ofBounded_zero.isComplexLinear
      0).starProjection v = v :=
  Submodule.starProjection_eq_self_iff.2 (by simp)

/-- The measure `‖v‖² δ₀` represents `t ↦ ⟪v, U_t v⟫ = ‖v‖²` for the identity group. -/
theorem inner_ofBounded_zero_eq_charFun (v : H) (t : ℝ) :
    ⟪v, ofBounded (0 : H →L[ℝ] H) t v⟫_ℂ =
      charFun ((‖v‖₊ ^ 2 : ℝ≥0) • Measure.dirac (0 : ℝ)) t := by
  rw [charFun_apply_real, integral_smul_nnreal_measure, integral_dirac]
  simp [inner_self_eq_norm_sq_to_K, NNReal.smul_def]

/-- **The atomic-mass identity at frequency `0`**: `‖P₀ v‖² = σ_v({0})`. -/
example (v : H) :
    ‖((ofBounded (0 : H →L[ℝ] H)).eigenspace isUnitary_ofBounded_zero.isComplexLinear
        0).starProjection v‖ ^ 2 =
      ((‖v‖₊ ^ 2 : ℝ≥0) • Measure.dirac (0 : ℝ)).real {0} :=
  isUnitary_ofBounded_zero.norm_starProjection_eigenspace_sq_eq_measureReal_singleton 0 v
    (inner_ofBounded_zero_eq_charFun v)

/-- Both sides of the atomic-mass identity: `‖P₀ v‖² = ‖v‖²`. -/
example (v : H) :
    ‖((ofBounded (0 : H →L[ℝ] H)).eigenspace isUnitary_ofBounded_zero.isComplexLinear
        0).starProjection v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [starProjection_eigenspace_ofBounded_zero_zero]

/-- **The twisted average** of the identity group at `a ≠ 0` is
`A_T^a v = ((1 − exp(−2πiaT)) / (2πiaT)) v`. -/
theorem twistedAverage_ofBounded_zero {a : ℝ} (ha : a ≠ 0) (T : ℝ) (v : H) :
    (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • ofBounded (0 : H →L[ℝ] H) t v =
      ((1 - exp (-(2 * π * a * T * I))) / (2 * π * a * T * I)) • v := by
  have hc : (-(2 * π * a * I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, ha, I_ne_zero]
  simp only [ofBounded_zero_apply, one_apply_eq_self]
  rw [intervalIntegral.integral_smul_const, smul_smul]
  congr 1
  have h := integral_exp_mul_complex (a := 0) (b := T) hc
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  have hfun : (fun t : ℝ => exp (-(2 * π * a * t * I))) =
      fun t : ℝ => exp (-(2 * π * a * I) * t) := by
    funext t; ring_nf
  rw [hfun, h]
  rcases eq_or_ne T 0 with rfl | _hT
  · simp
  · field_simp
    ring

/-- **The twisted averages of the identity group at `a ≠ 0` tend to `0`.** -/
theorem tendsto_twistedAverage_ofBounded_zero {a : ℝ} (ha : a ≠ 0) (v : H) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
        ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • ofBounded (0 : H →L[ℝ] H) t v)
      atTop (𝓝 0) := by
  obtain ⟨w, hw, -, hlim, -⟩ := isUnitary_ofBounded_zero.exists_tendsto_twistedAverage a v
  have hmem : w ∈ (ofBounded (0 : H →L[ℝ] H)).eigenspace
      isUnitary_ofBounded_zero.isComplexLinear (2 * π * a) := by
    rw [mem_eigenspace_iff]
    intro t
    push_cast
    exact hw t
  rw [eigenspace_ofBounded_zero_of_ne_zero (by positivity), Submodule.mem_bot] at hmem
  rwa [hmem] at hlim

/-- At `a ≠ 0` both sides of the atomic-mass identity vanish: `‖P_a v‖² = 0 = σ_v({2πa})`. -/
example {a : ℝ} (ha : a ≠ 0) (v : H) :
    ‖((ofBounded (0 : H →L[ℝ] H)).eigenspace isUnitary_ofBounded_zero.isComplexLinear
        (2 * π * a)).starProjection v‖ ^ 2 = 0 ∧
      ((‖v‖₊ ^ 2 : ℝ≥0) • Measure.dirac (0 : ℝ)).real {2 * π * a} = 0 := by
  have h2a : 2 * π * a ≠ 0 := by positivity
  refine ⟨by simp [eigenspace_ofBounded_zero_of_ne_zero h2a], ?_⟩
  simp [measureReal_def, Measure.dirac_apply', h2a.symm]

end TauCeti.Examples.TwistedAverageChecks
