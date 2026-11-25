/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Atoms
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Checks: twisted averages of the identity group

Checks for the continuous-time mean ergodic projection
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.exists_tendsto_twistedAverage`) on the
identity group `U_t = 1` of a complete complex Hilbert space `H`, the third Check of §12.4.1 of the
MathematicalBilliards roadmap:

* every vector is fixed, so the projection onto the fixed space is `P₀ v = v`;
* the measure `σ_v = ‖v‖² δ₀` represents `t ↦ ⟪v, U_t v⟫ = ‖v‖²`, and the atomic-mass identity
  reads `‖P₀ v‖² = ‖v‖² = σ_v({0})`;
* for `a ≠ 0` the eigenspace `E_a` is `{0}`, the twisted average is
  `A_T^a v = ((1 − exp(−2πiaT)) / (2πiaT)) v`, which tends to `0`, and both sides of the mass
  identity vanish.
-/

public section

noncomputable section

open Filter MeasureTheory Complex TauCeti.Semigroups
open scoped InnerProductSpace Topology Real

namespace TauCeti.Examples.TwistedAverageChecks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The identity group `U_t = 1`. -/
def idGroup : StronglyContinuousGroup H where
  toFun _ := ContinuousLinearMap.id ℝ H
  map_zero' := rfl
  map_add' _ _ := (ContinuousLinearMap.id_comp _).symm
  continuousAt_zero' _ := continuousAt_const

@[simp]
theorem idGroup_apply (t : ℝ) (v : H) : idGroup t v = v :=
  (rfl)

theorem isUnitary_idGroup : (idGroup (H := H)).IsUnitary :=
  .intro fun _ _ _ => by simp

/-- Every vector is fixed: the eigenspace at frequency `0` is everything. -/
theorem eigenspace_idGroup_zero :
    idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear 0 = ⊤ := by
  ext v
  simp

/-- At a nonzero frequency the eigenspace is `{0}`: `v = exp(iω t) v` at `t = π / ω` gives
`v = −v`. -/
theorem eigenspace_idGroup_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
    idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear ω = ⊥ := by
  ext v
  simp only [StronglyContinuousGroup.mem_eigenspace_iff, idGroup_apply, Submodule.mem_bot]
  refine ⟨fun h => ?_, fun h t => by simp [h]⟩
  have h' := h (Real.pi / ω)
  have hexp : exp (ω * ((Real.pi / ω : ℝ) : ℂ) * I) = -1 := by
    rw [ofReal_div, mul_div_cancel₀ _ (ofReal_ne_zero.2 hω), exp_pi_mul_I]
  rw [hexp, neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h'
  exact (smul_eq_zero.1 h').resolve_left two_ne_zero

variable [CompleteSpace H]

/-- The projection onto the fixed space is the identity, `P₀ v = v`. -/
theorem starProjection_eigenspace_idGroup_zero (v : H) :
    (idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear 0).starProjection v = v :=
  Submodule.starProjection_eq_self_iff.2 (by simp)

/-- The measure `c δ₀` is finite. -/
instance instIsFiniteMeasureOfRealSmulDirac (c : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac (0 : ℝ)) :=
  Measure.smul_finite _ ENNReal.ofReal_ne_top

omit [CompleteSpace H] in
/-- The measure `‖v‖² δ₀` represents `t ↦ ⟪v, U_t v⟫ = ‖v‖²`. -/
theorem inner_idGroup_eq_charFun (v : H) (t : ℝ) :
    ⟪v, idGroup t v⟫_ℂ = charFun (ENNReal.ofReal (‖v‖ ^ 2) • Measure.dirac (0 : ℝ)) t := by
  rw [charFun_apply_real, integral_smul_measure, integral_dirac, idGroup_apply,
    inner_self_eq_norm_sq_to_K, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp

/-- **The atomic-mass identity at frequency `0`**: `‖P₀ v‖² = ‖v‖² = σ_v({0})`. -/
example (v : H) :
    ‖(idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear 0).starProjection v‖ ^ 2 =
      (ENNReal.ofReal (‖v‖ ^ 2) • Measure.dirac (0 : ℝ)).real {0} := by
  rw [isUnitary_idGroup.norm_starProjection_eigenspace_sq_eq_measureReal_singleton 0 v
    (inner_idGroup_eq_charFun v)]

/-- Both sides of the atomic-mass identity: `‖P₀ v‖² = ‖v‖²`. -/
example (v : H) :
    ‖(idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear 0).starProjection v‖ ^ 2 =
      ‖v‖ ^ 2 := by
  rw [starProjection_eigenspace_idGroup_zero]

/-- **The twisted average** of the identity group at `a ≠ 0` is
`A_T^a v = ((1 − exp(−2πiaT)) / (2πiaT)) v`. -/
theorem twistedAverage_idGroup {a : ℝ} (ha : a ≠ 0) (T : ℝ) (v : H) :
    (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • idGroup t v =
      ((1 - exp (-(2 * π * a * T * I))) / (2 * π * a * T * I)) • v := by
  have hc : (-(2 * π * a * I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, ha, I_ne_zero]
  change (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • v = _
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
    ring_nf

/-- **The twisted averages at `a ≠ 0` tend to `0`**: by the mean ergodic theorem their limit lies
in the eigenspace `E_a = {0}`. -/
theorem tendsto_twistedAverage_idGroup {a : ℝ} (ha : a ≠ 0) (v : H) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
        ∫ t in (0 : ℝ)..T, exp (-(2 * π * a * t * I)) • idGroup t v) atTop (𝓝 0) := by
  obtain ⟨w, hw, -, hlim, -⟩ := isUnitary_idGroup.exists_tendsto_twistedAverage a v
  have hmem : w ∈ idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear
      (2 * π * a) := by
    rw [StronglyContinuousGroup.mem_eigenspace_iff]
    intro t
    rw [hw t]
    push_cast
    rfl
  rw [eigenspace_idGroup_of_ne_zero (by positivity), Submodule.mem_bot] at hmem
  rwa [hmem] at hlim

/-- At `a ≠ 0` both sides of the atomic-mass identity vanish: `‖P_a v‖² = 0 = σ_v({2πa})`. -/
example {a : ℝ} (ha : a ≠ 0) (v : H) :
    ‖(idGroup.eigenspace (isUnitary_idGroup (H := H)).isComplexLinear
        (2 * π * a)).starProjection v‖ ^ 2 = 0 ∧
      (ENNReal.ofReal (‖v‖ ^ 2) • Measure.dirac (0 : ℝ)).real {2 * π * a} = 0 := by
  have h2a : 2 * π * a ≠ 0 := by positivity
  refine ⟨by simp [eigenspace_idGroup_of_ne_zero h2a], ?_⟩
  simp [measureReal_def, Measure.dirac_apply', h2a.symm]

end TauCeti.Examples.TwistedAverageChecks
