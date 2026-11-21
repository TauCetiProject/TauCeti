/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.Semigroups.Group.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import TauCeti.Analysis.Bochner.CharFun.Bochner
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener

/-!
# Spectral measure and atomic-mass identity for unitary C₀-groups

For a unitary C₀-group `U` on a complex inner product space `H` and any vector `v : H`, the
correlation function `t ↦ ⟪v, U t v⟫_ℂ` is continuous and positive definite
(`IsUnitary.isPositiveDefiniteSub_inner`), so Bochner's theorem supplies a unique finite Borel
spectral measure `σ` on `ℝ` with `⟪v, U t v⟫_ℂ = charFun σ t`
(`IsUnitary.existsUnique_spectralMeasure`).

When `H` is complete, combining the twisted mean ergodic theorem
(`IsUnitary.tendsto_twistedAverage_starProjection`) with atomic-mass inversion for characteristic
functions (`MeasureTheory.tendsto_average_exp_mul_charFun`) identifies the squared norm of the
eigenprojection onto `U.eigenspace hU.isComplexLinear ω` as the spectral atomic mass `σ.real {ω}`
(`IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`).

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isPositiveDefiniteSub_inner`: positive
  definiteness of `t ↦ ⟪v, U t v⟫_ℂ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.existsUnique_spectralMeasure`: existence and
  uniqueness of the Bochner spectral measure `σ` representing `t ↦ ⟪v, U t v⟫_ℂ`.
* `IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`:
  `‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω}`.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U : StronglyContinuousGroup H}

/-- The correlation function `t ↦ ⟪v, U t v⟫_ℂ` of a unitary C₀-group is positive definite. -/
theorem isPositiveDefiniteSub_inner (hU : U.IsUnitary) (v : H) :
    TauCeti.IsPositiveDefiniteSub fun t : ℝ ↦ ⟪v, U t v⟫_ℂ := by
  refine TauCeti.IsPositiveDefiniteSub.of_posSemidef ?_
  have hgram : (fun a b : ℝ ↦ ⟪v, U (a - b) v⟫_ℂ) =
      Matrix.gram ℂ (fun t : ℝ ↦ U (-t) v) := by
    ext a b
    rw [Matrix.gram_apply]
    calc ⟪v, U (a - b) v⟫_ℂ
        = ⟪U (-a) v, U (-a) (U (a - b) v)⟫_ℂ := (hU.inner_map_map (-a) _ _).symm
      _ = ⟪U (-a) v, U (-b) v⟫_ℂ := by
          rw [← U.map_add_apply, ← add_sub_assoc, neg_add_cancel, zero_sub]
  rw [hgram]
  exact Matrix.posSemidef_gram ℂ (fun t : ℝ ↦ U (-t) v)

/-- **Spectral measure of a unitary C₀-group.** For every vector `v` in a complex inner product
space and every unitary C₀-group `U`, there is a unique finite Borel measure `σ` on `ℝ` whose
characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem existsUnique_spectralMeasure (hU : U.IsUnitary) (v : H) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have hboch := (TauCeti.bochner_charFun fun t : ℝ ↦ ⟪v, U t v⟫_ℂ).mp
    ⟨continuous_const.inner (U.continuous_orbit v), hU.isPositiveDefiniteSub_inner v⟩
  simpa only [funext_iff, eq_comm (a := ⟪v, U _ v⟫_ℂ)] using hboch

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
    MeasureTheory.tendsto_average_exp_mul_charFun σ ω
  have hfun : (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ) =
      fun T : ℝ ↦
        (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t := by
    funext T
    have hint : IntervalIntegrable
        (fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I)) • U t v) volume 0 T :=
      ((by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I))).smul
        (U.continuous_orbit v)).intervalIntegrable 0 T
    rw [inner_smul_right_eq_smul, Complex.real_smul, Complex.ofReal_inv]
    congr 1
    have hcomm := (innerSL ℂ v).intervalIntegral_comp_comm hint
    simpa only [innerSL_apply_apply, inner_smul_right, hσ] using hcomm.symm
  rw [hfun] at hlim₁
  have heq : ⟪v, P v⟫_ℂ = (σ.real {ω} : ℂ) := tendsto_nhds_unique hlim₁ hlim₂
  have hre := congrArg Complex.re heq
  rw [← Submodule.inner_starProjection_left_eq_right, ← RCLike.re_to_complex,
    Submodule.re_inner_starProjection_eq_normSq, ← Submodule.norm_coe,
    ← Submodule.starProjection_apply, Complex.ofReal_re] at hre
  exact hre

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
