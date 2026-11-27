/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Atoms
public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Basic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener
import TauCeti.Analysis.SpecificLimits.Cesaro.Integral
import TauCeti.Analysis.InnerProductSpace.OperatorIdentities

/-!
# Time averages of correlations of a unitary group

Let `U` be a unitary C₀-group on a complete complex Hilbert space `H` and `v ∈ H`. The Cesàro
averages of the squared correlations `|⟪v, U_t v⟫|²` converge to the sum of the fourth powers of
the norms of the eigenprojections of `v`:

`T⁻¹ ∫₀ᵀ |⟪v, U_t v⟫|² dt → Σ_ω ‖P_ω v‖⁴`

(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_norm_inner_sq`), where
`P_ω` is the orthogonal projection onto the common eigenspace `{u : U_t u = e^{iωt} u}`. Hence the
averages tend to `0` exactly when `v` is orthogonal to every eigenspace
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_norm_inner_sq_zero_iff`).
This is the Hilbert-space half of the eigenfunction criterion for weak mixing.

The squared limit is proved as follows: Bochner's theorem gives the spectral measure `σ_v` with
`charFun σ_v t = ⟪v, U_t v⟫` (`IsUnitary.existsUnique_spectralMeasure`), Wiener's lemma
(`TauCeti.tendsto_average_norm_charFun_sq`) gives the limit `Σ_ξ σ_v({ξ})²`, and the
atomic-mass identity
(`IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`) gives
`σ_v({ω}) = ‖P_ω v‖²`.

For vectors `f`, `g` orthogonal to every common eigenspace the Cesàro averages of the mixed
correlations vanish too: `T⁻¹ ∫₀ᵀ |⟪g, U_t f⟫| dt → 0`
(`IsUnitary.tendsto_average_norm_inner_of_forall_mem_orthogonal`).
The diagonal case follows from the squared one since `x ≤ x² / ε + ε` for `x ≥ 0` and `ε > 0`,
and polarization (`LinearMap.norm_inner_le_add`) bounds `|⟪g, U_t f⟫|` by a quarter of the sum
of the four diagonal correlations of `f ± g` and `f ± i g`. If `U` fixes a unit vector `e` and every
eigenvector is a multiple of `e`, the centered correlations `⟪g, U_t f⟫ - ⟪e, f⟫ ⟪g, e⟫` therefore
vanish in Cesàro mean for all `f`, `g`
(`IsUnitary.tendsto_average_norm_inner_sub_of_forall_mem_eigenspace`).

## References

* M. Hochman, *Notes on ergodic theory* (2012), Section 6.6.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U : StronglyContinuousGroup H}

/-- **Averaged squared correlations.** For a unitary C₀-group `U` on a complete complex Hilbert
space and `v ∈ H`, `T⁻¹ ∫₀ᵀ ‖⟪v, U_t v⟫‖² dt → Σ_ω ‖P_ω v‖⁴`, where `P_ω` is the orthogonal
projection onto the common eigenspace at angular frequency `ω`. -/
theorem tendsto_average_norm_inner_sq (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪v, U t v⟫_ℂ‖ ^ 2) atTop
      (𝓝 (∑' ω : ℝ, ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 4)) := by
  obtain ⟨σ, ⟨hσf, hσ⟩, -⟩ := hU.existsUnique_spectralMeasure v
  have hmass (ω : ℝ) : ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 4 =
      σ.real {ω} ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      hU.norm_starProjection_eigenspace_sq_eq_measureReal_singleton ω v hσ]
  simp_rw [hmass, hσ]
  exact tendsto_average_norm_charFun_sq σ

/-- **Vanishing averaged correlations.** For a unitary C₀-group `U` on a complete complex Hilbert
space and `v ∈ H`, `T⁻¹ ∫₀ᵀ ‖⟪v, U_t v⟫‖² dt → 0` iff `v` is orthogonal to every common
eigenspace of `U`. -/
theorem tendsto_average_norm_inner_sq_zero_iff (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪v, U t v⟫_ℂ‖ ^ 2) atTop (𝓝 0) ↔
      ∀ ω : ℝ, v ∈ (U.eigenspace hU.isComplexLinear ω)ᗮ := by
  obtain ⟨σ, ⟨hσf, hσ⟩, -⟩ := hU.existsUnique_spectralMeasure v
  simp_rw [hσ, tendsto_average_norm_charFun_sq_zero_iff σ,
    ← Submodule.starProjection_apply_eq_zero_iff]
  refine forall_congr' fun ω => ?_
  rw [← norm_eq_zero, ← measureReal_eq_zero_iff (measure_ne_top σ {ω}),
    ← hU.norm_starProjection_eigenspace_sq_eq_measureReal_singleton ω v hσ]
  exact pow_eq_zero_iff two_ne_zero

/-- **Vanishing averaged correlations.** For a unitary C₀-group `U` on a complete complex Hilbert
space and `v ∈ H` orthogonal to every common eigenspace of `U`, `T⁻¹ ∫₀ᵀ ‖⟪v, U_t v⟫‖ dt → 0`. -/
theorem tendsto_average_norm_inner_self_of_forall_mem_orthogonal (hU : U.IsUnitary) {v : H}
    (hv : ∀ ω : ℝ, v ∈ (U.eigenspace hU.isComplexLinear ω)ᗮ) :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪v, U t v⟫_ℂ‖) atTop (𝓝 0) := by
  have hsq := (hU.tendsto_average_norm_inner_sq_zero_iff v).2 hv
  have hc : Continuous fun t ↦ ‖⟪v, U t v⟫_ℂ‖ :=
    (continuous_const.inner (U.continuous_orbit v)).norm
  refine TauCeti.tendsto_average_of_forall_le (fun T ↦ hc.intervalIntegrable 0 T)
    (fun _ ↦ norm_nonneg _) fun ε hε ↦ ⟨fun t ↦ ε⁻¹ * ‖⟪v, U t v⟫_ℂ‖ ^ 2,
      fun T ↦ (continuous_const.mul (hc.pow 2)).intervalIntegrable 0 T, ?_, fun t ↦ ?_⟩
  · simpa [intervalIntegral.integral_const_mul, mul_left_comm _ ε⁻¹] using hsq.const_mul ε⁻¹
  · have hx := norm_nonneg ⟪v, U t v⟫_ℂ
    dsimp only
    rw [← div_eq_inv_mul, div_add' _ _ _ hε.ne', le_div_iff₀ hε]
    nlinarith [sq_nonneg (‖⟪v, U t v⟫_ℂ‖ - ε), mul_nonneg hx hε.le]

/-- **Vanishing averaged mixed correlations.** For a unitary C₀-group `U` on a complete complex
Hilbert space and `f g ∈ H` orthogonal to every common eigenspace of `U`,
`T⁻¹ ∫₀ᵀ ‖⟪g, U_t f⟫‖ dt → 0`. -/
theorem tendsto_average_norm_inner_of_forall_mem_orthogonal (hU : U.IsUnitary) {f g : H}
    (hf : ∀ ω : ℝ, f ∈ (U.eigenspace hU.isComplexLinear ω)ᗮ)
    (hg : ∀ ω : ℝ, g ∈ (U.eigenspace hU.isComplexLinear ω)ᗮ) :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪g, U t f⟫_ℂ‖) atTop (𝓝 0) := by
  have hc (v : H) : Continuous fun t ↦ ‖⟪v, U t v⟫_ℂ‖ :=
    (continuous_const.inner (U.continuous_orbit v)).norm
  have h₁ := hU.tendsto_average_norm_inner_self_of_forall_mem_orthogonal
    fun ω ↦ Submodule.add_mem _ (hf ω) (hg ω)
  have h₂ := hU.tendsto_average_norm_inner_self_of_forall_mem_orthogonal
    fun ω ↦ Submodule.sub_mem _ (hf ω) (hg ω)
  have h₃ := hU.tendsto_average_norm_inner_self_of_forall_mem_orthogonal
    fun ω ↦ Submodule.add_mem _ (hf ω) (Submodule.smul_mem _ Complex.I (hg ω))
  have h₄ := hU.tendsto_average_norm_inner_self_of_forall_mem_orthogonal
    fun ω ↦ Submodule.sub_mem _ (hf ω) (Submodule.smul_mem _ Complex.I (hg ω))
  have hsum := TauCeti.tendsto_average_add
    (fun T ↦ (((hc _).add (hc _)).add (hc _)).intervalIntegrable 0 T)
    (fun T ↦ (hc _).intervalIntegrable 0 T)
    (TauCeti.tendsto_average_add (fun T ↦ ((hc _).add (hc _)).intervalIntegrable 0 T)
      (fun T ↦ (hc _).intervalIntegrable 0 T)
      (TauCeti.tendsto_average_add (fun T ↦ (hc _).intervalIntegrable 0 T)
        (fun T ↦ (hc _).intervalIntegrable 0 T) h₁ h₂) h₃) h₄
  simp only [add_zero] at hsum
  refine TauCeti.tendsto_average_of_forall_le
    (fun T ↦ (continuous_const.inner (U.continuous_orbit f)).norm.intervalIntegrable 0 T)
    (fun _ ↦ norm_nonneg _) fun ε hε ↦ ⟨_,
      fun T ↦ ((((hc _).add (hc _)).add (hc _)).add (hc _)).intervalIntegrable 0 T, hsum,
      fun t ↦ ?_⟩
  have hpol := (U.complexLinearOperator hU.isComplexLinear t : H →ₗ[ℂ] H).norm_inner_le_add g f
  simp only [ContinuousLinearMap.coe_coe, complexLinearOperator_apply] at hpol
  simp only [Pi.add_apply]
  linarith [norm_nonneg ⟪f + g, U t (f + g)⟫_ℂ, norm_nonneg ⟪f - g, U t (f - g)⟫_ℂ,
    norm_nonneg ⟪f + Complex.I • g, U t (f + Complex.I • g)⟫_ℂ,
    norm_nonneg ⟪f - Complex.I • g, U t (f - Complex.I • g)⟫_ℂ]

/-- **Vanishing averaged centered correlations.** Let `U` be a unitary C₀-group on a complete
complex Hilbert space, fixing a unit vector `e`, whose eigenvectors at every frequency are
multiples of `e`. Then for all `f g ∈ H`, `T⁻¹ ∫₀ᵀ ‖⟪g, U_t f⟫ - ⟪e, f⟫ ⟪g, e⟫‖ dt → 0`. -/
theorem tendsto_average_norm_inner_sub_of_forall_mem_eigenspace (hU : U.IsUnitary) {e : H}
    (he : ⟪e, e⟫_ℂ = 1) (hUe : ∀ t, U t e = e)
    (heig : ∀ (ω : ℝ) (u : H), u ∈ U.eigenspace hU.isComplexLinear ω → ∃ c : ℂ, u = c • e)
    (f g : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪g, U t f⟫_ℂ - ⟪e, f⟫_ℂ * ⟪g, e⟫_ℂ‖) atTop
      (𝓝 0) := by
  -- the centered correlation is the correlation of `f - ⟪e, f⟫ e` and `g - ⟪e, g⟫ e`, which
  -- are orthogonal to every common eigenspace
  have horth (v : H) (ω : ℝ) : v - ⟪e, v⟫_ℂ • e ∈ (U.eigenspace hU.isComplexLinear ω)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu ↦ ?_
    obtain ⟨c, rfl⟩ := heig ω u hu
    simp only [inner_smul_left, inner_sub_right, inner_smul_right, he, mul_one]
    ring
  have hcorr (t : ℝ) : ⟪g, U t f⟫_ℂ - ⟪e, f⟫_ℂ * ⟪g, e⟫_ℂ =
      ⟪g - ⟪e, g⟫_ℂ • e, U t (f - ⟪e, f⟫_ℂ • e)⟫_ℂ := by
    have hinv : ⟪e, U t f⟫_ℂ = ⟪e, f⟫_ℂ := by
      rw [← hU.inner_map_map t e f, hUe]
    simp only [map_sub, hU.map_smul, hUe, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, hinv, he, inner_conj_symm]
    ring
  simpa only [hcorr] using
    hU.tendsto_average_norm_inner_of_forall_mem_orthogonal (horth f) (horth g)

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup
