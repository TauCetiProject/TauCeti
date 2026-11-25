/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Atoms
public import TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Basic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener

/-!
# Time averages of squared correlations of a unitary group

Let `U` be a unitary C₀-group on a complete complex Hilbert space `H` and `v ∈ H`. The Cesàro
averages of the squared correlations `|⟪v, U_t v⟫|²` converge to the sum of the fourth powers of
the norms of the eigenprojections of `v`:

`T⁻¹ ∫₀ᵀ |⟪v, U_t v⟫|² dt → Σ_ω ‖P_ω v‖⁴`

(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_norm_inner_sq`), where
`P_ω` is the orthogonal projection onto the common eigenspace `{u : U_t u = e^{iωt} u}`. Hence the
averages tend to `0` exactly when `v` is orthogonal to every eigenspace
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_norm_inner_sq_zero_iff`).
This is the Hilbert-space half of the eigenfunction criterion for weak mixing.

The proof: Bochner's theorem gives the spectral measure `σ_v` with `charFun σ_v t = ⟪v, U_t v⟫`
(`IsUnitary.existsUnique_spectralMeasure`), Wiener's lemma
(`TauCeti.tendsto_average_norm_charFun_sq`) gives the limit `Σ_ξ σ_v({ξ})²`, and the
atomic-mass identity
(`IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`) gives
`σ_v({ω}) = ‖P_ω v‖²`.

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

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup
