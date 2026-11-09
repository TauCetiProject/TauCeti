/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.Normed.Operator.IdempotentRange

/-!
# Spectral projections of self-adjoint operators

For a bounded self-adjoint operator `T` on a Hilbert space and a set `Ω ⊆ ℝ`, the spectral
projection `𝟙_Ω(T)` is computed by the real continuous functional calculus; it is a genuine
projection when the indicator of `Ω` is continuous on the spectrum of `T`, for instance when the
spectrum avoids the frontier of `Ω`. This file records how these projections depend on `Ω` and on
`T`.

The operator `T ↦ 𝟙_Ω(T)` is continuous near a self-adjoint `T₀` whose spectrum avoids the
frontier of `Ω`, by upper hemicontinuity of the spectrum and continuity of the functional
calculus. Since the rank of a continuous family of projections is locally constant, the range of
`𝟙_Ω(T)` is then isomorphic to that of `𝟙_Ω(T₀)` for self-adjoint `T` near `T₀`.

The functional calculus is used on a Hilbert space over any `RCLike` field for which the real
continuous functional calculus is isometric: complex Hilbert spaces, and real ones by
`ContinuousLinearMap.instIsometricContinuousFunctionalCalculusRealIsSelfAdjoint`.

## Main results

* `IsSelfAdjoint.eventually_nonempty_continuousLinearEquiv_range_cfc_indicator`: if the spectrum
  of a self-adjoint `T₀` avoids the frontier of `Ω`, then for self-adjoint `T` near `T₀` the
  ranges of `𝟙_Ω(T)` and `𝟙_Ω(T₀)` are isomorphic.
* `TauCeti.range_cfc_indicator_le_of_subset`: spectral projections are monotone in the set.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAlgebra ℝ (E →L[𝕜] E)] [IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- **Spectral projections have locally constant rank.** If the spectrum of a self-adjoint
operator `T₀` avoids the frontier of `Ω`, then for every self-adjoint `T` near `T₀` the ranges of
the spectral projections `𝟙_Ω(T₀)` and `𝟙_Ω(T)` are isomorphic. -/
theorem _root_.IsSelfAdjoint.eventually_nonempty_continuousLinearEquiv_range_cfc_indicator
    {T₀ : E →L[𝕜] E} (hT₀ : IsSelfAdjoint T₀) {Ω : Set ℝ}
    (hΩ : Disjoint (spectrum ℝ T₀) (frontier Ω)) :
    ∀ᶠ T in 𝓝[{T | IsSelfAdjoint T}] T₀,
      Nonempty ((cfc (Ω.indicator 1) T₀).range ≃L[𝕜] (cfc (Ω.indicator 1) T).range) := by
  set U : Set (E →L[𝕜] E) := {T | IsSelfAdjoint T ∧ Disjoint (spectrum ℝ T) (frontier Ω)}
  -- `U` is a neighbourhood of `T₀` among the self-adjoint operators.
  have hU : U ∈ 𝓝[{T | IsSelfAdjoint T}] T₀ := by
    have h := (upperHemicontinuous_spectrum ℝ (E →L[𝕜] E)).upperHemicontinuousAt T₀ _
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 hΩ.subset_compl_right)
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with T hT hsa
    exact ⟨hsa, subset_compl_iff_disjoint_right.1 (subset_of_mem_nhdsSet hT)⟩
  -- The spectral projection is continuous on `U`, so its rank is locally constant there.
  have hcont : ContinuousOn (fun T ↦ cfc (Ω.indicator (1 : ℝ → ℝ)) T) U :=
    ContinuousOn.cfc_of_mem_nhdsSet _ (s := (frontier Ω)ᶜ)
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 <| iUnion₂_subset fun T hT ↦
        hT.2.subset_compl_right) continuousOn_id (fun T hT ↦ hT.1)
      (ContinuousOn.indicator_of_disjoint_frontier (by exact continuousOn_const)
        disjoint_compl_left)
  have hmem : T₀ ∈ U := ⟨hT₀, hΩ⟩
  have h := eventually_nonempty_continuousLinearEquiv_range
    (continuousOn_iff_continuous_domRestrict.1 hcont)
    (fun T ↦ (isStarProjection_cfc_indicator (T : E →L[𝕜] E) Ω).isIdempotentElem) ⟨T₀, hmem⟩
  refine nhdsWithin_le_of_mem hU ?_
  rw [nhdsWithin_eq_map_subtype_coe hmem]
  exact Filter.eventually_map.2 h

/-- If `Ω' ⊆ Ω` and both indicators are continuous on the spectrum of `T`, the spectral projection
onto `Ω'` maps into the range of the spectral projection onto `Ω`. -/
theorem range_cfc_indicator_le_of_subset {T : E →L[𝕜] E} {Ω Ω' : Set ℝ} (hsub : Ω' ⊆ Ω)
    (hΩ : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hΩ' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    (cfc (Ω'.indicator 1) T).range ≤ (cfc (Ω.indicator 1) T).range := by
  have h : cfc (Ω'.indicator (1 : ℝ → ℝ)) T = cfc (Ω.indicator 1) T * cfc (Ω'.indicator 1) T := by
    rw [← cfc_mul _ _ T hΩ hΩ', ← Pi.mul_def, ← inter_indicator_one, inter_eq_right.2 hsub]
  rw [h, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.range_comp_le_range _ _

end TauCeti
