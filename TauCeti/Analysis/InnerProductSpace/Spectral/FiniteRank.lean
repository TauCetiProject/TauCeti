/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.ContinuousFunctionalCalculus
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import TauCeti.Analysis.Normed.Operator.Compact.Spectrum
import TauCeti.LinearAlgebra.End.Idempotent

/-!
# Spectral projections of finite rank

Let `T` be a self-adjoint operator on a real or complex Hilbert space, and `Ω ⊆ ℝ` a set whose
frontier avoids the spectrum of `T`, so that the continuous functional calculus defines the
spectral projection `cfc (Ω.indicator 1) T`. This file relates these projections for different
sets, and their finite ranks:

* **Monotonicity.** For `Ω ⊆ Ω'` the range of the projection for `Ω` lies in the range of the
  projection for `Ω'`, since the second projection fixes the first.
* **Additivity.** For disjoint `Ω₁` and `Ω₂` the projections are orthogonal and add up to the
  projection for `Ω₁ ∪ Ω₂`, so the ranks of finite-rank projections add.
* **Finiteness of the spectrum.** If the spectral projection for `Ω` has finite rank, the spectrum
  of `T` meets `Ω` in finitely many points. The operator
  `cfc (x ↦ Ω.indicator 1 x * (x - m + 1)) T`, for a lower bound `m` of the spectrum, has finite
  rank and so is compact, and by the spectral mapping theorem its spectrum contains the shifted
  points `x - m + 1 ≥ 1` of the spectrum of `T` in `Ω`. A compact operator has only finitely many
  spectral values of norm at least `1`.

Together with `Set.Finite.continuousOn_indicator`, finiteness shows that the indicator of a
subset of `Ω`, such as `[0, c]` inside `[-c, c]`, is continuous on the spectrum even when its
own frontier meets it: these are the spectral projections counting eigenvalues in `[0, c]` from
which the spectral flow of a path of self-adjoint Fredholm operators is built.

## Main results

* `ContinuousLinearMap.range_cfc_indicator_le_of_subset`: monotonicity of spectral projections.
* `ContinuousLinearMap.finrank_range_cfc_indicator_union`: additivity of their ranks.
* `IsSelfAdjoint.finite_spectrum_inter_of_finiteDimensional_range_cfc_indicator`: a spectral
  projection of finite rank sees finitely many spectral values.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
-/

public section

open Set

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [Algebra ℝ (H →L[𝕜] H)] [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace ContinuousLinearMap

/-- For `Ω ⊆ Ω'`, the spectral projection for `Ω` has range inside that for `Ω'`, provided both
indicators are continuous on the spectrum. -/
theorem range_cfc_indicator_le_of_subset (T : H →L[𝕜] H) {Ω Ω' : Set ℝ} (hΩ : Ω ⊆ Ω')
    (hf : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hf' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
    (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range ≤ (cfc (Ω'.indicator (1 : ℝ → ℝ)) T).range := by
  rw [← inter_eq_right.2 hΩ, ← TauCeti.cfc_indicator_mul_cfc_indicator T hf' hf]
  exact LinearMap.range_comp_le_range _ _

/-- For disjoint `Ω₁` and `Ω₂` whose indicators are continuous on the spectrum, the rank of the
spectral projection for `Ω₁ ∪ Ω₂` is the sum of the ranks of the projections for `Ω₁` and `Ω₂`,
when these are finite. -/
theorem finrank_range_cfc_indicator_union (T : H →L[𝕜] H) {Ω₁ Ω₂ : Set ℝ} (h : Disjoint Ω₁ Ω₂)
    (hf₁ : ContinuousOn (Ω₁.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hf₂ : ContinuousOn (Ω₂.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    [FiniteDimensional 𝕜 (cfc (Ω₁.indicator (1 : ℝ → ℝ)) T).range]
    [FiniteDimensional 𝕜 (cfc (Ω₂.indicator (1 : ℝ → ℝ)) T).range] :
    Module.finrank 𝕜 (cfc ((Ω₁ ∪ Ω₂).indicator (1 : ℝ → ℝ)) T).range =
      Module.finrank 𝕜 (cfc (Ω₁.indicator (1 : ℝ → ℝ)) T).range +
        Module.finrank 𝕜 (cfc (Ω₂.indicator (1 : ℝ → ℝ)) T).range := by
  set P := cfc (Ω₁.indicator (1 : ℝ → ℝ)) T
  set Q := cfc (Ω₂.indicator (1 : ℝ → ℝ)) T
  have hprod (Ω Ω' : Set ℝ) (hd : Disjoint Ω Ω')
      (hf : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
      (hf' : ContinuousOn (Ω'.indicator (1 : ℝ → ℝ)) (spectrum ℝ T)) :
      cfc (Ω.indicator (1 : ℝ → ℝ)) T * cfc (Ω'.indicator (1 : ℝ → ℝ)) T = 0 := by
    simp [TauCeti.cfc_indicator_mul_cfc_indicator T hf hf', hd.inter_eq]
  have hsum : cfc ((Ω₁ ∪ Ω₂).indicator (1 : ℝ → ℝ)) T = P + Q := by
    rw [← cfc_add T _ _ hf₁ hf₂]
    exact cfc_congr fun x _ ↦ congr_fun (indicator_union_of_disjoint h _) x
  -- Pass to the underlying linear endomorphisms, which are orthogonal idempotents.
  have hP : IsIdempotentElem (P : Module.End 𝕜 H) :=
    (TauCeti.isStarProjection_cfc_indicator T Ω₁).isIdempotentElem.map toLinearMapRingHom
  have hQ : IsIdempotentElem (Q : Module.End 𝕜 H) :=
    (TauCeti.isStarProjection_cfc_indicator T Ω₂).isIdempotentElem.map toLinearMapRingHom
  have hPQ : (P : Module.End 𝕜 H) * Q = 0 := by
    simpa using congr(($(hprod Ω₁ Ω₂ h hf₁ hf₂) : Module.End 𝕜 H))
  have hQP : (Q : Module.End 𝕜 H) * P = 0 := by
    simpa using congr(($(hprod Ω₂ Ω₁ h.symm hf₂ hf₁) : Module.End 𝕜 H))
  have hrange : (P + Q).range = P.range ⊔ Q.range := by
    simpa using hP.range_add_of_mul_eq_zero hQ hQP hPQ
  rw [hsum, hrange, ← Submodule.finrank_sup_add_finrank_inf_eq,
    disjoint_iff.1 (hP.disjoint_range_of_mul_eq_zero hPQ), finrank_bot, add_zero]

end ContinuousLinearMap

namespace IsSelfAdjoint

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

/-- **A spectral projection of finite rank sees finitely many spectral values.** If the indicator
of `Ω` is continuous on the spectrum of a self-adjoint operator `T` (for instance, if the frontier
of `Ω` avoids the spectrum) and the spectral projection of `T` for `Ω` has finite rank, then the
spectrum of `T` meets `Ω` in finitely many points. -/
theorem finite_spectrum_inter_of_finiteDimensional_range_cfc_indicator {T : H →L[𝕜] H}
    (hT : IsSelfAdjoint T) {Ω : Set ℝ} (hf : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ T))
    (hP : FiniteDimensional 𝕜 (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range) :
    (spectrum ℝ T ∩ Ω).Finite := by
  obtain ⟨m, hm⟩ := (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) T).bddBelow
  -- The shift `g x = (x - m + 1) * 1_Ω(x)` is at least `1` at the spectral values in `Ω`.
  set g : ℝ → ℝ := fun x ↦ Ω.indicator (1 : ℝ → ℝ) x * (x - m + 1)
  have hg : ContinuousOn g (spectrum ℝ T) := hf.mul (by fun_prop)
  set K := cfc g T
  -- `K` factors through the spectral projection, so it has finite rank and is compact.
  have hK : K = cfc (Ω.indicator (1 : ℝ → ℝ)) T * cfc (fun x : ℝ ↦ x - m + 1) T :=
    cfc_mul _ _ T hf (by fun_prop)
  have hKc : IsCompactOperator K := by
    refine LinearMap.HasFiniteRange.isCompactOperator ?_
    have hle : (K : H →ₗ[𝕜] H).range ≤ (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range := by
      rw [hK]
      exact LinearMap.range_comp_le_range _ _
    have : FiniteDimensional 𝕜 (K : H →ₗ[𝕜] H).range := Submodule.finiteDimensional_of_le hle
    exact Module.Finite.iff_fg.1 this
  -- By spectral mapping, the shifted spectral values in `Ω` are spectral values of `K` of norm
  -- at least `1`, of which there are finitely many.
  refine ((hKc.finite_spectrum_norm_ge one_pos).preimage
    (f := fun x : ℝ ↦ (algebraMap ℝ 𝕜 (x - m + 1))) ?_).subset ?_
  · intro x _ y _ hxy
    simpa using hxy
  · rintro x ⟨hxs, hxΩ⟩
    have hgx : g x = x - m + 1 := by simp [g, hxΩ]
    have h1 : 1 ≤ x - m + 1 := by linarith [hm hxs]
    refine ⟨?_, ?_⟩
    · rw [spectrum.algebraMap_mem_iff, ← hgx, cfc_map_spectrum g T hT hg]
      exact mem_image_of_mem g hxs
    · rw [RCLike.norm_ofReal, abs_of_nonneg (by linarith)]
      exact h1

end IsSelfAdjoint
