/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of Hilbert-space adjoints

Between Hilbert spaces the compact operators are closed under adjoints. Together with the
two-sided ideal property (`IsCompactOperator.mul_left`, `IsCompactOperator.mul_right` in
`TauCeti.Analysis.Normed.Operator.Compact.Basic`), this makes the compact operators on a Hilbert
space a two-sided `*`-ideal. These are the algebraic rules used to manipulate the compactness
conditions in the definition of a Fredholm module, such as compactness of commutators `[F, a]` and
of the defects `(F² - 1) a`. The Banach-space dual of a compact operator is treated separately in
`TauCeti.Analysis.Normed.Operator.Compact.Adjoint`.

The adjoint statement uses approximation numbers: an operator into a Hilbert space is compact
exactly when its approximation numbers tend to zero, and an operator and its adjoint have the same
approximation numbers.

## Main declarations

* `IsCompactOperator.adjoint`: the Hilbert-space adjoint of a compact operator is compact.
* `ContinuousLinearMap.isCompactOperator_adjoint_iff`: `T†` is compact exactly when `T` is.
* `IsCompactOperator.star`: on a Hilbert space, `star T` is compact when `T` is.
* `ContinuousLinearMap.isCompactOperator_star_iff`: `star T` is compact exactly when `T` is.
* `ContinuousLinearMap.isCompactOperator_adjoint_comp_self_iff`,
  `ContinuousLinearMap.isCompactOperator_comp_adjoint_self_iff`,
  `ContinuousLinearMap.isCompactOperator_star_mul_self_iff`,
  `ContinuousLinearMap.isCompactOperator_mul_star_self_iff`: a Gram operator `T† T` or `T T†` is
  compact if and only if `T` is.
* `IsCompactOperator.conjStarAlgEquiv`: conjugating by a unitary preserves compactness.
-/

public section

open scoped InnerProduct InnerProductSpace

namespace IsCompactOperator

section Adjoint

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Compactness of the adjoint.** The Hilbert-space adjoint of a compact operator is compact. -/
theorem adjoint {T : E →L[𝕜] F} (hT : IsCompactOperator T) : IsCompactOperator (T†) := by
  rw [ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue] at hT ⊢
  rwa [funext (ContinuousLinearMap.singularValue_adjoint T)]

/-- On a Hilbert space, the star of a compact operator, its adjoint, is compact. -/
theorem star {T : E →L[𝕜] E} (hT : IsCompactOperator T) : IsCompactOperator ⇑(star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact hT.adjoint

/-- Conjugating a compact operator by a unitary `U : E ≃ F` gives a compact operator
`U T U*`. -/
theorem conjStarAlgEquiv {T : E →L[𝕜] E} (hT : IsCompactOperator T) (U : E ≃ₗᵢ[𝕜] F) :
    IsCompactOperator (U.conjStarAlgEquiv T) := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_comp]
  exact (hT.comp_clm _).clm_comp _

end Adjoint

end IsCompactOperator

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A bounded operator between Hilbert spaces is compact exactly when its adjoint is. -/
@[simp]
theorem isCompactOperator_adjoint_iff {T : E →L[𝕜] F} :
    IsCompactOperator (T†) ↔ IsCompactOperator T :=
  ⟨fun h ↦ by simpa using h.adjoint, IsCompactOperator.adjoint⟩

/-- On a Hilbert space, an operator is compact exactly when its star, its adjoint, is. -/
@[simp]
theorem isCompactOperator_star_iff {T : E →L[𝕜] E} :
    IsCompactOperator ⇑(star T) ↔ IsCompactOperator T := by
  rw [star_eq_adjoint, isCompactOperator_adjoint_iff]

/-- The source Gram operator `T† ∘L T` of a bounded operator between Hilbert spaces is compact
if and only if `T` is compact. -/
@[simp]
theorem isCompactOperator_adjoint_comp_self_iff {T : E →L[𝕜] F} :
    IsCompactOperator ⇑(T† ∘L T) ↔ IsCompactOperator T := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.clm_comp (T†)⟩
  refine (isCompactOperator_iff_totallyBounded_image_closedBall T.toLinearMap one_pos).mpr ?_
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Cover `(T† ∘L T) '' closedBall 0 1` by finitely many balls of radius `ε² / 4` centred at
  -- images `(T† ∘L T) (g z)` of unit-ball vectors; Cauchy–Schwarz transfers this to an `ε`-net
  -- for `T '' closedBall 0 1`.
  obtain ⟨t, hts, htf, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded (h.totallyBounded_image_closedBall 1) (ε ^ 2 / 4)
      (by positivity)
  choose g hg_mem hg_eq using fun z : t ↦ hts z.2
  refine ⟨Set.range (fun z : t ↦ T (g z)), ?_, ?_⟩
  · have : Finite t := htf
    exact Set.finite_range _
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_image_of_mem _ hx))
    refine Set.mem_iUnion₂.mpr ⟨T (g ⟨z, hzt⟩), ⟨⟨z, hzt⟩, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, coe_coe, ← map_sub]
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hg1 : ‖g ⟨z, hzt⟩‖ ≤ 1 := by simpa using hg_mem ⟨z, hzt⟩
    have hdiff : ‖x - g ⟨z, hzt⟩‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    have hgram : ‖(T† ∘L T) (x - g ⟨z, hzt⟩)‖ < ε ^ 2 / 4 := by
      have hg' : (T† ∘L T) (g ⟨z, hzt⟩) = z := hg_eq ⟨z, hzt⟩
      rw [map_sub, hg']
      simpa [dist_eq_norm] using Metric.mem_ball.mp hxz
    have hsq : ‖T (x - g ⟨z, hzt⟩)‖ ^ 2 < ε ^ 2 := by
      calc ‖T (x - g ⟨z, hzt⟩)‖ ^ 2
          = RCLike.re ⟪x - g ⟨z, hzt⟩, (T† ∘L T) (x - g ⟨z, hzt⟩)⟫_𝕜 :=
            T.apply_norm_sq_eq_inner_adjoint_right _
        _ ≤ ‖x - g ⟨z, hzt⟩‖ * ‖(T† ∘L T) (x - g ⟨z, hzt⟩)‖ :=
            (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ ≤ 2 * (ε ^ 2 / 4) := by gcongr
        _ < ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- The target Gram operator `T ∘L T†` of a bounded operator between Hilbert spaces is compact
if and only if `T` is compact. -/
@[simp]
theorem isCompactOperator_comp_adjoint_self_iff {T : E →L[𝕜] F} :
    IsCompactOperator ⇑(T ∘L T†) ↔ IsCompactOperator T := by
  simpa using
    (isCompactOperator_adjoint_comp_self_iff (T := T†)).trans isCompactOperator_adjoint_iff

/-- On a Hilbert space, `star T * T` is compact if and only if `T` is compact. -/
theorem isCompactOperator_star_mul_self_iff {T : E →L[𝕜] E} :
    IsCompactOperator ⇑(star T * T) ↔ IsCompactOperator T := by
  rw [star_eq_adjoint, mul_def, isCompactOperator_adjoint_comp_self_iff]

/-- On a Hilbert space, `T * star T` is compact if and only if `T` is compact. -/
theorem isCompactOperator_mul_star_self_iff {T : E →L[𝕜] E} :
    IsCompactOperator ⇑(T * star T) ↔ IsCompactOperator T := by
  rw [star_eq_adjoint, mul_def, isCompactOperator_comp_adjoint_self_iff]

end ContinuousLinearMap
