/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Stability of surjectivity under small perturbations

Surjectivity onto a finite-dimensional space is stable under small perturbations in the operator
norm: the surjective maps form an open subset of the space of continuous linear maps. The source
is an arbitrary seminormed space over a complete nontrivially normed field.

Surjectivity onto a Banach space is stable under perturbations that are small relative to the map
itself. If `Q` is a surjective linear map from a module `D` into a Banach space and
`‖K z‖ ≤ θ * ‖Q z‖` for every `z` with `θ < 1`, then `Q + K` is surjective: `K` factors as
`S ∘ Q` with `‖S‖ ≤ θ`, and `Q + K = (1 + S) ∘ Q` with `1 + S` invertible by the Neumann series.
No topology on `D` is needed, which is what makes the statement usable for operators defined on
the domain of an unbounded operator.

Mathlib records the companion fact that a surjective continuous linear map between Banach spaces
is an open map, in `ContinuousLinearMap.isOpenMap`; the openness proved here is openness of the
locus of such maps inside `E →L[𝕜] F`, not of any one of them.

## Main results

* `TauCeti.isOpen_setOf_surjective`: surjectivity onto a finite-dimensional space is an open
  condition on continuous linear maps.
* `LinearMap.surjective_add_of_norm_le`: a surjective linear map into a Banach space stays
  surjective under a perturbation bounded by `θ < 1` times the map.
-/

public section

open Function

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Surjectivity onto a finite-dimensional space is an open condition on continuous linear
maps. -/
theorem isOpen_setOf_surjective : IsOpen {A : E →L[𝕜] F | Surjective A} := by
  rw [Metric.isOpen_iff]
  rintro A (hA : Surjective A)
  obtain ⟨R, hAR⟩ := A.exists_rightInverse_of_surjective (A.range_eq_top_of_surjective hA)
  have hAR : ∀ y, A (R y) = y := fun y ↦ by
    have := congrArg (fun g : F →L[𝕜] F ↦ g y) hAR
    simpa using this
  refine ⟨(‖R‖ + 1)⁻¹, by positivity, fun B hB ↦ ?_⟩
  have hBA : ‖B - A‖ < (‖R‖ + 1)⁻¹ := by
    rwa [Metric.mem_ball, dist_eq_norm] at hB
  have hlt : ‖B - A‖ * ‖R‖ < 1 := by
    have h₁ : ‖B - A‖ * ‖R‖ ≤ (‖R‖ + 1)⁻¹ * ‖R‖ :=
      mul_le_mul_of_nonneg_right hBA.le (norm_nonneg R)
    have h₂ : (‖R‖ + 1)⁻¹ * ‖R‖ < 1 := by
      rw [inv_mul_eq_div, div_lt_one (by positivity)]
      linarith
    linarith
  have key : ∀ y : F, ‖B (R y) - y‖ ≤ ‖B - A‖ * ‖R‖ * ‖y‖ := by
    intro y
    have hsub : B (R y) - y = (B - A) (R y) := by simp [hAR]
    rw [hsub]
    calc ‖(B - A) (R y)‖ ≤ ‖B - A‖ * ‖R y‖ := (B - A).le_opNorm _
      _ ≤ ‖B - A‖ * (‖R‖ * ‖y‖) := by gcongr; exact R.le_opNorm y
      _ = ‖B - A‖ * ‖R‖ * ‖y‖ := by ring
  have hinj : Injective ((B.comp R : F →L[𝕜] F) : F →ₗ[𝕜] F) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    have h1 : ‖y‖ ≤ ‖B - A‖ * ‖R‖ * ‖y‖ := by
      have hy' : B (R y) = 0 := hy
      have := key y
      rw [hy', zero_sub, norm_neg] at this
      exact this
    have h2 : 0 < ‖y‖ := norm_pos_iff.2 hy0
    nlinarith
  intro w
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hinj w
  exact ⟨R y, by simpa using hy⟩

end TauCeti

namespace LinearMap

variable {𝕜 D Y : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup D] [Module 𝕜 D]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- **Surjectivity is stable under relatively small perturbations.** If `Q : D →ₗ[𝕜] Y` is a
surjective linear map into a Banach space and `‖K z‖ ≤ θ * ‖Q z‖` for every `z`, with `θ < 1`, then
`Q + K` is surjective. -/
theorem surjective_add_of_norm_le (Q K : D →ₗ[𝕜] Y) (hQ : Surjective Q) {θ : ℝ} (hθ : θ < 1)
    (hK : ∀ z, ‖K z‖ ≤ θ * ‖Q z‖) : Surjective (Q + K) := by
  have hK' : ∀ z, ‖K z‖ ≤ max θ 0 * ‖Q z‖ := fun z ↦
    (hK z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hker : ker Q ≤ ker K := fun z hz ↦ by
    have := hK' z
    rw [mem_ker] at hz ⊢
    rwa [hz, norm_zero, mul_zero, norm_le_zero_iff] at this
  -- `K` factors through `Q` as `S ∘ Q`, with `S` of norm at most `θ`.
  let S : Y →ₗ[𝕜] Y := (ker Q).liftQ K hker ∘ₗ (Q.quotKerEquivOfSurjective hQ).symm.toLinearMap
  have hS : ∀ z, S (Q z) = K z := fun z ↦ by
    have : (Q.quotKerEquivOfSurjective hQ).symm (Q z) = Submodule.Quotient.mk z :=
      (LinearEquiv.symm_apply_eq _).2 (quotKerEquivOfSurjective_apply_mk Q hQ z).symm
    simp [S, this]
  have hSb : ∀ y, ‖S y‖ ≤ max θ 0 * ‖y‖ := fun y ↦ by
    obtain ⟨z, rfl⟩ := hQ y
    rw [hS]
    exact hK' z
  have hnorm : ‖-S.mkContinuous (max θ 0) hSb‖ < 1 := by
    rw [norm_neg]
    exact (S.mkContinuous_norm_le (le_max_right _ _) hSb).trans_lt (max_lt hθ one_pos)
  -- `Q + K = (1 + S) ∘ Q`, and `1 + S` is invertible.
  let u := Units.oneSub _ hnorm
  intro y
  obtain ⟨z, hz⟩ := hQ ((↑u⁻¹ : Y →L[𝕜] Y) y)
  refine ⟨z, ?_⟩
  have hu : (↑u : Y →L[𝕜] Y) ((↑u⁻¹ : Y →L[𝕜] Y) y) = y := by
    rw [← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]
  rw [← hu, ← hz, Units.val_oneSub]
  simp [hS]

end LinearMap

end
