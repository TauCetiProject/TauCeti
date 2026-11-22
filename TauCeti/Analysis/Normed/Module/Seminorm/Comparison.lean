/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Comparison of seminorms with a norm under composition

Two facts about real-valued functions compared with the norm of a normed space, used to transport
such comparisons through changes of coordinates.

## Main results

* `TauCeti.exists_bounds_comp_continuousLinearEquiv`: a function bounded above and below by
  positive multiples of the norm of `F` stays so bounded after precomposition with a continuous
  linear equivalence `G ≃L[𝕜] F`.
* `TauCeti.eventually_abs_sub_le_comp_continuousLinearMap`: if seminorms `N x` on `F` are
  uniformly close to `N x₀` on the unit ball for `x` near `x₀`, and `T : X → G →L[𝕜] F` is
  continuous at `x₀`, then the seminorms `v ↦ N x (T x v)` are uniformly close to
  `v ↦ N x₀ (T x₀ v)` on the unit ball of `G` for `x` near `x₀`.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A function bounded above and below by positive multiples of the norm stays so bounded after
precomposition with a continuous linear equivalence. -/
theorem exists_bounds_comp_continuousLinearEquiv {N : F → ℝ} {c C : ℝ} (hc : 0 < c)
    (hN : ∀ w, c * ‖w‖ ≤ N w ∧ N w ≤ C * ‖w‖) (T : G ≃L[𝕜] F) :
    ∃ c' > 0, ∃ C', ∀ v, c' * ‖v‖ ≤ N (T v) ∧ N (T v) ≤ C' * ‖v‖ := by
  refine ⟨c * (‖(T.symm : F →L[𝕜] G)‖ + 1)⁻¹, by positivity, max C 0 * ‖(T : G →L[𝕜] F)‖,
    fun v ↦ ⟨?_, ?_⟩⟩
  · have hv : ‖v‖ ≤ ‖(T.symm : F →L[𝕜] G)‖ * ‖T v‖ := by
      simpa using (T.symm : F →L[𝕜] G).le_opNorm (T v)
    have h1 : ‖v‖ ≤ (‖(T.symm : F →L[𝕜] G)‖ + 1) * ‖T v‖ := by nlinarith [norm_nonneg (T v)]
    calc c * (‖(T.symm : F →L[𝕜] G)‖ + 1)⁻¹ * ‖v‖
        ≤ c * (‖(T.symm : F →L[𝕜] G)‖ + 1)⁻¹ * ((‖(T.symm : F →L[𝕜] G)‖ + 1) * ‖T v‖) := by
          gcongr
      _ = c * ‖T v‖ := by field_simp
      _ ≤ N (T v) := (hN (T v)).1
  · calc N (T v) ≤ C * ‖T v‖ := (hN (T v)).2
      _ ≤ max C 0 * ‖T v‖ := by gcongr; exact le_max_left C 0
      _ ≤ max C 0 * (‖(T : G →L[𝕜] F)‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left ((T : G →L[𝕜] F).le_opNorm v) (le_max_right C 0)
      _ = max C 0 * ‖(T : G →L[𝕜] F)‖ * ‖v‖ := by ring

/-- Uniform closeness of seminorms on the unit ball survives precomposition with a family of
continuous linear maps that is continuous at the base point: if `N x` is within `δ * ‖w‖` of
`N x₀` for `x` near `x₀`, for every `δ > 0`, and `T` is continuous at `x₀`, then for every `ε > 0`
and `x` near `x₀`, `v ↦ N x (T x v)` is within `ε * ‖v‖` of `v ↦ N x₀ (T x₀ v)`. -/
theorem eventually_abs_sub_le_comp_continuousLinearMap {X : Type*} [TopologicalSpace X]
    {N : X → Seminorm 𝕜 F} {x₀ : X} {C : ℝ} (hC : ∀ w, N x₀ w ≤ C * ‖w‖)
    (hN : ∀ δ > 0, ∀ᶠ x in 𝓝 x₀, ∀ w, |N x w - N x₀ w| ≤ δ * ‖w‖)
    {T : X → G →L[𝕜] F} (hT : ContinuousAt T x₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, |N x (T x v) - N x₀ (T x₀ v)| ≤ ε * ‖v‖ := by
  set K := ‖T x₀‖ + 1
  set C' := max C 0 + 1
  have hK : 0 < K := by positivity
  have hC' : 0 < C' := by positivity
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖T x - T x₀‖ < min 1 (ε / (2 * C')) :=
    ((Metric.continuousAt_iff'.1 hT) (min 1 (ε / (2 * C'))) (by positivity)).mono fun x hx ↦ by
      rwa [← dist_eq_norm]
  filter_upwards [hnear, hN (ε / (2 * K)) (by positivity)] with x hx hNx v
  have hx1 : ‖T x - T x₀‖ ≤ 1 := hx.le.trans (min_le_left _ _)
  have hx2 : ‖T x - T x₀‖ ≤ ε / (2 * C') := hx.le.trans (min_le_right _ _)
  have hTx : ‖T x‖ ≤ K := by
    have := norm_le_insert' (T x) (T x₀)
    simp only [K]
    linarith
  have hCw : ∀ w, N x₀ w ≤ C' * ‖w‖ := fun w ↦ (hC w).trans (by
    gcongr; exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  calc |N x (T x v) - N x₀ (T x₀ v)|
      ≤ |N x (T x v) - N x₀ (T x v)| + |N x₀ (T x v) - N x₀ (T x₀ v)| := abs_sub_le _ _ _
    _ ≤ ε / (2 * K) * ‖T x v‖ + N x₀ (T x v - T x₀ v) :=
        add_le_add (hNx _) (abs_sub_map_le_sub _ _ _)
    _ ≤ ε / (2 * K) * (K * ‖v‖) + C' * (ε / (2 * C') * ‖v‖) := by
        gcongr
        · exact ((T x).le_opNorm v).trans (by gcongr)
        · refine (hCw _).trans ?_
          gcongr
          rw [← sub_apply]
          exact ((T x - T x₀).le_opNorm v).trans (by gcongr)
    _ = ε * ‖v‖ := by field_simp; ring

end TauCeti
