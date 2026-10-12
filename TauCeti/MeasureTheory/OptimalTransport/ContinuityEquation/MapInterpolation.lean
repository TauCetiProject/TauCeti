/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# The continuity equation along the linear interpolation of a map

Let `μ` be a finite measure on a finite-dimensional real normed space `E` and `T : E → E` a
measurable map, for instance a transport map from `μ` to its image law `T₊ μ`. Moving each point
`x` at constant speed along the segment from `x` to `T x` gives the curve of laws

`μₜ = (Fₜ)₊ μ`, where `Fₜ x = (1 - t) • x + t • T x`,

from `μ₀ = μ` to `μ₁ = T₊ μ`. When `μ` and `T₊ μ` are probability laws of finite `p`-th moment and
the graph plan of `T` is an optimal coupling for `W_p`, these laws trace a geodesic segment of
`P_p (E)` (`TauCeti.WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul`). This file
describes the curve in Eulerian terms.

If the displacement `T x - x` has finite first moment, then `μₜ` solves the continuity equation on
`(0, 1)` with the *barycentric velocity* `vₜ y = E_μ [T X - X | Fₜ X = y]`, the average
displacement of the particles found at `y` at time `t`. Precisely, `v` evaluated at `(t, Fₜ x)` is
the conditional expectation of `T x - x` given `(t, Fₜ x)`, for the measure `dt ⊗ μ` on
`(0, 1) × E`. Its `p`-action is at most the `p`-th moment of the displacement,
`∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt ≤ ∫ ‖T x - x‖ ^ p dμ` for every `p ≥ 1`.

If moreover no two particles meet at the same time and place once a `dt ⊗ μ`-null set of times and
particles is discarded (for instance if almost every `Fₜ` is injective on a measurable set carrying
`μ`), then no averaging takes place:
`vₜ (Fₜ x) = T x - x` for almost every `t ∈ (0, 1)` and `μ`-almost every `x`, and the `p`-action of
`v` equals the `p`-th moment of the displacement for every exponent `p`.

These curves are the map-induced competitors in the Benamou–Brenier formula: when the graph plan of
`T` is optimal for the cost `‖x - y‖ ^ p`, the `p`-th moment of the displacement is
`W_p (μ, T₊ μ) ^ p`, so the action of the barycentric velocity is at most `W_p (μ, T₊ μ) ^ p`.

## Main results

* `TauCeti.exists_isContinuityEquation_map_smul_add_smul`: the linear interpolation of a map with
  displacement of finite first moment solves the continuity equation with its barycentric velocity,
  whose `p`-action is at most the `p`-th moment of the displacement.
* `TauCeti.exists_isContinuityEquation_map_smul_add_smul_of_injOn`: when for every `t` the
  interpolating map `Fₜ` is injective on the fibre at `t` of a measurable set of full `dt ⊗ μ`
  measure, the velocity field is the displacement read along the interpolation, and its `p`-action
  equals the `p`-th moment of the displacement.
* `TauCeti.exists_isContinuityEquation_map_smul_add_smul_of_ae_injOn`: the special case in which
  almost every interpolating map is injective on one measurable set carrying `μ`.

## References

* J.-D. Benamou and Y. Brenier, *A computational fluid mechanics solution to the
  Monge–Kantorovich mass transfer problem*, Numer. Math. 84 (2000), 375--393.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1 and §8.3.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {T : E → E}

/-- **The continuity equation along the linear interpolation of a map.** Let `μ` be a finite
measure on `E` and `T` a measurable map whose displacement `T x - x` has finite first moment. Then
the laws `μₜ` of `(1 - t) • x + t • T x` under `μ` solve the continuity equation on `(0, 1)` with
the barycentric velocity `v`: its value at `(t, (1 - t) • x + t • T x)` is the conditional
expectation of the displacement `T x - x` given the time `t` and the position
`(1 - t) • x + t • T x`, for the measure `dt ⊗ μ` on `(0, 1) × E`. For every `p ≥ 1` its `p`-action
is at most the `p`-th moment of the displacement:
`∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt ≤ ∫ ‖T x - x‖ ^ p dμ`. -/
theorem exists_isContinuityEquation_map_smul_add_smul (μ : Measure E) [IsFiniteMeasure μ]
    (hT : Measurable T) (hint : ∫⁻ x, ‖T x - x‖ₑ ∂μ < ∞) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ μ.map fun x ↦ (1 - t) • x + t • T x) v 0 1 ∧
      (fun q : ℝ × E ↦ v q.1 ((1 - q.1) • q.2 + q.1 • T q.2)) =
        ((volume.restrict (Ioo 0 1)).prod μ)[fun q ↦ T q.2 - q.2 |
          MeasurableSpace.comap (fun q : ℝ × E ↦ (q.1, (1 - q.1) • q.2 + q.1 • T q.2))
            inferInstance] ∧
      ∀ p : ℝ, 1 ≤ p →
        ∫⁻ t in Ioo 0 1, ∫⁻ y, ‖v t y‖ₑ ^ p ∂μ.map (fun x ↦ (1 - t) • x + t • T x) ≤
          ∫⁻ x, ‖T x - x‖ₑ ^ p ∂μ := by
  obtain ⟨v, hce, hv, hact⟩ := exists_isContinuityEquation_map μ
    (γ := fun x t ↦ (1 - t) • x + t • T x) (V := fun x _ ↦ T x - x) (a := 0) (b := 1)
    (by fun_prop) (by fun_prop)
    (.of_forall fun x ↦ (by fun_prop : ContDiff ℝ 1 fun t : ℝ ↦ (1 - t) • x + t • T x).contDiffOn
      |>.absolutelyContinuousOnInterval)
    (.of_forall fun x ↦ .of_forall fun t _ ↦
      ((((hasDerivAt_id' t).const_sub 1).smul_const x).add
        ((hasDerivAt_id' t).smul_const (T x))).congr_deriv (by simp [neg_add_eq_sub]))
    (by simpa using hint)
  exact ⟨v, hce, hv, fun p hp ↦ (hact p hp).trans_eq (by simp)⟩

/-- **The velocity along an injective linear interpolation.** Let `μ` be a finite measure on `E` and
`T` a measurable map whose displacement `T x - x` has finite first moment, and let `A` be a
measurable set of times and particles carrying `dt ⊗ μ` on `(0, 1) × E` such that for every `t`
the map `x ↦ (1 - t) • x + t • T x` is injective on the particles `x` with `(t, x) ∈ A`. Then the
laws `μₜ` of `(1 - t) • x + t • T x` under `μ` solve the continuity equation on `(0, 1)` with a
velocity field `v` equal to the displacement along the interpolation:
`vₜ ((1 - t) • x + t • T x) = T x - x` for almost every `t ∈ (0, 1)` and `μ`-almost every `x`.
Consequently, for every exponent `p` the `p`-action of `v` is the `p`-th moment of the
displacement: `∫₀¹ ∫ ‖vₜ‖ ^ p dμₜ dt = ∫ ‖T x - x‖ ^ p dμ`. -/
theorem exists_isContinuityEquation_map_smul_add_smul_of_injOn (μ : Measure E) [IsFiniteMeasure μ]
    (hT : Measurable T) (hint : ∫⁻ x, ‖T x - x‖ₑ ∂μ < ∞) {A : Set (ℝ × E)} (hA : MeasurableSet A)
    (hAμ : ∀ᵐ q ∂(volume.restrict (Ioo 0 1)).prod μ, q ∈ A)
    (hinj : ∀ t, InjOn (fun x ↦ (1 - t) • x + t • T x) {x | (t, x) ∈ A}) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ μ.map fun x ↦ (1 - t) • x + t • T x) v 0 1 ∧
      (∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ x ∂μ, v t ((1 - t) • x + t • T x) = T x - x) ∧
      ∀ p : ℝ, ∫⁻ t in Ioo 0 1, ∫⁻ y, ‖v t y‖ₑ ^ p ∂μ.map (fun x ↦ (1 - t) • x + t • T x) =
        ∫⁻ x, ‖T x - x‖ₑ ^ p ∂μ := by
  obtain ⟨v, hce, hv, -⟩ := exists_isContinuityEquation_map_smul_add_smul μ hT hint
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  -- the time and position map `G` is injective on `A`, so conditioning on it is trivial
  set G : ℝ × E → ℝ × E := fun q ↦ (q.1, (1 - q.1) • q.2 + q.1 • T q.2)
  have hG : Measurable G := by fun_prop
  have hGinj : InjOn G A := by
    rintro ⟨t, x⟩ hx ⟨t', x'⟩ hx' he
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    exact Prod.ext rfl (hinj t hx hx' he)
  have hW : Integrable (fun x ↦ T x - x) μ :=
    ⟨(hT.sub measurable_id).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 hint⟩
  have hae : ∀ᵐ q ∂(volume.restrict (Ioo 0 1)).prod μ,
      v q.1 ((1 - q.1) • q.2 + q.1 • T q.2) = T q.2 - q.2 := by
    filter_upwards [MeasureTheory.condExp_comap_ae_eq_of_injOn hG hA hAμ hGinj
      (hW.comp_snd (volume.restrict (Ioo 0 1)))] with q hq
    rw [← hq]
    exact congrFun hv q
  have hae' : ∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ x ∂μ, v t ((1 - t) • x + t • T x) = T x - x := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact Measure.ae_ae_of_ae_prod hae
  refine ⟨v, hce, hae', fun p ↦ ?_⟩
  have hvm (t : ℝ) : Measurable (v t) := hce.measurable_velocity.comp measurable_prodMk_left
  calc ∫⁻ t in Ioo 0 1, ∫⁻ y, ‖v t y‖ₑ ^ p ∂μ.map (fun x ↦ (1 - t) • x + t • T x)
      = ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ x, ‖T x - x‖ₑ ^ p ∂μ := by
        refine setLIntegral_congr_fun_ae measurableSet_Ioo ?_
        filter_upwards [hae'] with t ht hmem
        rw [lintegral_map ((hvm t).enorm.pow_const p) (by fun_prop)]
        exact lintegral_congr_ae ((ht hmem).mono fun x hx ↦ by simp [hx])
    _ = ∫⁻ x, ‖T x - x‖ₑ ^ p ∂μ := by simp

/-- **The velocity along a linear interpolation injective on a fixed set.** The special case of
`exists_isContinuityEquation_map_smul_add_smul_of_injOn` in which, for almost every
`t ∈ (0, 1)`, the map `x ↦ (1 - t) • x + t • T x` is injective on one measurable set `S` carrying
`μ`: then `vₜ ((1 - t) • x + t • T x) = T x - x` for almost every `t ∈ (0, 1)` and `μ`-almost every
`x`, and for every exponent `p` the `p`-action of `v` is the `p`-th moment of the displacement. -/
theorem exists_isContinuityEquation_map_smul_add_smul_of_ae_injOn (μ : Measure E)
    [IsFiniteMeasure μ] (hT : Measurable T) (hint : ∫⁻ x, ‖T x - x‖ₑ ∂μ < ∞) {S : Set E}
    (hS : MeasurableSet S) (hSμ : ∀ᵐ x ∂μ, x ∈ S)
    (hinj : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → InjOn (fun x ↦ (1 - t) • x + t • T x) S) :
    ∃ v : ℝ → E → E,
      IsContinuityEquation (fun t ↦ μ.map fun x ↦ (1 - t) • x + t • T x) v 0 1 ∧
      (∀ᵐ t, t ∈ Ioo 0 1 → ∀ᵐ x ∂μ, v t ((1 - t) • x + t • T x) = T x - x) ∧
      ∀ p : ℝ, ∫⁻ t in Ioo 0 1, ∫⁻ y, ‖v t y‖ₑ ^ p ∂μ.map (fun x ↦ (1 - t) • x + t • T x) =
        ∫⁻ x, ‖T x - x‖ₑ ^ p ∂μ := by
  -- `U` is a measurable set of full measure in `(0, 1)` of times at which the interpolation is
  -- injective on `S`
  set N := toMeasurable volume {t | ¬(t ∈ Ioo (0 : ℝ) 1 → InjOn (fun x ↦ (1 - t) • x + t • T x) S)}
  set U := Ioo (0 : ℝ) 1 \ N
  have hU : MeasurableSet U := measurableSet_Ioo.diff (measurableSet_toMeasurable _ _)
  have hUμ : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), t ∈ U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1
        ((measure_toMeasurable _).trans (ae_iff.1 hinj)))] with t ht htN using ⟨ht, htN⟩
  have hUinj (t : ℝ) (ht : t ∈ U) : InjOn (fun x ↦ (1 - t) • x + t • T x) S := by
    by_contra h
    exact ht.2 (subset_toMeasurable _ _ fun h' ↦ h (h' ht.1))
  exact exists_isContinuityEquation_map_smul_add_smul_of_injOn μ hT hint (hU.prod hS)
    ((Measure.ae_prod_mem_iff_ae_ae_mem (hU.prod hS)).2
      (hUμ.mono fun _ ht ↦ hSμ.mono fun _ hx ↦ ⟨ht, hx⟩))
    fun t _ hx _ hx' ↦ hUinj t hx.1 hx.2 hx'.2

end TauCeti
