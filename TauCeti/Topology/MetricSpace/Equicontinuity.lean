/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Equicontinuity criteria in pseudometric spaces

When `g : X × Y → Z` is jointly continuous on a product with `Y` compact, the tube lemma around
each compact slice `{x₀} × Y` upgrades pointwise continuity of `g` to locally uniform control in
`y : Y`: every `δ > 0` holds uniformly across `Y` on a neighbourhood of `x₀`. Consequently, any
family `F : ι → X → W` into a pseudometric space whose distances are controlled linearly by uniform
`Y`-slice distance bounds of `g` (such as marginal integrals, suprema, infima, or log-partition
transforms of `g`) is equicontinuous on `X`.

In the other direction, a uniformly equicontinuous family of real functions has, for each
`ε > 0`, a common oscillation bound at small scales. Phrased with the scale `√s`, this turns an
error rate of the form `C (η + s L)`, where `η` is the oscillation over distances at most `√s`,
into convergence as `s → 0` that is uniform over the family.

## Main statements

* `Metric.equicontinuous_of_forall_dist_le`: a family `F : ι → X → W` controlled linearly by every
  uniform `Y`-slice distance bound of a jointly continuous map `g : X × Y → Z` with `Y` compact is
  equicontinuous.
* `TauCeti.exists_forall_mul_add_mul_lt_of_uniformEquicontinuous`: for a uniformly equicontinuous
  family of real functions and constants `C ≥ 0`, `L`, small times `s` admit an oscillation bound
  `η` over distances at most `√s` with `C (η + s L)` below any given `ε > 0`. This turns a
  rate of the form `C (η + s L)` into uniform convergence over the family.
-/

public section

open Filter Set Topology

namespace Metric

/-- **Tube-lemma equicontinuity criterion.** If `g : X × Y → Z` is jointly continuous into a
pseudometric space with `Y` compact, and a family `F : ι → X → W` into a pseudometric space has
distances controlled linearly by every uniform `Y`-slice distance bound of `g`, then `F` is
equicontinuous. -/
theorem equicontinuous_of_forall_dist_le {X Y Z W ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [PseudoMetricSpace Z] [PseudoMetricSpace W]
    {g : X × Y → Z} (hg : Continuous g) {F : ι → X → W} {L : ℝ}
    (hosc : ∀ x₁ x₂ δ, 0 ≤ δ → (∀ y, dist (g (x₁, y)) (g (x₂, y)) ≤ δ) →
      ∀ i, dist (F i x₁) (F i x₂) ≤ L * δ) :
    Equicontinuous F := by
  intro x₀
  rw [Metric.uniformity_basis_dist.equicontinuousAt_iff_right]
  intro r hr
  set M : ℝ := max L 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right L 1)
  set δ : ℝ := r / (2 * M)
  have hδ : 0 < δ := div_pos hr (mul_pos two_pos hM)
  have hn : IsOpen {z : X × Y | dist (g z) (g (x₀, z.2)) < δ} :=
    isOpen_lt (hg.dist (hg.comp (continuous_const.prodMk continuous_snd))) continuous_const
  obtain ⟨u, v, hu, -, hx₀u, huv_univ, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := x₀)) isCompact_univ hn
      (by rintro ⟨x, y⟩ ⟨rfl, _⟩; simpa using hδ)
  filter_upwards [hu.mem_nhds (hx₀u rfl)] with x hxu i
  rw [dist_comm]
  calc dist (F i x) (F i x₀)
      ≤ L * δ := hosc x x₀ δ hδ.le (fun y ↦ (huv ⟨hxu, huv_univ (mem_univ y)⟩).le) i
    _ ≤ M * δ := mul_le_mul_of_nonneg_right (le_max_left L 1) hδ.le
    _ = r / 2 := by simp only [δ]; field_simp [hM.ne']
    _ < r := half_lt_self hr

end Metric

namespace TauCeti

/-- `X ε / (2 (X + 1)) < ε / 2` for `X ≥ 0` and `ε > 0`. -/
private theorem mul_div_two_mul_add_one_lt {ε : ℝ} (hε : 0 < ε) (X : ℝ) (hX : 0 ≤ X) :
    X * (ε / (2 * (X + 1))) < ε / 2 := by
  have hX1 : X / (X + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  calc X * (ε / (2 * (X + 1))) = ε / 2 * (X / (X + 1)) := by field_simp
    _ < ε / 2 * 1 := mul_lt_mul_of_pos_left hX1 (by positivity)
    _ = ε / 2 := mul_one _

/-- **From the rate to uniform attainment.** Let `(g_k)` be a uniformly equicontinuous family of
real functions, and let `C ≥ 0` and `L` be constants. For every `ε > 0` there is `δ > 0` such that
each time `0 ≤ s < δ` admits an `η` by which every `g_k` moves by at most `η` over distances at
most `√s`, with `C (η + s L) < ε`. Combined with a rate `|u_k(x, s) - g_k(x)| ≤ C (η + s L)`, such
as the parabolic initial-trace rate
`TauCeti.ParabolicC2HolderSpace.exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le`, this
gives `u_k(·, s) → g_k` uniformly in `k` as `s → 0`. -/
theorem exists_forall_mul_add_mul_lt_of_uniformEquicontinuous {κ X : Type*} [PseudoMetricSpace X]
    {C : ℝ} (hC : 0 ≤ C) (L : ℝ) {g : κ → X → ℝ} (hg : UniformEquicontinuous g) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ → ∃ η, (∀ k x y, dist x y ≤ √s → |g k x - g k y| ≤ η) ∧
      C * (η + s * L) < ε := by
  -- Take `η` with `C η < ε / 2`, the scale `δ₁` of the oscillation `η`, and `C s |L| < ε / 2`.
  set R := C * |L|
  obtain ⟨δ₁, hδ₁, hδ₁η⟩ :=
    Metric.uniformEquicontinuous_iff.1 hg (ε / (2 * (C + 1))) (by positivity)
  refine ⟨min (δ₁ ^ 2) (ε / (2 * (R + 1))), by positivity, fun s hs0 hs ↦
    ⟨ε / (2 * (C + 1)), fun k x y hxy ↦ ?_, ?_⟩⟩
  · have hsδ : √s < δ₁ := by
      rw [← Real.sqrt_sq hδ₁.le]
      exact Real.sqrt_lt_sqrt hs0 (hs.trans_le (min_le_left _ _))
    simpa [Real.dist_eq] using (hδ₁η x y (hxy.trans_lt hsδ) k).le
  · have hR : C * (s * L) ≤ R * (ε / (2 * (R + 1))) :=
      calc _ ≤ C * (s * |L|) := by gcongr; exact le_abs_self _
        _ = R * s := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hs.le.trans (min_le_right _ _)) (by positivity)
    -- Each of the two terms is less than `ε / 2`.
    have h₁ := mul_div_two_mul_add_one_lt hε C hC
    have h₂ := mul_div_two_mul_add_one_lt hε R (by positivity)
    calc _ = C * (ε / (2 * (C + 1))) + C * (s * L) := by ring
      _ < ε := by linarith

end TauCeti
