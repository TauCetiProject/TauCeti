/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Equicontinuity from slice distance bounds on a compact factor

When `g : X × Y → Z` is jointly continuous on a product with `Y` compact, the tube lemma around
each compact slice `{x₀} × Y` upgrades pointwise continuity of `g` to locally uniform control in
`y : Y`: every `δ > 0` holds uniformly across `Y` on a neighbourhood of `x₀`. Consequently, any
family `F : ι → X → W` into a pseudometric space whose distances are controlled linearly by uniform
`Y`-slice distance bounds of `g` (such as marginal integrals, suprema, infima, or log-partition
transforms of `g`) is equicontinuous on `X`.

## Main statements

* `Metric.equicontinuous_of_forall_dist_le`: a family `F : ι → X → W` controlled linearly by every
  uniform `Y`-slice distance bound of a jointly continuous map `g : X × Y → Z` with `Y` compact is
  equicontinuous.
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
  set n : Set (X × Y) := {z | dist (g z) (g (x₀, z.2)) < δ}
  have hn : IsOpen n :=
    isOpen_lt (hg.dist (hg.comp (continuous_const.prodMk continuous_snd))) continuous_const
  have hsub : ({x₀} : Set X) ×ˢ (univ : Set Y) ⊆ n := by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain rfl := mem_singleton_iff.1 hx
    simp [n, hδ]
  obtain ⟨u, v, hu, -, hx₀u, huv_univ, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hn hsub
  filter_upwards [hu.mem_nhds (hx₀u rfl)] with x hxu i
  have hxy : ∀ y, dist (g (x, y)) (g (x₀, y)) ≤ δ := fun y ↦
    (huv ⟨hxu, huv_univ (mem_univ y)⟩).le
  rw [dist_comm]
  calc dist (F i x) (F i x₀) ≤ L * δ := hosc x x₀ δ hδ.le hxy i
    _ ≤ M * δ := mul_le_mul_of_nonneg_right (le_max_left L 1) hδ.le
    _ = r / 2 := by
        have hM' : M ≠ 0 := hM.ne'
        simp only [δ]
        field_simp
    _ < r := half_lt_self hr

end Metric
