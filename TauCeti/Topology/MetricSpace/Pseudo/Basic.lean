/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform convergence, uniform Cauchy and separation criteria from distance bounds

A family of functions into a pseudometric space whose distance to a limit function on `s` is
eventually bounded by a quantity tending to `0` converges uniformly on `s`
(`TauCeti.tendstoUniformlyOn_of_dist_le`). Likewise, an eventually vanishing uniform bound on the
pairwise distances `dist (F p.1 x) (F p.2 x)` along `l ×ˢ l` implies `UniformCauchySeqOn F l s`
(`TauCeti.uniformCauchySeqOn_of_dist_le`), and uniform convergence transfers between two families
whose uniform distance on `s` is eventually bounded by a quantity tending to `0`
(`TendstoUniformlyOn.congr_dist_le`).

A family of maps into a pseudometric space separates points through some entourage exactly when
it separates them through some positive distance
(`TauCeti.exists_separating_entourage_iff_exists_pos_dist`).
-/

public section

namespace TauCeti

open Filter Topology
open scoped Uniformity

variable {ι α β : Type*} [PseudoMetricSpace β] {l : Filter ι} {F : ι → α → β} {f : α → β}
  {s : Set α} {u : ι → ℝ}

/-- If, eventually along `l`, the distance from `F i` to `f` on `s` is at most `u i`, and `u`
tends to `0` along `l`, then `F` converges to `f` uniformly on `s`. -/
theorem tendstoUniformlyOn_of_dist_le (hu : Tendsto u l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ x ∈ s, dist (F i x) (f x) ≤ u i) : TendstoUniformlyOn F f l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h, Metric.tendsto_nhds.1 hu ε hε] with i hi hiε x hx
  rw [Real.dist_eq, sub_zero] at hiε
  rw [dist_comm]
  exact (hi x hx).trans_lt ((le_abs_self _).trans_lt hiε)

/-- If, eventually along `l ×ˢ l`, the distance between `F p.1` and `F p.2` on `s` is at most
`u p`, and `u` tends to `0` along `l ×ˢ l`, then `F` is uniformly Cauchy on `s`. -/
theorem uniformCauchySeqOn_of_dist_le {u : ι × ι → ℝ} (hu : Tendsto u (l ×ˢ l) (𝓝 0))
    (h : ∀ᶠ p in l ×ˢ l, ∀ x ∈ s, dist (F p.1 x) (F p.2 x) ≤ u p) :
    UniformCauchySeqOn F l s := by
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
  filter_upwards [h, Metric.tendsto_nhds.1 hu ε hε] with p hp hpu x hx
  rw [Real.dist_eq, sub_zero] at hpu
  exact hεV ((hp x hx).trans_lt ((le_abs_self _).trans_lt hpu))

/-- If `F` converges uniformly to `f` on `s`, and eventually along `l` the distance between `F i`
and `G i` on `s` is at most `u i` with `u → 0`, then `G` also converges uniformly to `f` on `s`. -/
theorem _root_.TendstoUniformlyOn.congr_dist_le {G : ι → α → β}
    (hF : TendstoUniformlyOn F f l s) (hu : Tendsto u l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ x ∈ s, dist (F i x) (G i x) ≤ u i) :
    TendstoUniformlyOn G f l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hF (ε / 2) (half_pos hε), h,
    Metric.tendsto_nhds.1 hu (ε / 2) (half_pos hε)] with i hiF hiFG hiu x hx
  rw [Real.dist_eq, sub_zero] at hiu
  calc dist (f x) (G i x)
      ≤ dist (f x) (F i x) + dist (F i x) (G i x) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hiF x hx) ((hiFG x hx).trans_lt ((le_abs_self _).trans_lt hiu))
    _ = ε := add_halves ε

/-- A family `g` of maps from a type `α` into a pseudometric space `β` separates points through
some entourage exactly when it separates them through some distance `δ > 0`: two points are equal
as soon as all their images are `U`-close, if and only if distinct points have images more than `δ`
apart. -/
theorem exists_separating_entourage_iff_exists_pos_dist (g : ι → α → β) :
    (∃ U ∈ 𝓤 β, ∀ x y : α, (∀ i, (g i x, g i y) ∈ U) → x = y) ↔
      ∃ δ > 0, ∀ x y : α, x ≠ y → ∃ i, δ < dist (g i x) (g i y) := by
  constructor
  · rintro ⟨U, hU, hsep⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
    refine ⟨ε / 2, half_pos hε, fun x y hxy ↦ ?_⟩
    by_contra! h
    exact hxy (hsep x y fun i ↦ hεU ((h i).trans_lt (half_lt_self hε)))
  · rintro ⟨δ, hδ, hsep⟩
    refine ⟨{p | dist p.1 p.2 ≤ δ}, Metric.mem_uniformity_dist.2 ⟨δ, hδ, fun _ _ h ↦ h.le⟩,
      fun x y h ↦ ?_⟩
    by_contra hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact (h i).not_gt hi

end TauCeti
