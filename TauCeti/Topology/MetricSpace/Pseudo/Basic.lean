/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Uniform convergence, uniform Cauchy and separation criteria from distance bounds

A family of functions into a pseudometric space whose distance to a limit function on `s` is
eventually bounded by a quantity tending to `0` converges uniformly on `s`
(`TauCeti.tendstoUniformlyOn_of_dist_le`). Likewise, an eventually vanishing uniform bound on the
pairwise distances `dist (F p.1 x) (F p.2 x)` along `l ×ˢ l` implies `UniformCauchySeqOn F l s`
(`TauCeti.uniformCauchySeqOn_of_dist_le`), and uniform convergence transfers between two families
whose uniform distance on `s` is eventually bounded by a quantity tending to `0`
(`TendstoUniformlyOn.congr_dist_le`).

For families with varying index types, multiplication by a convergent factor preserves uniform
convergence to a constant (`Filter.Tendsto.eventually_dist_mul_le`).

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

/-- Suppose `a` converges along `l`. If, eventually along `l ×ˢ l`, the bound
`dist (F p.1 x) (F p.2 x) ≤ C * dist (a p.1) (a p.2)` holds simultaneously for every
`x ∈ s` with a fixed constant `C`, then `F` is uniformly Cauchy on `s`. -/
theorem uniformCauchySeqOn_of_dist_le_mul_dist {γ : Type*} [PseudoMetricSpace γ]
    {a : ι → γ} {z : γ} (ha : Tendsto a l (𝓝 z)) (C : ℝ)
    (h : ∀ᶠ p in l ×ˢ l, ∀ x ∈ s,
      dist (F p.1 x) (F p.2 x) ≤ C * dist (a p.1) (a p.2)) :
    UniformCauchySeqOn F l s := by
  apply uniformCauchySeqOn_of_dist_le (u := fun p => C * dist (a p.1) (a p.2)) ?_ h
  simpa only [Function.comp_apply, dist_self, mul_zero] using tendsto_const_nhds.mul
    ((ha.comp tendsto_fst).dist (ha.comp tendsto_snd))

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

/-- Multiplication by a convergent factor preserves uniform convergence to a constant
on a family of varying index types. -/
theorem _root_.Filter.Tendsto.eventually_dist_mul_le {ι β : Type*} [PseudoMetricSpace β]
    [Mul β] [ContinuousMul β] {α : ι → Type*} {l : Filter ι} {f : ι → β}
    {g : (i : ι) → α i → β} {r s : β} (hf : Tendsto f l (𝓝 r))
    (hg : ∀ ε > 0, ∀ᶠ i in l, ∀ a, dist (g i a) s ≤ ε) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ a, dist (f i * g i a) (r * s) ≤ ε := by
  have ht : Tendsto (fun a : Σ i, α i ↦ g a.1 a.2) (comap Sigma.fst l) (𝓝 s) := by
    refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε hε ↦ ?_
    rw [eventually_comap]
    filter_upwards [hg ε hε] with i hi ⟨j, a⟩ hji
    obtain rfl : j = i := hji
    exact hi a
  intro ε hε
  have h := Metric.nhds_basis_closedBall.tendsto_right_iff.1
    ((hf.comp tendsto_comap).mul ht) ε hε
  rw [eventually_comap] at h
  exact h.mono fun i hi a ↦ hi ⟨i, a⟩ rfl

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
