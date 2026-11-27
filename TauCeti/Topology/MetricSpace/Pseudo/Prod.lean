/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Products of pseudometric spaces: neighborhoods and nested balls

In a product of pseudometric spaces, a property holds eventually for the product filter
`𝓝 x ×ˢ 𝓝[s] t` exactly when it holds on a box of points `(y, τ)` with `dist y x < δ`, `τ ∈ s`
and `dist τ t < δ` (`Metric.eventually_nhds_prod_nhdsWithin_iff`). This is the form of
`Metric.eventually_nhds_prod_iff` in which the second filter is also given by a distance bound,
as used for functions of a space variable and a time variable restricted to an interval.

A map of `X × F` preserving the first coordinate, injective on each product `V i ×ˢ ball c (r i)`
of a set with a ball about a common centre, is injective on their union, since over each point of
`X` these balls are nested (`TauCeti.injOn_biUnion_prod_ball`).

In `ℝ × ℝ` with the sup distance, every point is within `1 / 2` of the integer point obtained by
rounding its coordinates (`Prod.dist_round_le`), so the open unit balls about the integer points
cover the plane.

A neighbourhood of `(t, x)` in a product contains every point `(s, y)` with `dist s t < r` and
`y ∈ ball x r` for small `r > 0`, and `r` can be chosen so that a function continuous at `x` also
moves by less than a given `δ` on that ball (`TauCeti.exists_pos_forall_mem_of_mem_nhds`).
-/

public section

open Set Filter
open scoped Topology

namespace Metric

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A property holds eventually near `x` and near `t` within `s` if and only if it holds on a box
`dist y x < δ`, `τ ∈ s`, `dist τ t < δ`. -/
theorem eventually_nhds_prod_nhdsWithin_iff {P : X × Y → Prop} {x : X} {s : Set Y} {t : Y} :
    (∀ᶠ p in 𝓝 x ×ˢ 𝓝[s] t, P p) ↔
      ∃ δ > 0, ∀ y, dist y x < δ → ∀ τ ∈ s, dist τ t < δ → P (y, τ) := by
  rw [← nhdsWithin_univ, ← nhdsWithin_prod_eq, eventually_nhdsWithin_iff, eventually_nhds_iff]
  simp only [Prod.forall, Prod.dist_eq, max_lt_iff, mem_prod, mem_univ, true_and]
  exact exists_congr fun δ ↦ and_congr_right fun _ ↦ ⟨fun h y hy τ hτ hτt ↦ h y τ ⟨hy, hτt⟩ hτ,
    fun h y τ hyτ hτ ↦ h y hyτ.1 τ hτ hyτ.2⟩

end Metric

/-- Every point `y` of `ℝ × ℝ` is within `1 / 2` of the integer point `(round y.1, round y.2)`,
for the sup distance. -/
theorem Prod.dist_round_le (y : ℝ × ℝ) : dist y ((round y.1 : ℝ), (round y.2 : ℝ)) ≤ 1 / 2 := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le (abs_sub_round _) (abs_sub_round _)

namespace TauCeti

section Neighbourhood

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- **Small product balls in a neighbourhood.** If `N` is a neighbourhood of `(t, x)` in `X × Y`
and `g : Y → ℝ` is continuous at `x`, then for some `r > 0` every `(s, y)` with `dist s t < r` and
`y ∈ ball x r` lies in `N` and has `g y - g x ∈ (-δ, δ)`. -/
theorem exists_pos_forall_mem_of_mem_nhds {N : Set (X × Y)} {t : X} {x : Y} (hN : N ∈ 𝓝 (t, x))
    {g : Y → ℝ} (hg : ContinuousAt g x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ s y, dist s t < r → y ∈ Metric.ball x r → (s, y) ∈ N ∧ g y - g x ∈ Ioo (-δ) δ := by
  obtain ⟨r₁, hr₁, hr₁N⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨r₂, hr₂, hr₂g⟩ := Metric.eventually_nhds_iff.1 (Metric.tendsto_nhds.1 hg δ hδ)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun s y hs hy ↦ ⟨hr₁N ?_, ?_⟩⟩
  · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hs.trans_le (min_le_left _ _), (Metric.mem_ball.1 hy).trans_le (min_le_left _ _)⟩
  · have := hr₂g ((Metric.mem_ball.1 hy).trans_le (min_le_right _ _))
    rw [Real.dist_eq] at this
    exact mem_Ioo.2 (abs_lt.1 this)

end Neighbourhood

variable {ι X F F' : Type*} [PseudoMetricSpace F] {Φ : X × F → X × F'} {U : Set ι}
  {V : ι → Set X} {c : F} {r : ι → ℝ}

/-- A map of `X × F` preserving the first coordinate on the union of the products
`V i ×ˢ ball c (r i)`, `i ∈ U`, and injective on each of them, is injective on their union: over
each point of `X` the balls are nested, so two points with the same image lie in the product with
the larger ball. -/
theorem injOn_biUnion_prod_ball
    (hΦ : ∀ z ∈ ⋃ i ∈ U, V i ×ˢ Metric.ball c (r i), (Φ z).1 = z.1)
    (hinj : ∀ i ∈ U, InjOn Φ (V i ×ˢ Metric.ball c (r i))) :
    InjOn Φ (⋃ i ∈ U, V i ×ˢ Metric.ball c (r i)) := by
  intro z hz z' hz' h
  have h1 : z.1 = z'.1 := by rw [← hΦ z hz, ← hΦ z' hz', h]
  simp only [mem_iUnion, exists_prop] at hz hz'
  obtain ⟨i, hi, hzi⟩ := hz
  obtain ⟨i', hi', hzi'⟩ := hz'
  wlog hle : r i ≤ r i' generalizing z z' i i'
  · exact (this h.symm h1.symm i' hi' hzi' i hi hzi (le_of_not_ge hle)).symm
  exact hinj i' hi' ⟨h1 ▸ hzi'.1, Metric.ball_subset_ball hle hzi.2⟩ hzi' h

end TauCeti
