/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Frame
import TauCeti.Geometry.Manifold.Morse.Bott.LinearOrbit

/-!
# Orbits near a broken trajectory cross the Morse chart linearly

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold, linear in a
Morse chart `φ` at a critical point `x`: in the coordinates of `φ`, where
`f = f x + (1/2) Σᵢ wᵢ zᵢ²` with weights `wᵢ = ±1`, the flow of `X` is the linear flow
`Λ_t z = (e^{-wᵢ t} zᵢ)ᵢ` for as long as this linear orbit stays in the chart.

Consider a broken trajectory through `x`: a point `y₀` of the stable manifold `W^s(x)`, with a time
`a` of linear forward flow in `φ`, and a point `z₀` of the unstable manifold `W^u(x)`, with a time
`b` of linear backward flow. Let `yₙ → y₀` be points whose orbits pass near `z₀`:
`Φ_{Tₙ} yₙ → z₀`. This file shows that for all large `n` the orbit of `yₙ` crosses the chart along
its linear flow between the times `a` and `Tₙ - b`: the linear orbit of the coordinates of
`Φ_a yₙ` stays in the chart for the times between `0` and `Tₙ - a - b`
(`TauCeti.IsAdaptedPseudoGradient.eventually_forall_linearFlow_mem_target_of_broken`). This is
the hypothesis `hcross` of the λ-lemma on unstable frames near a broken trajectory
(`TauCeti.IsAdaptedPseudoGradient.tendsto_mvfderiv_comp_unstableFrame_flow`), so the convergence
of comparison maps near a broken trajectory
(`TauCeti.IsAdaptedPseudoGradient.tendsto_trajectoryComparison_of_broken`) holds for every
sequence of orbits converging to a broken trajectory.

## Proof

The linear orbit of the coordinates `w₀` of `Φ_a y₀` stays in the chart and has no coordinates of
negative weight. The model statement
(`TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_mem_or_exists_le_neg`, in
`TauCeti.Geometry.Manifold.Morse.Bott.LinearOrbit`) says that for every `w`
near `w₀`, either the whole forward linear orbit of `w` stays in the chart, or it stays in the chart
up to a time `e` at which the quadratic form `(1/2) Σᵢ wᵢ zᵢ²` is at most `-c`, for a constant
`c > 0` independent of `w`. Indeed, up to a fixed time the orbit of `w` follows that of `w₀`;
then it lies in a small cube about the origin, in which the coordinates of positive weight keep
shrinking, until the coordinates of negative weight have grown to the size of the cube, which
makes the quadratic form negative.

Running the flow backwards, the same holds for the backward linear orbit of the coordinates of
`Φ_{Tₙ - b} yₙ`, near those of `Φ_{-b} z₀`, with a quadratic form at least `c`. As long as a
linear orbit stays in the chart it is the actual orbit
(`TauCeti.IsAdaptedPseudoGradient.coord_toChart_flow_add`), so `f` is below `f x - c` at the time
`a + e` and above `f x + c` at the time `Tₙ - b - e'`. Since `f` does not increase along the
flow, the second time is the earlier one: the forward and the backward linear pieces of the orbit
overlap, and together they cover the whole crossing.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.eventually_forall_linearFlow_mem_target_of_broken`: orbits near
  a broken trajectory cross the Morse chart at the break along its linear flow.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (trajectories near a broken trajectory, for a pseudo-gradient that is linear near the
  critical points).
* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the passage near a hyperbolic critical point).
-/

public section

open Filter Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {hX : IsAdaptedPseudoGradient f X}
  {φ : MorseChart E f x}
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- **Joining the two linear pieces of an orbit.** Let the orbit of `y` be in the chart at the
times `a` and `τ`, with coordinates `w` and `ζ`. Suppose that the forward linear orbit of `w`
stays in the chart, or does so up to a time `e` at which the quadratic form is at most `-c₁`, and
that the backward linear orbit of `ζ` stays in the chart, or does so back to a time `-e'` at which
the quadratic form is at least `c₂`, with `c₁ + c₂ > 0`. Then the linear orbit of `w` stays in the
chart for the times between `0` and `τ - a`. Indeed `f` does not increase along the orbit, so the
time `τ - e'` comes before `a + e` and the two linear pieces overlap. -/
private theorem forall_mem_Icc_linearFlow_mem_target {y : M} {a τ c₁ c₂ : ℝ} (hc : 0 < c₁ + c₂)
    (ha : hX.flow a y ∈ φ.toChart.source) (hτ : hX.flow τ y ∈ φ.toChart.source)
    (h₁ : (∀ t, 0 ≤ t → φ.linearFlow t (φ.coord (φ.toChart (hX.flow a y))) ∈
        φ.coord.symm ⁻¹' φ.toChart.target) ∨
      ∃ e, 0 ≤ e ∧ (∀ t ∈ Icc 0 e, φ.linearFlow t (φ.coord (φ.toChart (hX.flow a y))) ∈
        φ.coord.symm ⁻¹' φ.toChart.target) ∧
        (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow e (φ.coord (φ.toChart (hX.flow a y))) i ^ 2 ≤
          -c₁)
    (h₂ : (∀ t, 0 ≤ t → φ.linearFlow (-t) (φ.coord (φ.toChart (hX.flow τ y))) ∈
        φ.coord.symm ⁻¹' φ.toChart.target) ∨
      ∃ e, 0 ≤ e ∧ (∀ t ∈ Icc 0 e, φ.linearFlow (-t) (φ.coord (φ.toChart (hX.flow τ y))) ∈
        φ.coord.symm ⁻¹' φ.toChart.target) ∧
        c₂ ≤ (2 : ℝ)⁻¹ * ∑ i, φ.weight i *
          φ.linearFlow (-e) (φ.coord (φ.toChart (hX.flow τ y))) i ^ 2) :
    ∀ t ∈ Icc 0 (τ - a), φ.linearFlow t (φ.coord (φ.toChart (hX.flow a y))) ∈
      φ.coord.symm ⁻¹' φ.toChart.target := by
  set w := φ.coord (φ.toChart (hX.flow a y))
  set ζ := φ.coord (φ.toChart (hX.flow τ y))
  -- A backward linear stretch of length `d` from `τ`, and the forward one of length `e` from `a`,
  -- in the form taken by `coord_toChart_flow_add`.
  have hB : ∀ d, 0 ≤ d → (∀ t ∈ Icc 0 d, φ.linearFlow (-t) ζ ∈
      φ.coord.symm ⁻¹' φ.toChart.target) →
      ∀ t ∈ uIcc 0 (-d), φ.coord.symm (φ.linearFlow t ζ) ∈ φ.toChart.target :=
    fun d hd hdV t ht ↦ by
      rw [uIcc_of_ge (neg_nonpos.2 hd)] at ht
      simpa using hdV (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- Once the linear orbit of `w` meets the backward linear orbit of `ζ`, they agree.
  have hmeet : ∀ e, φ.linearFlow e w = φ.linearFlow (-(τ - a - e)) ζ →
      ∀ t, φ.linearFlow t w = φ.linearFlow (-(τ - a - t)) ζ := fun e he t ↦ by
    rw [show t = (t - e) + e by ring, φ.linearFlow_add, he, ← φ.linearFlow_add]
    congr 1
    ring
  intro t ht
  rcases h₁ with hall | ⟨e, he, heV, heQ⟩
  · exact hall t ht.1
  rcases h₂ with hall' | ⟨e', he', he'V, he'Q⟩
  · -- The backward linear orbit of `ζ` covers the whole crossing.
    have hB' := coord_toChart_flow_add hφ hτ (hB (τ - a) (ht.1.trans ht.2) fun t ht ↦ hall' t ht.1)
    rw [show -(τ - a) + τ = a by ring] at hB'
    rw [hmeet 0 (by rw [φ.linearFlow_zero, sub_zero]; exact hB') t]
    exact hall' _ (by linarith [ht.2])
  rcases le_or_gt t e with hte | hte
  · exact heV t ⟨ht.1, hte⟩
  -- Both pieces end at levels of `f` beyond `f x - c₁` and `f x + c₂`, so they overlap.
  have hF : ∀ t ∈ uIcc 0 e, φ.coord.symm (φ.linearFlow t w) ∈ φ.toChart.target :=
    fun t ht ↦ heV t (by rwa [uIcc_of_le he] at ht)
  have hfF : f (hX.flow (e + a) y) =
      f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow e w i ^ 2 := by
    rw [φ.eq_quadratic _ (flow_add_mem_source_of_forall_mem_uIcc hφ ha hF),
      coord_toChart_flow_add hφ ha hF]
  have hfB : f (hX.flow (-e' + τ) y) =
      f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow (-e') ζ i ^ 2 := by
    rw [φ.eq_quadratic _ (flow_add_mem_source_of_forall_mem_uIcc hφ hτ (hB e' he' he'V)),
      coord_toChart_flow_add hφ hτ (hB e' he' he'V)]
  have hlt : -e' + τ < e + a := by
    by_contra hle
    have := hX.antitone_flow y (not_lt.1 hle)
    simp only [hfF, hfB] at this
    linarith
  have hB'' := coord_toChart_flow_add hφ hτ (hB (τ - a - e) (by linarith [ht.2]) fun t ht ↦
    he'V t ⟨ht.1, ht.2.trans (by linarith)⟩)
  rw [show -(τ - a - e) + τ = e + a by ring, coord_toChart_flow_add hφ ha hF] at hB''
  rw [hmeet e hB'' t]
  exact he'V _ ⟨by linarith [ht.2], by linarith⟩

/-- **Orbits near a broken trajectory cross the Morse chart linearly.** Let `y₀` be a point of
`W^s(x)` with a time `a` of linear forward flow in the Morse chart `φ` at `x`, and `z₀` a point of
`W^u(x)` with a time `b` of linear backward flow. If `yₙ → y₀` and `Φ_{Tₙ} yₙ → z₀`, then eventually
the linear orbit of the coordinates of `Φ_a yₙ` stays in the chart for the times between `0` and
`Tₙ - a - b`: the orbit of `yₙ` crosses the chart of `x` along the linear flow. -/
theorem eventually_forall_linearFlow_mem_target_of_broken (hf : IsMorse 𝓘(ℝ, E) f) {y₀ z₀ : M}
    {a b : ℝ} (hy₀ : y₀ ∈ hX.flow.stableSet x) (ha : a ∈ hX.linearForwardTimes φ y₀)
    (hz₀ : z₀ ∈ hX.flow.unstableSet x) (hb : b ∈ hX.linearBackwardTimes φ z₀)
    {ι : Type*} {l : Filter ι} {y : ι → M} {T : ι → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (hz : Tendsto (fun n ↦ hX.flow (T n) (y n)) l (𝓝 z₀)) :
    ∀ᶠ n in l, ∀ t ∈ Icc 0 (T n - a - b),
      φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow a (y n))))) ∈
        φ.toChart.target := by
  have := φ.finiteDimensional
  have ha' := (hX.mem_linearForwardTimes φ).1 ha
  have hb' := (hX.mem_linearBackwardTimes φ).1 hb
  have hV := φ.isOpen_preimage_coord_symm_target
  have h0 := φ.zero_mem_preimage_coord_symm_target
  -- The model statements forwards from `Φ_a y₀` and backwards from `Φ_{-b} z₀`.
  obtain ⟨c₁, hc₁, h₁⟩ :=
    φ.toMorseBottChart.exists_pos_eventually_forall_linearFlow_mem_or_exists_le_neg
      φ.weight_eq_neg_one_or_eq_one hV h0
      (fun i hi ↦ by
        have h := congrFun (negativeCoord_toChart_flow_eq_zero_of_mem_stableSet hφ hy₀ ha) ⟨i, hi⟩
        simpa using h) ha'.2
  obtain ⟨c₂, hc₂, h₂⟩ :=
    φ.toMorseBottChart.exists_pos_eventually_forall_linearFlow_neg_mem_or_exists_le
      φ.weight_eq_neg_one_or_eq_one hV h0
      (fun i hi ↦ coord_toChart_flow_neg_eq_zero_of_not_weight_neg hφ hf hz₀ hb (not_lt.2 hi.le))
      fun t ht ↦ hb'.2 (-t) (by linarith)
  -- The orbits of `yₙ` pass near `Φ_a y₀` at the time `a` and near `Φ_{-b} z₀` at `Tₙ - b`.
  have hfa : Tendsto (fun n ↦ hX.flow a (y n)) l (𝓝 (hX.flow a y₀)) :=
    ((hX.flow.continuous continuous_const continuous_id).tendsto y₀).comp hy
  have hfb : Tendsto (fun n ↦ hX.flow (-b + T n) (y n)) l (𝓝 (hX.flow (-b) z₀)) := by
    refine (((hX.flow.continuous continuous_const continuous_id).tendsto z₀).comp hz).congr
      fun n ↦ ?_
    rw [Function.comp_apply, id, ← Flow.map_add]
  filter_upwards [((φ.continuous_coord.tendsto _).comp
      ((φ.toChart.continuousAt ha'.1).tendsto.comp hfa)).eventually h₁,
    ((φ.continuous_coord.tendsto _).comp
      ((φ.toChart.continuousAt hb'.1).tendsto.comp hfb)).eventually h₂,
    hfa.eventually (φ.toChart.open_source.mem_nhds ha'.1),
    hfb.eventually (φ.toChart.open_source.mem_nhds hb'.1)] with n hn₁ hn₂ hna hnb t ht
  exact forall_mem_Icc_linearFlow_mem_target hφ (add_pos hc₁ hc₂) hna hnb hn₁ hn₂ t
    (by rwa [show -b + T n - a = T n - a - b by ring])

end IsAdaptedPseudoGradient

end TauCeti
