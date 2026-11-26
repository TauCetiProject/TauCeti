/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow

/-!
# Local stable sets of an adapted pseudo-gradient

Near a critical point `x` of `f`, an adapted pseudo-gradient `X` reads in a Morse chart as the
linear field `z ↦ (-wᵢ zᵢ)ᵢ`. Its flow is therefore the linear flow `z ↦ (e^{-wᵢ t} zᵢ)ᵢ` for as
long as the orbit stays in the chart. On a small coordinate cube around `x`, this identifies the
stable set `W^s(x)` with the coordinate subspace `{zᵢ = 0 whenever wᵢ < 0}`.

A Morse chart is a Morse–Bott chart with no weight `0`, and an adapted pseudo-gradient is adapted in
the Morse–Bott sense (`TauCeti.IsAdaptedPseudoGradient.isBottAdaptedPseudoGradient`), with the same
flow (`TauCeti.IsAdaptedPseudoGradient.isBottAdaptedPseudoGradient_flow`). The statements of this
file are therefore the special case of those of `TauCeti.Geometry.Manifold.Morse.Bott.Flow` in
which the only critical point near `x` is `x` itself. One inclusion is read off the linear flow. The
other is the energy barrier: an orbit starting in the cube off the coordinate subspace reaches a
level below `f x` before leaving the chart, and `f` decreases along orbits, so the orbit cannot
converge to `x`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm_of_forall_mem_uIcc`: the flow of an adapted
  pseudo-gradient is the linear flow at time `t`, when the linear orbit stays in the chart on the
  closed interval between `0` and `t`.
* `TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm_of_forall_coord_eq_zero`: on the coordinate
  subspace of the positive weights, the flow is the contraction `z ↦ e^{-t} z`.
* `TauCeti.IsAdaptedPseudoGradient.mem_stableSet_of_forall_coord_eq_zero`: near `x`, the points
  of the coordinate subspace of the positive weights lie in `W^s(x)`.
* `TauCeti.IsAdaptedPseudoGradient.norm_linearFlow_lt_and_flow_eq_of_exp_mul_lt`: the flow is
  the linear flow until a coordinate of negative weight has grown.
* `TauCeti.IsAdaptedPseudoGradient.apply_flow_lt_of_le_exp_mul`: the energy barrier for the other
  points near `x`, with a bound on the time at which it is crossed.
* `TauCeti.IsAdaptedPseudoGradient.exists_forall_mem_stableSet_iff`: on a small coordinate cube,
  `W^s(x)` is the coordinate subspace of the positive weights.
* `TauCeti.IsAdaptedPseudoGradient.exists_forall_coord_flow_eq_exp_smul`: on a small coordinate
  cube, points of `W^s(x)` move by the linear contraction `z ↦ e^{-t} z` for all `t ≥ 0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- The linear flow of the negated Morse chart runs the linear flow backwards. -/
theorem neg_linearFlow (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) (t : ℝ)
    (z : Fin (Module.finrank ℝ E) → ℝ) : (φ.neg h).linearFlow t z = φ.linearFlow (-t) z := by
  rw [toMorseBottChart_neg]
  exact φ.toMorseBottChart.neg_linearFlow t z

/-- In a Morse chart, the projection onto the coordinates of weight `0` is zero: every weight is
`±1`. -/
theorem ite_weight_eq_zero (z : Fin (Module.finrank ℝ E) → ℝ) :
    (fun i ↦ if φ.weight i = 0 then z i else 0) = 0 := by
  funext i
  rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> simp [hi]

end MorseChart

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

/-- **In a Morse chart, the flow of an adapted pseudo-gradient is linear up to time `t`.** If `X`
is the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and the linear orbit of `z` stays in
the chart for all times between `0` and `t`, then at time `t` the flow of `X` from the point with
coordinates `z` is the point with coordinates `(e^{-wᵢ t} zᵢ)ᵢ`. -/
theorem flow_toChart_symm_of_forall_mem_uIcc (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {z : Fin (Module.finrank ℝ E) → ℝ} {t : ℝ}
    (hz : ∀ s ∈ uIcc 0 t, φ.coord.symm (φ.linearFlow s z) ∈ φ.toChart.target) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (φ.linearFlow t z)) := by
  rw [← hX.isBottAdaptedPseudoGradient_flow]
  exact hX.isBottAdaptedPseudoGradient.flow_toChart_symm_of_forall_mem_uIcc φ.toMorseBottChart hφ hz

/-- **On the stable subspace the flow contracts.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in
the Morse chart `φ`, and let `z` be small coordinates vanishing in every direction of negative
weight. Then for `t ≥ 0` the flow moves the point with coordinates `z` to the point with
coordinates `e^{-t} z`. -/
theorem flow_toChart_symm_of_forall_coord_eq_zero (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ < r / 2) (hu : ∀ i, φ.weight i < 0 → z i = 0) {t : ℝ} (ht : 0 ≤ t) :
    hX.flow t (φ.toChart.symm (φ.coord.symm z)) =
      φ.toChart.symm (φ.coord.symm (Real.exp (-t) • z)) := by
  have hlin : φ.linearFlow t z = Real.exp (-t) • z := by
    ext i
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · rw [φ.linearFlow_of_weight_eq_neg_one hi, Pi.smul_apply, hu i (by rw [hi]; norm_num),
        mul_zero, smul_zero]
    · rw [φ.linearFlow_of_weight_eq_one hi, Pi.smul_apply, smul_eq_mul]
  rw [← hlin, ← hX.isBottAdaptedPseudoGradient_flow]
  exact hX.isBottAdaptedPseudoGradient.flow_toChart_symm_of_forall_coord_eq_zero
    φ.toMorseBottChart hφ hrT hz hu ht

/-- **Points of the stable subspace converge to the critical point.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and let the coordinates of `y` be small and vanish in every
direction of negative weight. Then the orbit of `y` converges to `x`. -/
theorem mem_stableSet_of_forall_coord_eq_zero (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source) (hyr : ‖φ.coord (φ.toChart y)‖ < r / 2)
    (hu : ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) : y ∈ hX.flow.stableSet x := by
  have h := hX.isBottAdaptedPseudoGradient.tendsto_flow_of_forall_coord_eq_zero φ.toMorseBottChart
    hφ hrT hy hyr hu
  rw [φ.ite_weight_eq_zero, φ.toChart_symm_coord_symm_zero, hX.isBottAdaptedPseudoGradient_flow]
    at h
  exact Flow.mem_stableSet.2 h

/-- **The flow is linear until a coordinate of negative weight grows.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and let the coordinates of `y` have norm less than `r / 2`.
At a time `t ≥ 0` by which no coordinate of negative weight of the linear orbit has grown to size
`r`, the linear orbit has norm less than `r`, and the orbit of `y` is the linear orbit read on the
manifold. -/
theorem norm_linearFlow_lt_and_flow_eq_of_exp_mul_lt (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source) (hyr : ‖φ.coord (φ.toChart y)‖ < r / 2) {t : ℝ}
    (ht : 0 ≤ t) (hsmall : ∀ i, φ.weight i < 0 → Real.exp t * |φ.coord (φ.toChart y) i| < r) :
    ‖φ.linearFlow t (φ.coord (φ.toChart y))‖ < r ∧
      hX.flow t y = φ.toChart.symm (φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart y)))) := by
  rw [← hX.isBottAdaptedPseudoGradient_flow]
  exact hX.isBottAdaptedPseudoGradient.norm_linearFlow_lt_and_flow_eq_of_exp_mul_lt
    φ.toMorseBottChart hφ hrT hy hyr ht hsmall

/-- **The energy barrier, with a time bound.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the
Morse chart `φ`, and let the coordinates of `y` be small compared with `r`. At every time `t` by
which a coordinate of negative weight of the linear orbit has grown to size `r`, the orbit of `y`
is below the level `f x`. -/
theorem apply_flow_lt_of_le_exp_mul (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {r : ℝ} (hrT : ∀ z, ‖z‖ < r → φ.coord.symm z ∈ φ.toChart.target)
    {y : M} (hy : y ∈ φ.toChart.source)
    (hyr : ‖φ.coord (φ.toChart y)‖ < r / (4 * (Module.finrank ℝ E + 1)))
    {t : ℝ} {j : Fin (Module.finrank ℝ E)} (hj : φ.weight j < 0)
    (hjr : r ≤ Real.exp t * |φ.coord (φ.toChart y) j|) :
    f (hX.flow t y) < f x := by
  rw [← hX.isBottAdaptedPseudoGradient_flow]
  exact hX.isBottAdaptedPseudoGradient.apply_flow_lt_of_le_exp_mul φ.toMorseBottChart hφ hrT hy hyr
    hj hjr

/-- **The local stable set in a Morse chart.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in
the Morse chart `φ`. On a small coordinate cube around `x`, a point lies in the stable set
`W^s(x)` exactly when its coordinates of negative weight vanish. -/
theorem exists_forall_mem_stableSet_iff (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∃ ε > 0, ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε →
      (y ∈ hX.flow.stableSet x ↔ ∀ i, φ.weight i < 0 → φ.coord (φ.toChart y) i = 0) := by
  obtain ⟨ε, hε, hs⟩ :=
    hX.isBottAdaptedPseudoGradient.exists_forall_mem_stableSet_iff φ.toMorseBottChart hφ
  refine ⟨ε, hε, fun y hy hyε ↦ ?_⟩
  -- There is no coordinate of weight `0`, so the condition on those coordinates is empty.
  have hw (i : Fin (Module.finrank ℝ E)) : φ.weight i ≠ 0 := by
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> simp [hi]
  rw [← hX.isBottAdaptedPseudoGradient_flow,
    hs y hy hyε x φ.mem_source φ.toMorseBottChart.mfderiv_self]
  exact and_iff_left fun i hi ↦ absurd hi (hw i)

/-- **The linear contraction on the local stable set.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`. On a small coordinate cube, a point `y` of `W^s(x)` stays
in the chart for all positive times, and its coordinates at time `t ≥ 0` are `e^{-t}` times those
of `y`. -/
theorem exists_forall_coord_flow_eq_exp_smul (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∃ ρ > 0, ∀ y ∈ hX.flow.stableSet x, y ∈ φ.toChart.source → ‖φ.coord (φ.toChart y)‖ < ρ →
      ∀ t, 0 ≤ t → hX.flow t y ∈ φ.toChart.source ∧
        φ.coord (φ.toChart (hX.flow t y)) = Real.exp (-t) • φ.coord (φ.toChart y) := by
  obtain ⟨ε, hε, hεs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  refine ⟨min ε (r / 2), by positivity, fun y hys hy hyρ t ht ↦ ?_⟩
  set z := φ.coord (φ.toChart y)
  have hu := (hεs y hy (hyρ.trans_le (min_le_left _ _))).1 hys
  have hz2 : ‖z‖ < r / 2 := hyρ.trans_le (min_le_right _ _)
  have hflow := hX.flow_toChart_symm_of_forall_coord_eq_zero φ hφ hrT hz2 hu ht
  rw [φ.toChart_symm_coord_symm_coord hy] at hflow
  -- The contracted coordinates are again coordinates of a point of the chart.
  have hnorm : ‖Real.exp (-t) • z‖ ≤ ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))
  have hT := hrT _ (hnorm.trans_lt (hz2.trans (half_lt_self hr)))
  rw [hflow]
  exact ⟨φ.toChart.map_target hT, by rw [φ.toChart.right_inv hT, LinearEquiv.apply_symm_apply]⟩

end IsAdaptedPseudoGradient

end TauCeti
