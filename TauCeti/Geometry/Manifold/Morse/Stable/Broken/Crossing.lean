/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Frame

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
(`TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_mem`) says that for every `w`
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

* `TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_mem`,
  `TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_neg_mem`: the model statements
  about forward and backward linear orbits.
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

namespace MorseBottChart

variable (φ : MorseBottChart E f x)

/-- With weights `±1`, the quadratic form along the linear flow is `e^{-2t} P - e^{2t} S`, where
`P` and `S` are the sums of the squares of the coordinates of positive and negative weight. -/
private theorem sum_weight_mul_linearFlow_sq (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1)
    (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    ∑ i, φ.weight i * φ.linearFlow t z i ^ 2 =
      Real.exp (-(2 * t)) * ∑ i, (if φ.weight i = 1 then z i ^ 2 else 0) -
        Real.exp (2 * t) * ∑ i, (if φ.weight i = 1 then 0 else z i ^ 2) := by
  have h2 (s : ℝ) : Real.exp s ^ 2 = Real.exp (2 * s) := by rw [sq, ← Real.exp_add, two_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases hw i with hi | hi
  · simp only [linearFlow_apply, hi, mul_pow, h2, show (-1 : ℝ) ≠ 1 by norm_num, ite_false]
    ring_nf
  · simp only [linearFlow_apply, hi, mul_pow, h2, ite_true]
    ring_nf

/-- **The exit time.** With weights `±1`, let `S > 0` and `P` be the sums of the squares of the
coordinates of `w` of negative and of positive weight, with `S ≤ ρ²` and `S P ≤ ρ⁴ / 2`. At the time
`e ≥ 0` with `e^{e} √S = ρ`, the coordinates of negative weight are at most `ρ` and the quadratic
form `(1/2) Σᵢ wᵢ zᵢ²` of the linear flow is at most `-ρ² / 4`. -/
private theorem exists_exit_time (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1) {ρ : ℝ}
    (hρ : 0 < ρ) {w : Fin (Module.finrank ℝ E) → ℝ}
    (hS : 0 < ∑ i, (if φ.weight i = 1 then 0 else w i ^ 2))
    (hSρ : ∑ i, (if φ.weight i = 1 then 0 else w i ^ 2) ≤ ρ ^ 2)
    (hSP : (∑ i, (if φ.weight i = 1 then 0 else w i ^ 2)) *
      ∑ i, (if φ.weight i = 1 then w i ^ 2 else 0) ≤ ρ ^ 4 / 2) :
    ∃ e, 0 ≤ e ∧ (∀ i, φ.weight i ≠ 1 → Real.exp e * |w i| ≤ ρ) ∧
      (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow e w i ^ 2 ≤ -(ρ ^ 2 / 4) := by
  set S := ∑ i, (if φ.weight i = 1 then 0 else w i ^ 2)
  set P := ∑ i, (if φ.weight i = 1 then w i ^ 2 else 0)
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hexp : Real.exp (Real.log (ρ / Real.sqrt S)) = ρ / Real.sqrt S :=
    Real.exp_log (div_pos hρ hsqrt)
  refine ⟨Real.log (ρ / Real.sqrt S),
    Real.log_nonneg ((one_le_div hsqrt).2 (Real.sqrt_le_iff.2 ⟨hρ.le, hSρ⟩)), fun i hi ↦ ?_, ?_⟩
  · -- Each coordinate of negative weight is at most `√S`.
    have hwi : w i ^ 2 ≤ S := by
      have h := Finset.single_le_sum (f := fun j ↦ if φ.weight j = 1 then 0 else w j ^ 2)
        (fun j _ ↦ by split_ifs <;> positivity) (Finset.mem_univ i)
      simpa [hi] using h
    calc Real.exp (Real.log (ρ / Real.sqrt S)) * |w i| ≤ ρ / Real.sqrt S * Real.sqrt S := by
          rw [hexp]
          gcongr
          exact Real.abs_le_sqrt hwi
      _ = ρ := div_mul_cancel₀ _ hsqrt.ne'
  · -- At the exit time `e^{2e} = ρ² / S`, so the quadratic form is `S P / ρ² - ρ² ≤ -ρ² / 2`.
    have h2e : Real.exp (2 * Real.log (ρ / Real.sqrt S)) = ρ ^ 2 / S := by
      rw [two_mul, Real.exp_add, hexp, div_mul_div_comm, Real.mul_self_sqrt hS.le, sq]
    have hP : S / ρ ^ 2 * P ≤ ρ ^ 2 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [sum_weight_mul_linearFlow_sq φ hw, Real.exp_neg, h2e, inv_div,
      div_mul_cancel₀ _ hS.ne']
    linarith

/-- With weights `±1`, after the time `t₀` the linear flow of `w` lies in the cube of radius `ρ`,
as long as its coordinates of negative weight do, provided `e^{-t₀} ‖w‖ ≤ ρ`. -/
private theorem norm_linearFlow_le_of_le (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1)
    {w : Fin (Module.finrank ℝ E) → ℝ} {ρ t₀ t : ℝ} (hρ : 0 ≤ ρ) (ht : t₀ ≤ t)
    (hw₀ : Real.exp (-t₀) * ‖w‖ ≤ ρ) (hneg : ∀ i, φ.weight i ≠ 1 → Real.exp t * |w i| ≤ ρ) :
    ‖φ.linearFlow t w‖ ≤ ρ := by
  refine (pi_norm_le_iff_of_nonneg hρ).2 fun i ↦ ?_
  rcases hw i with hi | hi
  · rw [linearFlow_apply, hi, neg_one_mul, neg_neg, norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    exact hneg i (by rw [hi]; norm_num)
  · rw [linearFlow_apply, hi, one_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-t) * ‖w i‖ ≤ Real.exp (-t₀) * ‖w‖ := by
          gcongr
          exact norm_le_pi_norm w i
      _ ≤ ρ := hw₀

/-- Near a point `w₀` without coordinates of negative weight, the sum `S` of the squares of the
coordinates of negative weight is small, and so is its product with the sum `P` of the squares of
those of positive weight: `S ≤ ρ²` and `S P ≤ ρ⁴ / 2`. -/
private theorem eventually_sum_sq_le (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1)
    {w₀ : Fin (Module.finrank ℝ E) → ℝ} (hw₀ : ∀ i, φ.weight i < 0 → w₀ i = 0) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∀ᶠ w in 𝓝 w₀, ∑ i, (if φ.weight i = 1 then 0 else w i ^ 2) ≤ ρ ^ 2 ∧
      (∑ i, (if φ.weight i = 1 then 0 else w i ^ 2)) *
        ∑ i, (if φ.weight i = 1 then w i ^ 2 else 0) ≤ ρ ^ 4 / 2 := by
  have hSc : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ ↦
      ∑ i, (if φ.weight i = 1 then 0 else z i ^ 2) :=
    continuous_finsetSum _ fun i _ ↦ by split_ifs <;> fun_prop
  have hPc : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ ↦
      ∑ i, (if φ.weight i = 1 then z i ^ 2 else 0) :=
    continuous_finsetSum _ fun i _ ↦ by split_ifs <;> fun_prop
  have hS₀ : ∑ i, (if φ.weight i = 1 then 0 else w₀ i ^ 2) = 0 := Finset.sum_eq_zero fun i _ ↦ by
    split_ifs with hi
    · rfl
    · rw [hw₀ i (by rcases hw i with h | h <;> simp_all), sq, zero_mul]
  have hSP := (hSc.tendsto w₀).mul (hPc.tendsto w₀)
  have hS := hSc.tendsto w₀
  rw [hS₀, zero_mul] at hSP
  rw [hS₀] at hS
  exact (hS.eventually (ge_mem_nhds (by positivity))).and
    (hSP.eventually (ge_mem_nhds (by positivity)))

/-- **Linear orbits near an orbit of the stable plane.** Let the weights be `±1`, let `V` be an
open set of coordinates containing the origin, and let `w₀` have no coordinates of negative weight,
with forward linear orbit in `V`. There is `c > 0` such that for every `w` near `w₀`, either the
whole forward linear orbit of `w` lies in `V`, or it lies in `V` up to a time `e ≥ 0` at which the
quadratic form `(1/2) Σᵢ wᵢ zᵢ²` is at most `-c`. -/
theorem exists_pos_eventually_forall_linearFlow_mem
    (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1) {V : Set (Fin (Module.finrank ℝ E) → ℝ)}
    (hV : IsOpen V) (h0 : 0 ∈ V) {w₀ : Fin (Module.finrank ℝ E) → ℝ}
    (hw₀ : ∀ i, φ.weight i < 0 → w₀ i = 0) (hw₀V : ∀ t, 0 ≤ t → φ.linearFlow t w₀ ∈ V) :
    ∃ c > 0, ∀ᶠ w in 𝓝 w₀, (∀ t, 0 ≤ t → φ.linearFlow t w ∈ V) ∨
      ∃ e, 0 ≤ e ∧ (∀ t ∈ Icc 0 e, φ.linearFlow t w ∈ V) ∧
        (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow e w i ^ 2 ≤ -c := by
  -- A cube of radius `ρ` about the origin lies in `V`, and after the time `t₀` the coordinates of
  -- positive weight of points near `w₀` are at most `ρ`. Near `w₀` the sums `S` and `P` of the
  -- squares of the coordinates of negative and positive weight satisfy `eventually_sum_sq_le`.
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.1 hV 0 h0
  have hρ : 0 < ρ' / 2 := half_pos hρ'
  have hcube : ∀ z, ‖z‖ ≤ ρ' / 2 → z ∈ V := fun z hz ↦
    hball (mem_ball_zero_iff.2 (hz.trans_lt (half_lt_self hρ')))
  obtain ⟨t₀, ht₀ρ⟩ : ∃ t₀, Real.exp (-t₀) * (‖w₀‖ + 1) ≤ ρ' / 2 :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (‖w₀‖ + 1)).eventually
      (ge_mem_nhds (by simpa using hρ))).exists
  -- Up to the time `t₀` the orbits of points near `w₀` follow that of `w₀`, by compactness.
  have hinit : ∀ᶠ w in 𝓝 w₀, ∀ t ∈ Icc 0 t₀, φ.linearFlow t w ∈ V :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦
      φ.continuous_linearFlow_uncurry.continuousAt.preimage_mem_nhds (hV.mem_nhds (hw₀V t ht.1))
  refine ⟨(ρ' / 2) ^ 2 / 4, by positivity, ?_⟩
  filter_upwards [φ.eventually_sum_sq_le hw hw₀ hρ, hinit, ball_mem_nhds w₀ one_pos]
    with w ⟨hSw, hSPw⟩ hinitw hwb
  have hw1 : Real.exp (-t₀) * ‖w‖ ≤ ρ' / 2 := le_trans (by
    gcongr
    linarith [norm_le_norm_add_norm_sub' w w₀, (mem_ball_iff_norm.1 hwb).le]) ht₀ρ
  have hlate : ∀ t, t₀ ≤ t → (∀ i, φ.weight i ≠ 1 → Real.exp t * |w i| ≤ ρ' / 2) →
      φ.linearFlow t w ∈ V := fun t ht hneg ↦
    hcube _ (φ.norm_linearFlow_le_of_le hw hρ.le ht hw1 hneg)
  rcases (Finset.sum_nonneg fun i _ ↦ by split_ifs <;> positivity :
    0 ≤ ∑ i, (if φ.weight i = 1 then 0 else w i ^ 2)).eq_or_lt with hS0 | hSpos
  · -- Without coordinates of negative weight, the whole orbit stays in `V`.
    refine Or.inl fun t ht ↦ (le_total t₀ t).elim (fun h ↦ hlate t h fun i hi ↦ ?_)
      fun h ↦ hinitw t ⟨ht, h⟩
    have hwi : w i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ by split_ifs <;> positivity)).1
        hS0.symm i (Finset.mem_univ i)
      simpa [hi] using this
    rw [hwi, abs_zero, mul_zero]
    exact hρ.le
  · -- Otherwise the orbit stays in `V` up to the exit time.
    obtain ⟨e, he, heneg, heQ⟩ := φ.exists_exit_time hw hρ hSpos hSw hSPw
    refine Or.inr ⟨e, he, fun t ht ↦ (le_total t₀ t).elim
      (fun h ↦ hlate t h fun i hi ↦ le_trans (by gcongr; exact ht.2) (heneg i hi))
      fun h ↦ hinitw t ⟨ht.1, h⟩, heQ⟩

/-- **Linear orbits near an orbit of the unstable plane**, the backward counterpart of
`TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_mem`. Let the weights be `±1`, let
`V` be an open set of coordinates containing the origin, and let `ζ₀` have no coordinates of
positive weight, with backward linear orbit in `V`. There is `c > 0` such that for every `ζ` near
`ζ₀`, either the whole backward linear orbit of `ζ` lies in `V`, or it lies in `V` back to a time
`-e ≤ 0` at which the quadratic form `(1/2) Σᵢ wᵢ zᵢ²` is at least `c`. -/
theorem exists_pos_eventually_forall_linearFlow_neg_mem
    (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1) {V : Set (Fin (Module.finrank ℝ E) → ℝ)}
    (hV : IsOpen V) (h0 : 0 ∈ V) {ζ₀ : Fin (Module.finrank ℝ E) → ℝ}
    (hζ₀ : ∀ i, 0 < φ.weight i → ζ₀ i = 0) (hζ₀V : ∀ t, 0 ≤ t → φ.linearFlow (-t) ζ₀ ∈ V) :
    ∃ c > 0, ∀ᶠ ζ in 𝓝 ζ₀, (∀ t, 0 ≤ t → φ.linearFlow (-t) ζ ∈ V) ∨
      ∃ e, 0 ≤ e ∧ (∀ t ∈ Icc 0 e, φ.linearFlow (-t) ζ ∈ V) ∧
        c ≤ (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow (-e) ζ i ^ 2 := by
  -- Apply the forward statement to the negated chart, whose linear flow runs backwards.
  have hwn : ∀ i, φ.neg.weight i = -1 ∨ φ.neg.weight i = 1 := fun i ↦ by
    rcases hw i with h | h <;> simp [h]
  obtain ⟨c, hc, h⟩ := φ.neg.exists_pos_eventually_forall_linearFlow_mem hwn hV h0
    (fun i hi ↦ hζ₀ i (by simpa using hi)) fun t ht ↦ by
      rw [neg_linearFlow]
      exact hζ₀V t ht
  refine ⟨c, hc, h.mono fun ζ hζ ↦ ?_⟩
  simp only [neg_linearFlow, neg_weight, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
    mul_neg] at hζ
  exact hζ.imp_right fun ⟨e, he, heV, heQ⟩ ↦ ⟨e, he, heV, by linarith⟩

end MorseBottChart

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {hX : IsAdaptedPseudoGradient f X}
  {φ : MorseChart E f x}
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- Along a linear stretch of an orbit in the chart, the coordinates of the orbit follow the linear
flow and `f` is given by the quadratic normal form of those coordinates. -/
private theorem flow_add_mem_source_and_eq {y : M} {T s : ℝ}
    (hT : hX.flow T y ∈ φ.toChart.source)
    (hs : ∀ t ∈ uIcc 0 s, φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈
      φ.toChart.target) :
    φ.coord (φ.toChart (hX.flow (s + T) y)) =
        φ.linearFlow s (φ.coord (φ.toChart (hX.flow T y))) ∧
      f (hX.flow (s + T) y) = f x + (2 : ℝ)⁻¹ *
        ∑ i, φ.weight i * φ.linearFlow s (φ.coord (φ.toChart (hX.flow T y))) i ^ 2 := by
  have hc := coord_toChart_flow_add hφ hT hs
  exact ⟨hc, by rw [φ.eq_quadratic _ (flow_add_mem_source_of_forall_mem_uIcc hφ hT hs), hc]⟩

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
  -- The backward linear stretch of length `d` from `τ`, read on the orbit.
  have hB : ∀ d, 0 ≤ d → (∀ t ∈ Icc 0 d, φ.linearFlow (-t) ζ ∈
      φ.coord.symm ⁻¹' φ.toChart.target) → φ.coord (φ.toChart (hX.flow (-d + τ) y)) =
        φ.linearFlow (-d) ζ ∧ f (hX.flow (-d + τ) y) =
          f x + (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow (-d) ζ i ^ 2 := fun d hd hdV ↦
    flow_add_mem_source_and_eq hφ hτ fun t ht ↦ by
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
    have hB' := (hB (τ - a) (ht.1.trans ht.2) fun t ht ↦ hall' t ht.1).1
    rw [show -(τ - a) + τ = a by ring] at hB'
    rw [hmeet 0 (by rw [φ.linearFlow_zero, sub_zero]; exact hB') t]
    exact hall' _ (by linarith [ht.2])
  rcases le_or_gt t e with hte | hte
  · exact heV t ⟨ht.1, hte⟩
  -- Both pieces end at levels of `f` beyond `f x - c₁` and `f x + c₂`, so they overlap.
  have hfF := (flow_add_mem_source_and_eq hφ ha fun t ht ↦ heV t (by rwa [uIcc_of_le he] at ht)).2
  have hlt : -e' + τ < e + a := by
    by_contra hle
    have := hX.antitone_flow y (not_lt.1 hle)
    simp only [hfF, (hB e' he' he'V).2] at this
    linarith
  have hB'' := (hB (τ - a - e) (by linarith [ht.2]) fun t ht ↦
    he'V t ⟨ht.1, ht.2.trans (by linarith)⟩).1
  rw [show -(τ - a - e) + τ = e + a by ring,
    (coord_toChart_flow_add hφ ha fun t ht ↦ heV t (by rwa [uIcc_of_le he] at ht))] at hB''
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
  obtain ⟨c₁, hc₁, h₁⟩ := φ.toMorseBottChart.exists_pos_eventually_forall_linearFlow_mem
    φ.weight_eq_neg_one_or_eq_one hV h0
    (fun i hi ↦ by
      have h := congrFun (negativeCoord_toChart_flow_eq_zero_of_mem_stableSet hφ hy₀ ha) ⟨i, hi⟩
      simpa using h) ha'.2
  obtain ⟨c₂, hc₂, h₂⟩ := φ.toMorseBottChart.exists_pos_eventually_forall_linearFlow_neg_mem
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
