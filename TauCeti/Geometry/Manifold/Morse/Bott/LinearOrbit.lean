/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.PseudoGradient

/-!
# Linear orbits near the stable and unstable planes of a Morse chart

In the coordinates of a Morse–Bott chart with weights `wᵢ = ±1`, the linear flow
`Λ_t z = (e^{-wᵢ t} zᵢ)ᵢ` contracts the coordinates of positive weight and expands those of
negative weight. Let `V` be an open set of coordinates containing the origin and `w₀` a point
without coordinates of negative weight whose forward linear orbit stays in `V`. This file shows
that there is `c > 0` such that for every `w` near `w₀`, either the whole forward linear orbit of
`w` stays in `V`, or it stays in `V` up to a time `e` at which the quadratic form
`(1/2) Σᵢ wᵢ zᵢ²` is at most `-c`. Indeed, up to a fixed time the orbit of `w` follows that of
`w₀`; then it lies in a small cube about the origin, in which the coordinates of positive weight
keep shrinking, until the coordinates of negative weight have grown to the size of the cube, which
makes the quadratic form negative. The backward statement, near a point without coordinates of
positive weight, follows by negating the chart.

These model statements are the chart-level input to the crossing of a Morse chart by orbits near a
broken trajectory
(`TauCeti.IsAdaptedPseudoGradient.eventually_forall_linearFlow_mem_target_of_broken`).

## Main results

* `TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_mem_or_exists_le_neg`: forward
  linear orbits near an orbit of the stable plane stay in `V` or leave it after the quadratic form
  has dropped to `-c`.
* `TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_neg_mem_or_exists_le`: the
  backward counterpart near an orbit of the unstable plane.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the passage near a hyperbolic critical point).
-/

public section

open Filter Metric Set Topology

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
theorem exists_pos_eventually_forall_linearFlow_mem_or_exists_le_neg
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
`TauCeti.MorseBottChart.exists_pos_eventually_forall_linearFlow_mem_or_exists_le_neg`. Let the
weights be `±1`, let `V` be an open set of coordinates containing the origin, and let `ζ₀` have no
coordinates of positive weight, with backward linear orbit in `V`. There is `c > 0` such that for
every `ζ` near `ζ₀`, either the whole backward linear orbit of `ζ` lies in `V`, or it lies in `V`
back to a time `-e ≤ 0` at which the quadratic form `(1/2) Σᵢ wᵢ zᵢ²` is at least `c`. -/
theorem exists_pos_eventually_forall_linearFlow_neg_mem_or_exists_le
    (hw : ∀ i, φ.weight i = -1 ∨ φ.weight i = 1) {V : Set (Fin (Module.finrank ℝ E) → ℝ)}
    (hV : IsOpen V) (h0 : 0 ∈ V) {ζ₀ : Fin (Module.finrank ℝ E) → ℝ}
    (hζ₀ : ∀ i, 0 < φ.weight i → ζ₀ i = 0) (hζ₀V : ∀ t, 0 ≤ t → φ.linearFlow (-t) ζ₀ ∈ V) :
    ∃ c > 0, ∀ᶠ ζ in 𝓝 ζ₀, (∀ t, 0 ≤ t → φ.linearFlow (-t) ζ ∈ V) ∨
      ∃ e, 0 ≤ e ∧ (∀ t ∈ Icc 0 e, φ.linearFlow (-t) ζ ∈ V) ∧
        c ≤ (2 : ℝ)⁻¹ * ∑ i, φ.weight i * φ.linearFlow (-e) ζ i ^ 2 := by
  -- Apply the forward statement to the negated chart, whose linear flow runs backwards.
  have hwn : ∀ i, φ.neg.weight i = -1 ∨ φ.neg.weight i = 1 := fun i ↦ by
    rcases hw i with h | h <;> simp [h]
  obtain ⟨c, hc, h⟩ :=
    φ.neg.exists_pos_eventually_forall_linearFlow_mem_or_exists_le_neg hwn hV h0
      (fun i hi ↦ hζ₀ i (by simpa using hi)) fun t ht ↦ by
        rw [neg_linearFlow]
        exact hζ₀V t ht
  refine ⟨c, hc, h.mono fun ζ hζ ↦ ?_⟩
  simp only [neg_linearFlow, neg_weight, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
    mul_neg] at hζ
  exact hζ.imp_right fun ⟨e, he, heV, heQ⟩ ↦ ⟨e, he, heV, by linarith⟩

end MorseBottChart

end TauCeti
