/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic

/-!
# Orbits that lose little height stay close to where they start

Let `f` be a Morse function on a compact boundaryless manifold and `X` a pseudo-gradient field
adapted to `f`. Along an orbit of `X` the value of `f` decreases, and this file shows that an orbit
starting near a point `m` cannot travel far from `m` without losing a definite amount of height.

* **Near a regular point** `m`, an orbit starting close to `m` and losing height at most `ε` stays
  in a prescribed neighbourhood of `m`
  (`TauCeti.IsAdaptedPseudoGradient.exists_mem_nhds_forall_flow_mem_of_sub_le`). Indeed the orbit
  of every point close to `m` loses height at least `ε` within a short time, during which it does
  not leave the neighbourhood.
* **Near a critical point** `q`, an orbit starting close to `q` stays in a prescribed neighbourhood
  of `q` for as long as it remains above the level of `q`
  (`TauCeti.IsAdaptedPseudoGradient.exists_mem_nhds_forall_flow_mem_of_le`), and, backwards in
  time, for as long as it remains below that level
  (`TauCeti.IsAdaptedPseudoGradient.exists_mem_nhds_forall_flow_neg_mem_of_le`). In a Morse chart
  in which `X` is linear, the coordinates of negative weight grow along the orbit; once one of them
  is large compared with the starting point, the quadratic normal form, and so `f`, is below
  `f q` (`TauCeti.IsAdaptedPseudoGradient.apply_flow_lt_of_le_exp_mul`).

These are the local estimates behind the continuity of the parametrization of broken trajectories
by the values of `f`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_mem_nhds_forall_flow_mem_of_sub_le`: near a regular
  point, an orbit losing little height stays close.
* `TauCeti.IsAdaptedPseudoGradient.exists_mem_nhds_forall_flow_mem_of_le`: near a critical point,
  an orbit staying above its level stays close.
* `TauCeti.IsAdaptedPseudoGradient.exists_mem_nhds_forall_flow_neg_mem_of_le`: the same backwards
  in time, below the level.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 and Chapter 3.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **Near a regular point, an orbit losing little height stays close.** For a regular point `m`
of `f` and a neighbourhood `U` of `m`, there are a neighbourhood `V` of `m` and `ε > 0` such that
the orbit of every point `y` of `V` lies in `U` at every time `t ≥ 0` at which it has lost height
at most `ε`. -/
theorem exists_mem_nhds_forall_flow_mem_of_sub_le {m : M}
    (hm : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f m ≠ 0) {U : Set M} (hU : U ∈ 𝓝 m) :
    ∃ V ∈ 𝓝 m, ∃ ε > 0, ∀ y ∈ V, ∀ t, 0 ≤ t → f y - f (hX.flow t y) ≤ ε →
      hX.flow t y ∈ U := by
  have hf := hX.mdifferentiable.continuous
  -- For short times the orbits of the points close to `m` stay in `U`.
  have hcont : Continuous fun p : ℝ × M ↦ hX.flow p.1 p.2 :=
    hX.flow.continuous continuous_fst continuous_snd
  have hev : {p : ℝ × M | hX.flow p.1 p.2 ∈ U} ∈ 𝓝 (0, m) :=
    hcont.continuousAt (by simpa using hU)
  rw [nhds_prod_eq] at hev
  obtain ⟨S, hS, V₁, hV₁, hSV⟩ := mem_prod_iff.1 hev
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hS
  set τ := δ / 2 with hτdef
  have hτ : 0 < τ := half_pos hδ
  -- Within the time `τ`, the orbits of the points close to `m` lose height at least `ε`.
  set g : M → ℝ := fun y ↦ f y - f (hX.flow τ y)
  have hg : Continuous g := hf.sub (hf.comp (hX.flow.continuous continuous_const continuous_id))
  have hgm : 0 < g m := by
    have hanti := hX.strictAnti_comp (hX.isMIntegralCurve_flow m) (hX.mfderiv_flow_ne_zero hm)
    have := hanti hτ
    simp only [comp_apply, Flow.map_zero_apply] at this
    exact sub_pos.2 this
  refine ⟨V₁ ∩ g ⁻¹' Ioi (g m / 2), inter_mem hV₁ ((hg.isOpen_preimage _ isOpen_Ioi).mem_nhds
    (half_lt_self hgm)), g m / 2, half_pos hgm, fun y ⟨hyV, hyg⟩ t ht hdrop ↦ ?_⟩
  -- An orbit that has lost height at most `ε` has not reached the time `τ`.
  have htτ : t < τ := by
    by_contra! htτ
    have := hX.antitone_flow y htτ
    simp only [mem_preimage, mem_Ioi, g] at hyg
    linarith
  refine hSV (mk_mem_prod (hball ?_) hyV)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht]
  linarith

section Chart

variable {q : M} (φ : MorseChart E f q)
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  {R : ℝ} (hRT : ∀ z, ‖z‖ < R → φ.coord.symm z ∈ φ.toChart.target)
  {y : M} (hy : y ∈ φ.toChart.source)
  (hyR : ‖φ.coord (φ.toChart y)‖ < R / (4 * (Module.finrank ℝ E + 1)))
include hφ hRT hy hyR

/-- Starting with coordinates small compared with `R`, an orbit of a pseudo-gradient that is linear
in the Morse chart `φ` is, at every time `t ≥ 0` at which it is still above the level of `q`, the
linear orbit, and its coordinates have size less than `R`. -/
private theorem flow_eq_linearFlow_of_le {t : ℝ} (ht : 0 ≤ t) (hlev : f q ≤ f (hX.flow t y)) :
    ‖φ.linearFlow t (φ.coord (φ.toChart y))‖ < R ∧
      hX.flow t y = φ.toChart.symm (φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart y)))) := by
  have hR : 0 < R :=
    (div_pos_iff_of_pos_right (by positivity)).1 ((norm_nonneg _).trans_lt hyR)
  have hz2 : ‖φ.coord (φ.toChart y)‖ < R / 2 := hyR.trans_le (div_le_div_of_nonneg_left hR.le
    (by norm_num) (by linarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _)]))
  -- The coordinates of negative weight have not reached `R` by time `t`, so neither has the orbit.
  exact hX.norm_linearFlow_lt_and_flow_eq_of_exp_mul_lt φ hφ hRT hy hz2 ht fun i hi ↦
    not_le.1 fun h ↦ (hX.apply_flow_lt_of_le_exp_mul φ hφ hRT hy hyR hi h).not_ge hlev

end Chart

/-- **Near a critical point, an orbit staying above its level stays close.** For a critical point
`q` of `f` and a neighbourhood `U` of `q`, there is a neighbourhood `V` of `q` such that the orbit
of every point `y` of `V` lies in `U` at every time `t ≥ 0` at which it is still at height at least
`f q`. -/
theorem exists_mem_nhds_forall_flow_mem_of_le {q : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    {U : Set M} (hU : U ∈ 𝓝 q) :
    ∃ V ∈ 𝓝 q, ∀ y ∈ V, ∀ t, 0 ≤ t → f q ≤ f (hX.flow t y) → hX.flow t y ∈ U := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart q hq
  have := φ.finiteDimensional
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  -- The coordinates of a ball around `0` lie in the target and are sent into `U`.
  have hcont : ContinuousAt (fun z ↦ φ.toChart.symm (φ.coord.symm z)) 0 :=
    (φ.toChart.continuousAt_symm (hrT 0 (by simpa using hr))).comp
      φ.coord.symm.toLinearMap.continuous_of_finiteDimensional.continuousAt
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.1 (hcont (by simpa using hU))
  set R := min r ρ
  have hRT : ∀ z, ‖z‖ < R → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦
    hrT z (hz.trans_le (min_le_left _ _))
  -- The points of the chart with small coordinates form a neighbourhood of `q`.
  have hζ : ContinuousAt (fun y ↦ φ.coord (φ.toChart y)) q :=
    φ.coord.toLinearMap.continuous_of_finiteDimensional.continuousAt.comp
      (φ.toChart.continuousAt φ.mem_source)
  have hball := hζ (by simpa [φ.apply_self] using
    Metric.ball_mem_nhds 0 (div_pos (lt_min hr hρ) (by positivity) :
      0 < R / (4 * (Module.finrank ℝ E + 1))))
  refine ⟨_, inter_mem (φ.toChart.open_source.mem_nhds φ.mem_source) hball,
    fun y ⟨hy, hyR⟩ t ht hlev ↦ ?_⟩
  obtain ⟨hnorm, hflow⟩ := hX.flow_eq_linearFlow_of_le φ hφ hRT hy (by simpa using hyR) ht hlev
  rw [hflow]
  exact hρU (mem_ball_zero_iff.2 (hnorm.trans_le (min_le_right _ _)))

/-- **Near a critical point, an orbit staying below its level stays close backwards in time.** For
a critical point `q` of `f` and a neighbourhood `U` of `q`, there is a neighbourhood `V` of `q` such
that the orbit of every point `y` of `V` lies in `U` at every time `-t ≤ 0` at which it is still at
height at most `f q`. -/
theorem exists_mem_nhds_forall_flow_neg_mem_of_le (hf : IsMorse 𝓘(ℝ, E) f) {q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) {U : Set M} (hU : U ∈ 𝓝 q) :
    ∃ V ∈ 𝓝 q, ∀ y ∈ V, ∀ t, 0 ≤ t → f (hX.flow (-t) y) ≤ f q → hX.flow (-t) y ∈ U := by
  obtain ⟨V, hV, hVU⟩ :=
    (hX.neg hf).exists_mem_nhds_forall_flow_mem_of_le (mfderiv_neg_eq_zero_iff.2 hq) hU
  refine ⟨V, hV, fun y hy t ht hle ↦ ?_⟩
  have := hVU y hy t ht
  simp only [hX.neg_flow hf, Flow.reverse_apply, Pi.neg_apply, neg_le_neg_iff] at this
  exact this hle

end IsAdaptedPseudoGradient

end TauCeti
