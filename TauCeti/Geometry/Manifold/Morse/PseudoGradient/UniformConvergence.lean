/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local

/-!
# Uniform exponential convergence on compact parts of stable sets

Let `X` be a pseudo-gradient field adapted to a function `f` on a compact boundaryless manifold,
and `φ` a Morse chart at a critical point `x` in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`.
Every orbit in the stable set `W^s(x)` converges to `x`, and once it is in a small coordinate cube
of `φ` its coordinates are `e^{-t}` times their entrance value. This file shows that the
convergence is uniform, at the same exponential rate, on each compact subset `K` of `W^s(x)`:
there are `T` and `C` such that for every `y ∈ K` and every `t ≥ T` the point `flow t y` lies in
the chart, its coordinates of negative weight vanish and its coordinates have size at most
`C e^{-t}`. Consequently `f (flow t y) - f x ≤ C' e^{-2t}`, and `flow t y → x` uniformly in
`y ∈ K`, which we state as convergence along the filter `atTop ×ˢ 𝓟 K`. The reversed field `-X`
gives the same statements for compact subsets of unstable sets as `t → -∞`.

These estimates control families of trajectories near their ends: all the trajectories
through a compact family enter a fixed Morse box at a common time and then follow the linear
flow, as the compactness and gluing arguments for spaces of trajectories require.

The proof is local-to-global. In the chart, the set `V` of points of a small cube is open, and
on `V ∩ W^s(x)` the flow is the linear contraction
(`TauCeti.IsAdaptedPseudoGradient.exists_forall_coord_flow_eq_exp_smul`), so `V ∩ W^s(x)` is
forward invariant. Each orbit from `K` enters `V` at some integer time `n`, and so does every
orbit from the open set `(flow n)⁻¹' V`. Finitely many of these open sets cover `K`, which bounds
the entrance times uniformly.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_forall_norm_coord_flow_le_mul_exp`: the coordinates of
  `flow t y` decay like `C e^{-t}` uniformly for `y` in a compact subset of `W^s(x)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_forall_sub_le_mul_exp`: the energy `f (flow t y) - f x`
  decays like `C e^{-2t}`, uniformly on such a compact set.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_flow_atTop_prod_principal`: the orbits from a compact
  subset of `W^s(x)` converge to `x` uniformly.
* `TauCeti.IsAdaptedPseudoGradient.exists_forall_norm_coord_flow_le_mul_exp_of_unstableSet`,
  `TauCeti.IsAdaptedPseudoGradient.exists_forall_sub_le_mul_exp_of_unstableSet` and
  `TauCeti.IsAdaptedPseudoGradient.tendsto_flow_atBot_prod_principal`: the same in backward time
  for compact subsets of `W^u(x)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_forall_exists_norm_coord_flow_eq` and
  `TauCeti.IsAdaptedPseudoGradient.exists_forall_exists_norm_coord_flow_eq_of_unstableSet`: the
  orbit of a point of `W^s(x)` or `W^u(x)` other than `x` crosses every small coordinate sphere
  of the chart, on the coordinate subspace of the stable or unstable set.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 and Chapter 3 (pseudo-gradients that are linear near the critical points, and the
  compactness of spaces of trajectories).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- **Uniform exponential decay in a Morse chart.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ`
in the Morse chart `φ`, and `K` a compact subset of the stable set `W^s(x)`. There are `T` and `C`
such that for every `y ∈ K` and `t ≥ T`, the point `flow t y` lies in the chart, its coordinates of
negative weight vanish, and its coordinates have size at most `C e^{-t}`. -/
theorem exists_forall_norm_coord_flow_le_mul_exp (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ hX.flow.stableSet x) :
    ∃ T C : ℝ, ∀ y ∈ K, ∀ t, T ≤ t → hX.flow t y ∈ φ.toChart.source ∧
      (∀ i, φ.weight i < 0 → φ.coord (φ.toChart (hX.flow t y)) i = 0) ∧
      ‖φ.coord (φ.toChart (hX.flow t y))‖ ≤ C * Real.exp (-t) := by
  obtain ⟨ρ, hρ, hρs⟩ := hX.exists_forall_coord_flow_eq_exp_smul φ hφ hf
  obtain ⟨ε, hε, hεs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ hf
  -- The open cube `V` of radius `min ρ ε` around `x`, read in the chart.
  set δ := min ρ ε
  set V := φ.toChart.source ∩ φ.toChart ⁻¹' (φ.coord ⁻¹' Metric.ball 0 δ)
  have hV : IsOpen V := φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
    (Metric.isOpen_ball.preimage φ.continuous_coord)
  have hxV : x ∈ V := ⟨φ.mem_source, by simp [φ.apply_self, δ, hρ, hε]⟩
  -- Every orbit from `K` enters `V` at an integer time, and finitely many times suffice.
  have hcover : K ⊆ ⋃ n : ℕ, hX.flow n ⁻¹' V := fun y hy ↦ by
    obtain ⟨n, hn⟩ := (((Flow.mem_stableSet.1 (hKs hy)).comp
      tendsto_natCast_atTop_atTop).eventually (hV.mem_nhds hxV)).exists
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n : ℕ ↦ hX.flow n ⁻¹' V)
    (fun n ↦ hV.preimage (hX.flow.continuous_toFun n)) hcover
  set N : ℕ := s.sup id
  refine ⟨N, δ * Real.exp N, fun y hy t ht ↦ ?_⟩
  obtain ⟨n, hns, hn⟩ := mem_iUnion₂.1 (hs hy)
  have hnN : (n : ℝ) ≤ N := Nat.cast_le.2 (Finset.le_sup (f := id) hns)
  -- At time `n` the orbit is in `V ∩ W^s(x)`, where the flow is the linear contraction.
  set w := hX.flow n y
  have hws : w ∈ hX.flow.stableSet x := (Flow.apply_mem_stableSet_iff _ _).2 (hKs hy)
  have hwδ : ‖φ.coord (φ.toChart w)‖ < δ := mem_ball_zero_iff.1 hn.2
  obtain ⟨hmem, heq⟩ := hρs w hws hn.1 (hwδ.trans_le (min_le_left _ _)) (t - n) (by linarith)
  have htw : hX.flow t y = hX.flow (t - n) w := by
    rw [← Flow.map_add, sub_add_cancel]
  rw [htw]
  refine ⟨hmem, fun i hi ↦ ?_, ?_⟩
  · have hu := (hεs w hn.1 (hwδ.trans_le (min_le_right _ _))).1 hws
    rw [heq, Pi.smul_apply, hu i hi, smul_zero]
  · rw [heq, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-(t - n)) * ‖φ.coord (φ.toChart w)‖
        = ‖φ.coord (φ.toChart w)‖ * Real.exp n * Real.exp (-t) := by
          rw [neg_sub, sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ δ * Real.exp N * Real.exp (-t) := by gcongr

/-- **Uniform exponential decay of the energy.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in
the Morse chart `φ`, and `K` a compact subset of the stable set `W^s(x)`. There are `T` and `C`
such that `f (flow t y) - f x ≤ C e^{-2t}` for every `y ∈ K` and `t ≥ T`. -/
theorem exists_forall_sub_le_mul_exp (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ hX.flow.stableSet x) :
    ∃ T C : ℝ, ∀ y ∈ K, ∀ t, T ≤ t → f (hX.flow t y) - f x ≤ C * Real.exp (-2 * t) := by
  obtain ⟨T, C, hTC⟩ := hX.exists_forall_norm_coord_flow_le_mul_exp φ hφ hf hK hKs
  refine ⟨T, Module.finrank ℝ E / 2 * C ^ 2, fun y hy t ht ↦ ?_⟩
  obtain ⟨hmem, -, hle⟩ := hTC y hy t ht
  set z := φ.coord (φ.toChart (hX.flow t y))
  -- In the normal form `f = f x + ½ Σ wᵢ zᵢ²`, each term is at most `‖z‖² ≤ (C e^{-t})²`.
  have hterm (i : Fin (Module.finrank ℝ E)) : φ.weight i * z i ^ 2 ≤ (C * Real.exp (-t)) ^ 2 := by
    have hzi : z i ^ 2 ≤ (C * Real.exp (-t)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm z i).trans hle) 2
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi <;> rw [hi] <;> nlinarith [sq_nonneg (z i)]
  have hsum : ∑ i, φ.weight i * z i ^ 2 ≤ Module.finrank ℝ E * (C * Real.exp (-t)) ^ 2 := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hterm i
  have hexp : (C * Real.exp (-t)) ^ 2 = C ^ 2 * Real.exp (-2 * t) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  rw [φ.eq_quadratic _ hmem]
  rw [hexp] at hsum
  linarith

/-- **Uniform convergence on compact parts of a stable set.** The orbits of the flow of an
adapted pseudo-gradient from a compact subset `K` of the stable set `W^s(x)` converge to `x`
uniformly on `K`: `flow t y → x` as `t → ∞`, uniformly in `y ∈ K`. -/
theorem tendsto_flow_atTop_prod_principal (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ hX.flow.stableSet x) :
    Tendsto (fun p : ℝ × M ↦ hX.flow p.1 p.2) (atTop ×ˢ 𝓟 K) (𝓝 x) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp
  -- A point with a converging orbit is a rest point, hence a critical point with a Morse chart.
  have hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 := hX.mfderiv_eq_zero_of_forall_eq (hf x) fun t ↦ by
    rw [Flow.fixed_of_mem_stableSet (hKs hy) t]
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart x hx
  obtain ⟨T, C, hTC⟩ := hX.exists_forall_norm_coord_flow_le_mul_exp φ hφ hf hK hKs
  intro U hU
  rw [mem_map]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (φ.tendsto_toChart_symm_coord_symm_nhds_zero hU)
  have hsmall : Tendsto (fun t ↦ C * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  have hev : ∀ᶠ t in atTop, T ≤ t ∧ C * Real.exp (-t) < δ :=
    (eventually_ge_atTop T).and (hsmall.eventually (gt_mem_nhds hδ))
  filter_upwards [prod_mem_prod hev (mem_principal_self K)] with p hp
  obtain ⟨hmem, -, hle⟩ := hTC p.2 hp.2 p.1 hp.1.1
  have h := hball (mem_ball_zero_iff.2 (hle.trans_lt hp.1.2))
  rwa [mem_preimage, φ.toChart_symm_coord_symm_coord hmem] at h

/-- **Uniform exponential decay in a Morse chart, backward in time.** Let `f` be a Morse function,
`X` the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ` at the critical point `x`, and `K` a
compact subset of the unstable set `W^u(x)`. There are `T` and `C` such that for every `y ∈ K` and
`t ≤ T`, the point `flow t y` lies in the chart, its coordinates of positive weight vanish, and its
coordinates have size at most `C e^{t}`. -/
theorem exists_forall_norm_coord_flow_le_mul_exp_of_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {K : Set M} (hK : IsCompact K) (hKu : K ⊆ hX.flow.unstableSet x) :
    ∃ T C : ℝ, ∀ y ∈ K, ∀ t, t ≤ T → hX.flow t y ∈ φ.toChart.source ∧
      (∀ i, 0 < φ.weight i → φ.coord (φ.toChart (hX.flow t y)) i = 0) ∧
      ‖φ.coord (φ.toChart (hX.flow t y))‖ ≤ C * Real.exp t := by
  -- Backward in time, `X` is the reversed field `-X` of the Morse function `-f`.
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl)
  obtain ⟨T, C, hTC⟩ := (hX.neg hf).exists_forall_norm_coord_flow_le_mul_exp (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd) (hf.neg.contMDiff.mdifferentiable (by simp)) hK
    (hX.unstableSet_eq_stableSet_neg hf x ▸ hKu)
  refine ⟨-T, C, fun y hy t ht ↦ ?_⟩
  have h := hTC y hy (-t) (by linarith)
  simpa only [hX.neg_flow hf, Flow.reverse_apply, neg_neg, MorseChart.neg_toChart,
    MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply, Left.neg_neg_iff] using h

/-- **Uniform exponential decay of the energy, backward in time.** Let `f` be a Morse function,
`X` the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ` at the critical point `x`, and `K` a
compact subset of the unstable set `W^u(x)`. There are `T` and `C` such that
`f x - f (flow t y) ≤ C e^{2t}` for every `y ∈ K` and `t ≤ T`. -/
theorem exists_forall_sub_le_mul_exp_of_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {K : Set M} (hK : IsCompact K) (hKu : K ⊆ hX.flow.unstableSet x) :
    ∃ T C : ℝ, ∀ y ∈ K, ∀ t, t ≤ T → f x - f (hX.flow t y) ≤ C * Real.exp (2 * t) := by
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl)
  obtain ⟨T, C, hTC⟩ := (hX.neg hf).exists_forall_sub_le_mul_exp (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd) (hf.neg.contMDiff.mdifferentiable (by simp)) hK
    (hX.unstableSet_eq_stableSet_neg hf x ▸ hKu)
  refine ⟨-T, C, fun y hy t ht ↦ ?_⟩
  have h := hTC y hy (-t) (by linarith)
  rw [show -2 * -t = 2 * t by ring] at h
  simp only [hX.neg_flow hf, Flow.reverse_apply, neg_neg, Pi.neg_apply] at h
  linarith

/-- **Uniform convergence on compact parts of an unstable set.** For a Morse function `f`, the
orbits of the flow of an adapted pseudo-gradient from a compact subset `K` of the unstable set
`W^u(x)` converge to `x` uniformly on `K` as `t → -∞`. -/
theorem tendsto_flow_atBot_prod_principal (hf : IsMorse 𝓘(ℝ, E) f) {K : Set M}
    (hK : IsCompact K) (hKu : K ⊆ hX.flow.unstableSet x) :
    Tendsto (fun p : ℝ × M ↦ hX.flow p.1 p.2) (atBot ×ˢ 𝓟 K) (𝓝 x) := by
  have h := ((hX.neg hf).tendsto_flow_atTop_prod_principal
    (hf.neg.contMDiff.mdifferentiable (by simp)) hK
    (hX.unstableSet_eq_stableSet_neg hf x ▸ hKu)).comp
    (tendsto_neg_atBot_atTop.prodMap (tendsto_id (x := 𝓟 K)))
  refine h.congr fun p ↦ ?_
  simp [hX.neg_flow hf, Flow.reverse_apply]

/-- **Stable orbits cross every small coordinate sphere.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ` at `x`, and `y ≠ x` a point of `W^s(x)`. For every small
enough `ε > 0`, the orbit of `y` passes through a point of the chart whose coordinates of negative
weight vanish and whose coordinates have sup norm exactly `ε`. -/
theorem exists_forall_exists_norm_coord_flow_eq (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {y : M} (hy : y ∈ hX.flow.stableSet x) (hyx : y ≠ x) :
    ∃ m > 0, ∀ ε, 0 < ε → ε ≤ m → ∃ t, hX.flow t y ∈ φ.toChart.source ∧
      (∀ i, φ.weight i < 0 → φ.coord (φ.toChart (hX.flow t y)) i = 0) ∧
      ‖φ.coord (φ.toChart (hX.flow t y))‖ = ε := by
  obtain ⟨T, C, hTC⟩ := hX.exists_forall_norm_coord_flow_le_mul_exp φ hφ hf isCompact_singleton
    (singleton_subset_iff.2 hy)
  set g : ℝ → ℝ := fun t ↦ ‖φ.coord (φ.toChart (hX.flow t y))‖
  have hg : ContinuousOn g (Ici T) :=
    (φ.continuous_coord.comp_continuousOn (φ.toChart.continuousOn.comp
      (hX.flow.continuous continuous_id continuous_const).continuousOn
      fun t ht ↦ (hTC y rfl t ht).1)).norm
  -- At time `T` the orbit is in the chart but not at `x`, so its coordinates are nonzero.
  have hT := (hTC y rfl T le_rfl).1
  have hgT : 0 < g T := by
    refine norm_pos_iff.2 fun h0 ↦ hyx ?_
    have hx := (φ.toChart_eq_zero_iff hT).1 (φ.coord.map_eq_zero_iff.1 h0)
    rw [← Flow.map_zero_apply hX.flow y, ← neg_add_cancel T, Flow.map_add, hx,
      Flow.fixed_of_mem_stableSet hy]
  refine ⟨g T, hgT, fun ε hε hεT ↦ ?_⟩
  -- The coordinates decay to `0`, so they reach the norm `ε` by the intermediate value theorem.
  have hlim : Tendsto (fun t ↦ C * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  obtain ⟨t₁, ht₁, hCt₁⟩ := ((eventually_ge_atTop T).and (hlim.eventually (ge_mem_nhds hε))).exists
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' ht₁ (hg.mono Icc_subset_Ici_self)
    ⟨(hTC y rfl t₁ ht₁).2.2.trans hCt₁, hεT⟩
  obtain ⟨hmem, hzero, -⟩ := hTC y rfl t ht.1
  exact ⟨t, hmem, hzero, hgt⟩

/-- **Unstable orbits cross every small coordinate sphere.** Let `f` be a Morse function, `X` the
linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ` at `x`, and `y ≠ x` a point of `W^u(x)`. For
every small enough `ε > 0`, the orbit of `y` passes through a point of the chart whose coordinates
of positive weight vanish and whose coordinates have sup norm exactly `ε`. -/
theorem exists_forall_exists_norm_coord_flow_eq_of_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {y : M} (hy : y ∈ hX.flow.unstableSet x) (hyx : y ≠ x) :
    ∃ m > 0, ∀ ε, 0 < ε → ε ≤ m → ∃ t, hX.flow t y ∈ φ.toChart.source ∧
      (∀ i, 0 < φ.weight i → φ.coord (φ.toChart (hX.flow t y)) i = 0) ∧
      ‖φ.coord (φ.toChart (hX.flow t y))‖ = ε := by
  -- Backward in time, `X` is the reversed field `-X` of the Morse function `-f`.
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl)
  obtain ⟨m, hm, h⟩ := (hX.neg hf).exists_forall_exists_norm_coord_flow_eq (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd) (hf.neg.contMDiff.mdifferentiable (by simp))
    (hX.unstableSet_eq_stableSet_neg hf x ▸ hy) hyx
  refine ⟨m, hm, fun ε hε hεm ↦ ?_⟩
  obtain ⟨t, ht⟩ := h ε hε hεm
  refine ⟨-t, ?_⟩
  simpa only [hX.neg_flow hf, Flow.reverse_apply, MorseChart.neg_toChart, MorseChart.neg_coord,
    MorseChart.neg_weight, Pi.neg_apply, Left.neg_neg_iff] using ht

end IsAdaptedPseudoGradient

end TauCeti
