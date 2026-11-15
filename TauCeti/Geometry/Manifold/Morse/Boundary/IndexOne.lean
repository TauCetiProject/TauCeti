/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum
import TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional

/-!
# The integral Morse boundary of a critical point of index one

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, and `p` a critical point of index `1`. Its unstable manifold `W^u(p)` is a line through
`p`, so `W^u(p) - {p}` consists of two trajectories, one leaving `p` in each direction. This file
shows that, for the signs of the integral Morse complex, these two trajectories always carry
opposite signs whenever they end at the same critical point. Consequently their contributions
to the integral boundary cancel, and with a single minimum every critical point of index `1` is
an integral cycle. This is the cancellation behind the integral Morse complexes of the sphere
with two maxima, of the torus and of the real projective plane in degree `1`.

The two trajectories are seen in a Morse chart `φ` at `p` in which `X` is linear. Its space `V` of
coordinates of negative weight is a line, oriented by the orientation of `W^u(p)` at `p`. For
small `c ∈ V`, the point `y_c` of the chart with coordinates `c` in the directions of negative
weight and `0` elsewhere lies on `W^u(p)`, and the unstable frame at `y_c` sends `c` to the
velocity `X y_c`
(`TauCeti.IsAdaptedPseudoGradient.eventually_mem_unstableSet_and_unstableFrame_eq`): in the chart
both vectors have coordinates `c` in the directions of negative weight, along which the linear
field is the identity. So at `y_c` the vector `c` points along the flow, while at `y_{-c}` it points
against it. For `c ≠ 0` the points `y_c` and `y_{-c}` therefore lie on different orbits, which are
the two trajectories leaving `p`
(`TauCeti.IsAdaptedPseudoGradient.eventually_unstableSet_eq_insert_union_orbit`).

If both trajectories end at a critical point `q` of index `0`, the sign of each of them compares
the orientation of `V` with the direction in which `f` decreases. The comparison maps at `y_c` and
`y_{-c}`, from `V` to `ℝ × V_q` with `V_q = 0`, differ by a negative factor, so the two signs are
opposite (`TauCeti.IsAdaptedPseudoGradient.trajectorySign_eq_neg_of_notMem_orbit`). Hence the
signed count of the trajectories from `p` to `q` vanishes as soon as both trajectories leaving `p`
end at `q` (`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_eq_zero_of_mem_stableSet`).
Under the Morse–Smale condition every trajectory leaving `p` ends at a critical point of index `0`,
so when `f` has a single such point `m`, no integral boundary has a component along `m`, and the
integral boundary of every critical point of index `1` is zero (in the namespace
`TauCeti.IsAdaptedPseudoGradient`,
`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero` and
`IsMorseSmale.signedMorseBoundary_single_eq_zero_of_unique_index_zero`). The mod-two counterpart
is `IsMorseSmale.morseBoundaryCoeff_eq_zero_of_unique_index_zero`, where the two trajectories
cancel because they are two.

The dual statement for a unique maximum does not hold over `ℤ`: on the real projective plane the
two trajectories from the maximum to the saddle carry the same sign. Whether they do depends on
the orientability of `M` along them, which the local argument here does not see.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `eventually_mem_unstableSet_and_unstableFrame_eq`: on the unstable axis of a Morse chart, the
  unstable frame of the coordinates is the velocity.
* `eventually_unstableSet_eq_insert_union_orbit`: at a critical point of index `1`, the unstable
  manifold is the critical point together with the orbits of `y_c` and `y_{-c}`.
* `trajectorySign_eq_neg_of_notMem_orbit`: two different trajectories from a critical point of
  index `1` to the same critical point carry opposite signs.
* `signedTrajectoryCount_eq_zero_of_mem_stableSet`: if both trajectories leaving a critical point
  of index `1` end at `q`, the signed count of the trajectories to `q` is zero.
* `IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero`: no integral boundary has a
  component along a unique critical point of index `0`.
* `IsMorseSmale.signedMorseBoundary_single_eq_zero_of_unique_index_zero`: with a unique critical
  point of index `0`, the integral boundary of every critical point of index `1` vanishes.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations, and the computation for the sphere with
  two maxima, where the two flow lines from the saddle to the minimum carry opposite signs).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients, and its computation for the real
  projective plane).
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

variable {hX : IsAdaptedPseudoGradient f X} {p : M} {φ : MorseChart E f p}

section UnstableAxis

variable (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- A point of the unstable axis whose linear backward orbit stays in the chart lies on the
unstable manifold: for `t ≤ 0` its flow is the linear flow, which tends to the centre. -/
private theorem toChart_symm_negativeExtend_mem_unstableSet {c : {i // φ.weight i < 0} → ℝ}
    (hmem : ∀ t ≤ 0, φ.coord.symm (φ.linearFlow t (φ.coord (φ.negativeExtend c))) ∈
      φ.toChart.target) :
    φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet p := by
  set z := φ.coord (φ.negativeExtend c)
  have hlin (t : ℝ) : φ.linearFlow t z = Real.exp t • z := by
    simpa using φ.linearFlow_neg_coord_negativeExtend (-t) c
  rw [Flow.mem_unstableSet]
  have hflow : ∀ᶠ t in atBot, φ.toChart.symm (φ.coord.symm (Real.exp t • z)) =
      hX.flow t (φ.toChart.symm (φ.negativeExtend c)) := by
    filter_upwards [eventually_le_atBot 0] with t ht
    rw [← LinearEquiv.symm_apply_apply φ.coord (φ.negativeExtend c),
      flow_toChart_symm_of_forall_mem_uIcc hX φ hφ fun s hs ↦
        hmem s (by rw [uIcc_of_ge ht] at hs; exact hs.2), hlin]
  refine Tendsto.congr' hflow ?_
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp t • z) atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.smul_const z
  have hlim : Tendsto (fun t : ℝ ↦ φ.toChart.symm (φ.coord.symm (Real.exp t • z))) atBot
      (𝓝 (φ.toChart.symm (φ.coord.symm 0))) :=
    (φ.toChart.continuousAt_symm (by simpa using φ.toChart.map_source φ.mem_source)).tendsto.comp
      (((φ.coord.symm.toLinearMap.continuous_of_finiteDimensional).tendsto 0).comp hexp)
  rwa [φ.toChart_symm_coord_symm_zero] at hlim

/-- At a point of the unstable axis whose linear backward orbit stays in the chart, the unstable
frame of the coordinates is the velocity: in the chart, the frame is read through
`mfderiv_unstableFrame` at the time `0`, and the velocity through the linear field, which is the
identity on the negative directions. -/
private theorem unstableFrame_toChart_symm_negativeExtend {c : {i // φ.weight i < 0} → ℝ}
    (hmem : ∀ t ≤ 0, φ.coord.symm (φ.linearFlow t (φ.coord (φ.negativeExtend c))) ∈
      φ.toChart.target) :
    hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
      X (φ.toChart.symm (φ.negativeExtend c)) := by
  have htarget : φ.negativeExtend c ∈ φ.toChart.target := by
    simpa using hmem 0 le_rfl
  set y := φ.toChart.symm (φ.negativeExtend c)
  have hy : y ∈ φ.toChart.source := φ.toChart.map_target htarget
  have hcoord : φ.coord (φ.toChart y) = φ.coord (φ.negativeExtend c) := by
    rw [φ.toChart.right_inv htarget]
  have hT : (0 : ℝ) ∈ hX.linearBackwardTimes φ y := by
    refine (hX.mem_linearBackwardTimes φ).2 ⟨by simpa using hy, fun t ht ↦ ?_⟩
    simpa [hcoord] using hmem t ht
  have hF := mfderiv_unstableFrame hφ hT c
  have hcomp : (φ.toChart ∘ hX.flow (-0) : M → E) = φ.toChart := by
    funext w
    simp
  rw [hcomp, neg_zero, Real.exp_zero, one_smul] at hF
  have hV : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y) = φ.negativeExtend c := by
    refine φ.coord.injective (funext fun i ↦ ?_)
    simp only [hφ y hy, hcoord]
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · rw [hi]
      ring
    · rw [φ.coord_negativeExtend_of_not_weight_neg c (by rw [hi]; norm_num), mul_zero, neg_zero]
  have hinv := isInvertible_mfderiv_chart
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas) hy
  exact hinv.injective (hF.trans hV.symm)

/-- **The unstable axis of a Morse chart.** Let `X` be linear in the Morse chart `φ` at `p`. For
every small `c` in the space of coordinates of negative weight, the point `y` of the chart whose
coordinates are `c` in the directions of negative weight and `0` elsewhere lies on the unstable
manifold of `p`, and the unstable frame at `y` sends `c` to the velocity `X y`. -/
theorem eventually_mem_unstableSet_and_unstableFrame_eq :
    ∀ᶠ c in 𝓝 (0 : {i // φ.weight i < 0} → ℝ), φ.negativeExtend c ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet p ∧
        hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
          X (φ.toChart.symm (φ.negativeExtend c)) := by
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have hcont : Continuous fun c : {i // φ.weight i < 0} → ℝ ↦ φ.coord (φ.negativeExtend c) :=
    (φ.coord.toLinearMap.comp φ.negativeExtend).continuous_of_finiteDimensional
  have h0 : Tendsto (fun c : {i // φ.weight i < 0} → ℝ ↦ ‖φ.coord (φ.negativeExtend c)‖) (𝓝 0)
      (𝓝 0) := by
    simpa using (hcont.tendsto 0).norm
  filter_upwards [h0.eventually (gt_mem_nhds hr)] with c hc
  -- Along the negative directions the linear flow is the scaling by `e^{t}`, which keeps the
  -- point in the chart for `t ≤ 0`.
  have hmem (t : ℝ) (ht : t ≤ 0) :
      φ.coord.symm (φ.linearFlow t (φ.coord (φ.negativeExtend c))) ∈ φ.toChart.target := by
    refine hrT _ ?_
    have hlin : φ.linearFlow t (φ.coord (φ.negativeExtend c)) =
        Real.exp t • φ.coord (φ.negativeExtend c) := by
      simpa using φ.linearFlow_neg_coord_negativeExtend (-t) c
    rw [hlin, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ht)).trans_lt hc
  exact ⟨by simpa using hmem 0 le_rfl, toChart_symm_negativeExtend_mem_unstableSet hφ hmem,
    unstableFrame_toChart_symm_negativeExtend hφ hmem⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] hφ in
/-- A point of the unstable axis with nonzero coordinates is not the centre of the chart. -/
private theorem toChart_symm_negativeExtend_ne {c : {i // φ.weight i < 0} → ℝ} (hc : c ≠ 0)
    (hT : φ.negativeExtend c ∈ φ.toChart.target) : φ.toChart.symm (φ.negativeExtend c) ≠ p := by
  intro h
  have h0 : φ.negativeExtend c = 0 := by
    rw [← φ.toChart.right_inv hT, h, φ.apply_self]
  exact hc (φ.injective_negativeExtend (h0.trans (map_zero _).symm))

/-- On the unstable axis, the points with opposite coordinates `c` and `-c ≠ 0` lie on different
orbits: the unstable frame of `c` is the velocity at the first point and its opposite at the
second, while the flow carries the frame and the velocity at the first point to positive multiples
of those at the second. -/
private theorem notMem_orbit_toChart_symm_negativeExtend_neg (hf : IsMorse 𝓘(ℝ, E) f)
    {c : {i // φ.weight i < 0} → ℝ} (hc : c ≠ 0)
    (h₁ : φ.negativeExtend c ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet p ∧
      hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
        X (φ.toChart.symm (φ.negativeExtend c)))
    (h₂ : φ.negativeExtend (-c) ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.unstableSet p ∧
      hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend (-c))) (-c) =
        X (φ.toChart.symm (φ.negativeExtend (-c)))) :
    φ.toChart.symm (φ.negativeExtend (-c)) ∉
      hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) := by
  set y₁ := φ.toChart.symm (φ.negativeExtend c)
  set y₂ := φ.toChart.symm (φ.negativeExtend (-c))
  intro h
  obtain ⟨t, ht⟩ := (hX.flow.mem_orbit_iff).1 h
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ hf h₁.2.1).exists
  -- The frame at `y₂` on `c` is `e^{-t}` times the velocity, and also minus the velocity.
  have hflow := unstableFrame_flow hφ hT t c
  rw [h₁.2.2, hX.mfderiv_flow_apply_self, ht] at hflow
  have hneg : hX.unstableFrame φ y₂ c = -X y₂ := by
    rw [← h₂.2.2, map_neg, neg_neg]
  rw [hneg, eq_comm, ← sub_eq_zero, sub_neg_eq_add] at hflow
  have hsum : (Real.exp (-t) + 1) • X y₂ = 0 := by rwa [add_smul, one_smul]
  have hX0 : X y₂ = 0 := (smul_eq_zero.1 hsum).resolve_left (by positivity)
  -- So `y₂` is a rest point on the unstable manifold of `p`, hence `p` itself, which is not on
  -- the axis away from `0`.
  have hcrit := hX.eq_zero_iff.1 hX0
  refine toChart_symm_negativeExtend_ne (neg_ne_zero.2 hc) h₂.1 ?_
  have hlim := Flow.mem_unstableSet.1 h₂.2.1
  simp only [hX.flow_apply_of_mfderiv_eq_zero hcrit] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- On the unstable axis, the conclusions of
`TauCeti.IsAdaptedPseudoGradient.eventually_mem_unstableSet_and_unstableFrame_eq` hold at `c` and
at `-c` for all small `c`. -/
private theorem eventually_axis :
    ∀ᶠ c in 𝓝 (0 : {i // φ.weight i < 0} → ℝ),
      (φ.negativeExtend c ∈ φ.toChart.target ∧
        φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet p ∧
        hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
          X (φ.toChart.symm (φ.negativeExtend c))) ∧
      (φ.negativeExtend (-c) ∈ φ.toChart.target ∧
        φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.unstableSet p ∧
        hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend (-c))) (-c) =
          X (φ.toChart.symm (φ.negativeExtend (-c)))) := by
  have h := eventually_mem_unstableSet_and_unstableFrame_eq (hX := hX) hφ
  refine h.and ?_
  have hneg : Tendsto (fun c : {i // φ.weight i < 0} → ℝ ↦ -c) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_neg (0 : {i // φ.weight i < 0} → ℝ))
  exact hneg.eventually h

/-- **The two trajectories leaving a critical point of index one.** Let `X` be linear in the Morse
chart `φ` at a critical point `p` of index `1`. For every small `c ≠ 0` in the space of coordinates
of negative weight, which is a line, the points `y_c` and `y_{-c}` of the chart with coordinates
`c` and `-c` in the direction of negative weight and `0` elsewhere lie on different orbits, and the
unstable manifold of `p` is `p` together with these two orbits. -/
theorem eventually_unstableSet_eq_insert_union_orbit (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) :
    ∀ᶠ c in 𝓝[≠] (0 : {i // φ.weight i < 0} → ℝ),
      φ.toChart.symm (φ.negativeExtend (-c)) ∉
          hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∧
        hX.flow.unstableSet p = insert p (hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∪
          hX.flow.orbit (φ.toChart.symm (φ.negativeExtend (-c)))) := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_axis (hX := hX) hφ),
    self_mem_nhdsWithin] with c ⟨h₁, h₂⟩ hc
  set y₁ := φ.toChart.symm (φ.negativeExtend c)
  set y₂ := φ.toChart.symm (φ.negativeExtend (-c))
  have hc : c ≠ 0 := hc
  have hsep := notMem_orbit_toChart_symm_negativeExtend_neg hφ hf hc h₁ h₂
  refine ⟨hsep, ?_⟩
  obtain ⟨u₁, u₂, -, -, -, hW⟩ := hX.exists_unstableSet_eq_insert_union_orbit hf
    (hX.mfderiv_eq_zero_of_mem_unstableSet h₁.2.1) hp
  have hy₁ : y₁ ≠ p := toChart_symm_negativeExtend_ne hc h₁.1
  have hy₂ : y₂ ≠ p := toChart_symm_negativeExtend_ne (neg_ne_zero.2 hc) h₂.1
  have horb {y u : M} (h : y ∈ hX.flow.orbit u) : hX.flow.orbit y = hX.flow.orbit u := by
    obtain ⟨t, rfl⟩ := (hX.flow.mem_orbit_iff).1 h
    exact Flow.orbit_apply _ _ _
  have hmem₁ := h₁.2.1
  have hmem₂ := h₂.2.1
  rw [hW] at hmem₁ hmem₂
  rcases hmem₁ with h | h | h
  · exact absurd h hy₁
  all_goals rcases hmem₂ with h' | h' | h'
  all_goals first
    | exact absurd h' hy₂
    | exact absurd (by rw [horb h]; exact h') hsep
    | rw [hW, horb h, horb h']
  exact congrArg (insert p) (union_comm _ _)

end UnstableAxis

/-- If the unstable manifold of `p` is `p` together with the orbits of two points `a` and `b` of
trajectories from `p` to `q`, then the middle-level slice of the trajectories from `p` to `q`
consists of one point on each of these orbits. -/
private theorem exists_morseTrajectorySlice_eq_pair {q a b : M} (hpq : p ≠ q)
    (ha : a ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hb : b ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hU : hX.flow.unstableSet p = insert p (hX.flow.orbit a ∪ hX.flow.orbit b)) :
    ∃ za ∈ hX.flow.orbit a, ∃ zb ∈ hX.flow.orbit b,
      hX.morseTrajectorySlice p q = {za, zb} := by
  -- Each of the two trajectories crosses the middle level once.
  have hval := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpq ha
  have hlo : f q < (f p + f q) / 2 := by linarith [hval.1, hval.2]
  have hhi : (f p + f q) / 2 < f p := by linarith [hval.1, hval.2]
  obtain ⟨τa, hτa, huniqa⟩ :=
    hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpq ha hlo hhi
  obtain ⟨τb, hτb, huniqb⟩ :=
    hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpq hb hlo hhi
  refine ⟨hX.flow τa a, Flow.mem_orbit _ _ _, hX.flow τb b, Flow.mem_orbit _ _ _, ?_⟩
  ext z
  simp only [mem_morseTrajectorySlice, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hzu, -, hzc⟩
    have hzp : z ≠ p := by
      rintro rfl
      linarith
    rw [hU] at hzu
    rcases hzu with h | h | h
    · exact absurd h hzp
    · obtain ⟨t, rfl⟩ := (hX.flow.mem_orbit_iff).1 h
      exact Or.inl (by rw [huniqa t hzc])
    · obtain ⟨t, rfl⟩ := (hX.flow.mem_orbit_iff).1 h
      exact Or.inr (by rw [huniqb t hzc])
  · rintro (rfl | rfl)
    · exact ⟨(Flow.apply_mem_unstableSet_iff _ τa).2 ha.1,
        (Flow.apply_mem_stableSet_iff _ τa).2 ha.2, hτa⟩
    · exact ⟨(Flow.apply_mem_unstableSet_iff _ τb).2 hb.1,
        (Flow.apply_mem_stableSet_iff _ τb).2 hb.2, hτb⟩

section Sign

variable {q : M} {φq : MorseChart E f q}
  {op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
  {oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q))}
  {hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1}

/-- When `q` has index `0`, so that `ℝ × V_q` is a line, two isomorphic comparison maps that differ
by a negative factor give opposite signs. -/
private theorem trajectorySign_eq_neg_of_comparison_eq_smul
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) {y₁ y₂ : M}
    (hC₁ : Bijective (hX.trajectoryComparison φ φq y₁))
    (hC₂ : Bijective (hX.trajectoryComparison φ φq y₂)) {a : ℝ} (ha : a < 0)
    (h : ∀ v, hX.trajectoryComparison φ φq y₂ v = a • hX.trajectoryComparison φ φq y₁ v) :
    hX.trajectorySign φ φq op oq hpq y₂ = -hX.trajectorySign φ φq op oq hpq y₁ := by
  set e₁ := LinearEquiv.ofBijective (hX.trajectoryComparison φ φq y₁).toLinearMap hC₁
  set e₂ := LinearEquiv.ofBijective (hX.trajectoryComparison φ φq y₂).toLinearMap hC₂
  set B := LinearEquiv.smulOfNeZero ℝ (ℝ × ({i // φq.weight i < 0} → ℝ)) a ha.ne
  have he : e₂ = e₁.trans B := LinearEquiv.ext fun v ↦ by
    simp [e₁, e₂, B, LinearEquiv.ofBijective_apply, h]
  have hcard : Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) =
      Module.finrank ℝ (ℝ × ({i // φq.weight i < 0} → ℝ)) := by
    rw [Fintype.card_fin, Module.finrank_prod, Module.finrank_self, φq.finrank_negativeWeight_fun]
    omega
  -- `B` is the multiplication by `a < 0` on a line, so it reverses orientations.
  have hdet : LinearMap.det (B : (ℝ × ({i // φq.weight i < 0} → ℝ)) →ₗ[ℝ] _) < 0 := by
    have hB : (B : (ℝ × ({i // φq.weight i < 0} → ℝ)) →ₗ[ℝ] _) = a • LinearMap.id :=
      LinearMap.ext fun w ↦ by simp [B]
    rw [hB, LinearMap.det_smul, LinearMap.det_id, mul_one, ← hcard, Fintype.card_fin, hpq, hq,
      zero_add, pow_one]
    exact ha
  have hmap : Orientation.map _ e₂ op = Orientation.map _ e₁ (-op) := by
    rw [he, Orientation.map_trans,
      ((Orientation.map _ e₁ op).map_eq_neg_iff_det_neg B hcard).2 hdet, Orientation.map_neg]
  rw [trajectorySign_of_bijective hC₂, hmap, ← trajectorySign_of_bijective hC₁ (op := -op),
    trajectorySign_neg_left]

variable (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφ hφq

/-- On the unstable axis of a critical point of index `1`, the trajectories through `y_c` and
`y_{-c}` to a critical point of index `0` carry opposite signs: the two comparison maps differ by
a negative factor, since the unstable frame of `c` is the velocity at `y_c` and its opposite at
`y_{-c}`. -/
private theorem trajectorySign_toChart_symm_negativeExtend_neg (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    {c : {i // φ.weight i < 0} → ℝ} (hc : c ≠ 0)
    (h₁ : φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet p ∧
      hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
        X (φ.toChart.symm (φ.negativeExtend c)))
    (h₂ : φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.unstableSet p ∧
      hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend (-c))) (-c) =
        X (φ.toChart.symm (φ.negativeExtend (-c))))
    (hs₁ : φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.stableSet q)
    (hs₂ : φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.stableSet q) :
    hX.trajectorySign φ φq op oq hpq (φ.toChart.symm (φ.negativeExtend (-c))) =
      -hX.trajectorySign φ φq op oq hpq (φ.toChart.symm (φ.negativeExtend c)) := by
  set y₁ := φ.toChart.symm (φ.negativeExtend c)
  set y₂ := φ.toChart.symm (φ.negativeExtend (-c))
  have hne : p ≠ q := by
    rintro rfl
    omega
  have hm₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨h₁.1, hs₁⟩
  have hm₂ : y₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := ⟨h₂.1, hs₂⟩
  -- `f` decreases along the flow at both points.
  have hd₁ := hX.mvfderiv_apply_lt_zero y₁
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hm₁)
  have hd₂ := hX.mvfderiv_apply_lt_zero y₂
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hm₂)
  -- The space of coordinates of negative weight at `q` is zero, and the one at `p` is the line
  -- spanned by `c`.
  have : Subsingleton ({i // φq.weight i < 0} → ℝ) :=
    Module.finrank_zero_iff.1 (by rw [φq.finrank_negativeWeight_fun]; omega)
  have hV : Module.finrank ℝ ({i // φ.weight i < 0} → ℝ) = 1 := by
    rw [φ.finrank_negativeWeight_fun, hp]
  -- So the comparison map at `y₂` is the one at `y₁` times the negative factor `-d₂ / d₁`.
  set a := -mvfderiv 𝓘(ℝ, E) f y₂ (X y₂) / mvfderiv 𝓘(ℝ, E) f y₁ (X y₁)
  have ha₁ : a * mvfderiv 𝓘(ℝ, E) f y₁ (X y₁) = -mvfderiv 𝓘(ℝ, E) f y₂ (X y₂) :=
    div_mul_cancel₀ _ hd₁.ne
  refine trajectorySign_eq_neg_of_comparison_eq_smul (by omega)
    (bijective_trajectoryComparison hφ hφq hMS hf hpq hm₁)
    (bijective_trajectoryComparison hφ hφq hMS hf hpq hm₂)
    (a := a) (div_neg_of_pos_of_neg (neg_pos.2 hd₂) hd₁) fun v ↦ ?_
  obtain ⟨t, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' c hc).1 hV v
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  have hF₂ : hX.unstableFrame φ y₂ c = -X y₂ := by
    rw [← h₂.2, map_neg, neg_neg]
  simp only [trajectoryComparison_apply, map_smul, Prod.smul_fst, smul_eq_mul, hF₂, h₁.2,
    map_neg]
  linear_combination -t * ha₁

/-- **The two trajectories leaving a critical point of index one carry opposite signs.** Let `X`
be a Morse–Smale pseudo-gradient adapted to a Morse function `f`, linear in Morse charts at a
critical point `p` of index `1` and at a critical point `q` of index `0`. If `y₁` and `y₂` lie on
two different trajectories from `p` to `q`, then their signs are opposite, for every choice of the
orientations at `p` and `q`. -/
theorem trajectorySign_eq_neg_of_notMem_orbit (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hy₂ : y₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (h : y₂ ∉ hX.flow.orbit y₁) :
    hX.trajectorySign φ φq op oq hpq y₂ = -hX.trajectorySign φ φq op oq hpq y₁ := by
  have hne : p ≠ q := by
    rintro rfl
    omega
  have : Nontrivial ({i // φ.weight i < 0} → ℝ) :=
    Module.nontrivial_of_finrank_eq_succ (by rw [φ.finrank_negativeWeight_fun, hp])
  obtain ⟨c, ⟨h₁, h₂⟩, ⟨-, hW⟩, hc⟩ := ((eventually_nhdsWithin_of_eventually_nhds
    (eventually_axis (hX := hX) hφ)).and
      ((eventually_unstableSet_eq_insert_union_orbit hφ hf hp).and self_mem_nhdsWithin)).exists
  have hcrit := hX.mfderiv_eq_zero_of_mem_unstableSet h₁.2.1
  have horb {y u : M} (h : y ∈ hX.flow.orbit u) : hX.flow.orbit y = hX.flow.orbit u := by
    obtain ⟨t, rfl⟩ := (hX.flow.mem_orbit_iff).1 h
    exact Flow.orbit_apply _ _ _
  -- Each of `y₁` and `y₂` lies on the orbit of `y_c` or on that of `y_{-c}`, and has the sign of
  -- that point of the axis.
  have hmem {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
      y ∈ hX.flow.orbit (φ.toChart.symm (φ.negativeExtend c)) ∨
        y ∈ hX.flow.orbit (φ.toChart.symm (φ.negativeExtend (-c))) := by
    have hyu := hy.1
    rw [hW] at hyu
    exact hyu.resolve_left fun h ↦
      hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy (h ▸ hcrit)
  have hsign {y u : M} (hu : u ∈ hX.flow.unstableSet p)
      (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hyu : y ∈ hX.flow.orbit u) :
      u ∈ hX.flow.stableSet q ∧
        hX.trajectorySign φ φq op oq hpq y = hX.trajectorySign φ φq op oq hpq u := by
    obtain ⟨t, rfl⟩ := (hX.flow.mem_orbit_iff).1 hyu
    have hus : u ∈ hX.flow.stableSet q := (Flow.apply_mem_stableSet_iff _ t).1 hy.2
    exact ⟨hus, trajectorySign_flow hφ hφq hMS hf ⟨hu, hus⟩ t⟩
  have hab := trajectorySign_toChart_symm_negativeExtend_neg (op := op) (oq := oq) (hpq := hpq) hφ
    hφq hMS hf hp hc ⟨h₁.2.1, h₁.2.2⟩ ⟨h₂.2.1, h₂.2.2⟩
  rcases hmem hy₁ with h₁a | h₁b <;> rcases hmem hy₂ with h₂a | h₂b
  · exact (h (by rw [horb h₁a]; exact h₂a)).elim
  · obtain ⟨ha, hs₁⟩ := hsign h₁.2.1 hy₁ h₁a
    obtain ⟨hb, hs₂⟩ := hsign h₂.2.1 hy₂ h₂b
    rw [hs₁, hs₂, hab ha hb]
  · obtain ⟨hb, hs₁⟩ := hsign h₂.2.1 hy₁ h₁b
    obtain ⟨ha, hs₂⟩ := hsign h₁.2.1 hy₂ h₂a
    rw [hs₁, hs₂, hab ha hb, neg_neg]
  · exact (h (by rw [horb h₁b]; exact h₂b)).elim

/-- **The trajectories leaving a critical point of index one cancel.** Let `X` be a Morse–Smale
pseudo-gradient adapted to a Morse function `f`, linear in Morse charts at a critical point `p` of
index `1` and at a critical point `q` of index `0`. If both trajectories leaving `p` end at `q`,
then the signed count of the trajectories from `p` to `q` is zero, for every choice of the
orientations at `p` and `q`. -/
theorem signedTrajectoryCount_eq_zero_of_mem_stableSet (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    (hW : ∀ y ∈ hX.flow.unstableSet p, y ≠ p → y ∈ hX.flow.stableSet q) :
    hX.signedTrajectoryCount φ φq op oq hpq = 0 := by
  have hne : p ≠ q := by
    rintro rfl
    omega
  have : Nontrivial ({i // φ.weight i < 0} → ℝ) :=
    Module.nontrivial_of_finrank_eq_succ (by rw [φ.finrank_negativeWeight_fun, hp])
  obtain ⟨c, ⟨h₁, h₂⟩, ⟨hsep, hU⟩, hc⟩ := ((eventually_nhdsWithin_of_eventually_nhds
    (eventually_axis (hX := hX) hφ)).and
      ((eventually_unstableSet_eq_insert_union_orbit hφ hf hp).and self_mem_nhdsWithin)).exists
  set a := φ.toChart.symm (φ.negativeExtend c)
  set b := φ.toChart.symm (φ.negativeExtend (-c))
  have ha : a ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨h₁.2.1, hW a h₁.2.1 (toChart_symm_negativeExtend_ne hc h₁.1)⟩
  have hb : b ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨h₂.2.1, hW b h₂.2.1 (toChart_symm_negativeExtend_ne (neg_ne_zero.2 hc) h₂.1)⟩
  -- The slice consists of one crossing on each of the two orbits, which carry opposite signs.
  obtain ⟨za, hza, zb, hzb, hslice⟩ := exists_morseTrajectorySlice_eq_pair hne ha hb hU
  have hmem {z : M} (hz : z ∈ hX.morseTrajectorySlice p q) :
      z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨(hX.mem_morseTrajectorySlice.1 hz).1, (hX.mem_morseTrajectorySlice.1 hz).2.1⟩
  have hza' := hmem (hslice ▸ mem_insert za {zb})
  have hzb' := hmem (hslice ▸ mem_insert_of_mem za (mem_singleton zb))
  have hsep' : zb ∉ hX.flow.orbit za := by
    obtain ⟨s, rfl⟩ := (hX.flow.mem_orbit_iff).1 hza
    obtain ⟨t, rfl⟩ := (hX.flow.mem_orbit_iff).1 hzb
    rw [Flow.orbit_apply]
    intro h
    obtain ⟨u, hu⟩ := (hX.flow.mem_orbit_iff).1 h
    exact hsep ((hX.flow.mem_orbit_iff).2
      ⟨-t + u, by rw [Flow.map_add, hu, Flow.map_neg_apply_map]⟩)
  have hne' : za ≠ zb := fun h ↦
    hsep' (h ▸ (hX.flow.mem_orbit_iff).2 ⟨0, Flow.map_zero_apply _ _⟩)
  rw [signedTrajectoryCount_def, hslice, finsum_mem_pair hne',
    trajectorySign_eq_neg_of_notMem_orbit hφ hφq hMS hf hp hza' hzb' hsep', add_neg_cancel]

end Sign

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (𝔬 : MorseOrientation f X)
include h hf

/-- **No integral boundary reaches a unique critical point of index zero.** Under the Morse–Smale
condition, if `m` is the only critical point of index `0`, then its coefficient in the integral
boundary of every critical point vanishes, whatever the orientations: both trajectories leaving a
critical point of index `1` end at `m`, with opposite signs. -/
theorem signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero {m : criticalPoints 𝓘(ℝ, E) f}
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (p : criticalPoints 𝓘(ℝ, E) f) : hX.signedMorseBoundaryCoeff 𝔬 p m = 0 := by
  -- A point of minimum of `f` is a critical point of index `0`, hence `m`.
  have hm : manifoldMorseIndex 𝓘(ℝ, E) f m = 0 := by
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn ⟨(m : M), mem_univ _⟩
      hf.contMDiff.continuous.continuousOn
    have hmin : IsLocalMin f x := hx.isLocalMin Filter.univ_mem
    have hx0 := manifoldMorseIndex_eq_zero_of_isLocalMin
      ((hf.contMDiff.of_le (by norm_cast)).contMDiffAt (x := x)) hmin
    rw [← huniq x (mem_criticalPoints_iff_mfderiv_eq_zero.1 hmin.mem_criticalPoints) hx0]
    exact hx0
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f m + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hind]
    exact signedTrajectoryCount_eq_zero_of_mem_stableSet (𝔬.coord_mfderiv_chart p)
      (𝔬.coord_mfderiv_chart m) h hf (by omega) fun y hyu hyp ↦
        h.mem_stableSet_of_unique_index_zero hf (by omega) huniq hyu hyp
  · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hind

/-- **With a unique minimum, critical points of index one are integral cycles.** Under the
Morse–Smale condition, if `f` has at most one critical point of index `0`, then the integral Morse
boundary of every critical point of index `1` vanishes, with coefficients in any ring and whatever
the orientations. -/
theorem signedMorseBoundary_single_eq_zero_of_unique_index_zero {R : Type*} [Ring R]
    {p : criticalPoints 𝓘(ℝ, E) f} (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton)
    (a : R) : hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) = 0 := by
  ext q
  rw [signedMorseBoundary_single_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
  · have hqm (y : M) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0)
        (hy0 : manifoldMorseIndex 𝓘(ℝ, E) f y = 0) : y = q :=
      hmin ⟨hy, hy0⟩ ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2, hq⟩
    rw [h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬 hqm p, Int.cast_zero,
      mul_zero]
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega), Int.cast_zero,
      mul_zero]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
