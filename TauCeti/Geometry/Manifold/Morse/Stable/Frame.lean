/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Derivative
public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import TauCeti.Geometry.Manifold.TangentCone
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Normal coordinates of stable manifolds and frames of unstable manifolds

Let `X` be a pseudo-gradient adapted to `f` on a compact manifold, and `φ` a Morse chart at a
critical point `x` of index `k` in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. Write
`V = {i // wᵢ < 0} → ℝ` for the space of coordinates of negative weight, of dimension `k`. This file
transports the coordinate splitting of `φ` along the flow, to every point of the stable and the
unstable manifold of `x`:

* for `y ∈ W^s(x)`, the **normal coordinates** `hX.stableNormal φ y : T_y M → V`, a surjection
  whose kernel is the tangent space of `W^s(x)` at `y`
  (`TauCeti.IsAdaptedPseudoGradient.stableNormal_eq_zero_iff`);
* for `y ∈ W^u(x)`, the **unstable frame** `hX.unstableFrame φ y : V → T_y M`, an injection whose
  range is the tangent space of `W^u(x)` at `y`
  (`TauCeti.IsAdaptedPseudoGradient.range_unstableFrame`).

So an orientation of `V`, that is, of the unstable manifold of `x` at `x`, orients the tangent
space of `W^u(x)` at every point through the frame, and orients the normal space of `W^s(x)` at
every point through the normal coordinates. These are the orientations from which the signs of
the trajectories counted by the integral Morse differential are built.

Both maps are read off the flow. If the forward orbit of `y ∈ W^s(x)` has reached, at time `T`, the
part of the chart in which the flow is linear for all later times, the normal coordinates are
`e^{-T}` times the coordinates of negative weight of the derivative of `φ ∘ Φ_T` at `y`
(`TauCeti.IsAdaptedPseudoGradient.stableNormal_apply`). By the computation of the derivative of the
linear flow (`TauCeti.IsAdaptedPseudoGradient.coord_mfderiv_toChart_comp_flow`), waiting for a
further time `s` multiplies all coordinates of negative weight by `e^{s}`, since all these weights
are `-1`; the factor `e^{-T}` makes the result independent of `T`. The unstable frame is built in
the same way from the backward orbit of `y ∈ W^u(x)`, along which the coordinates of negative
weight shrink by `e^{-s}`: its value on `c ∈ V` is the vector whose image under the derivative of
`φ ∘ Φ_{-T}` has coordinates `e^{-T} c` in the directions of negative weight and `0` elsewhere
(`TauCeti.IsAdaptedPseudoGradient.mfderiv_unstableFrame`).

The tangent spaces are identified through the slice charts `φ ∘ Φ_T` and `φ ∘ Φ_{-T}` of the
stable and unstable manifolds
(`TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_stableSet_flow`), in which these manifolds
are the coordinate subspaces of the Morse chart.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `linearForwardTimes`, `linearBackwardTimes`: the times at which the forward, respectively
  backward, orbit of a point has entered the part of the chart where the flow stays linear.
* `stableNormal`: the normal coordinates of the stable manifold.
* `unstableFrame`: the frame of the unstable manifold.

## Main results

* `eventually_mem_linearForwardTimes`, `eventually_mem_linearBackwardTimes`: points of the
  stable, respectively unstable, manifold have admissible times.
* `stableNormal_apply`, `mfderiv_unstableFrame`: the two maps read at any admissible time.
* `eventually_span_mtangentConeAt_stableSet_eq_comap`: for all large times `T`, the tangent space
  of the stable manifold is read off the derivative of `φ ∘ Φ_T`.
* `stableNormal_eq_zero_iff`, `surjective_stableNormal`: the normal coordinates vanish exactly on
  the tangent space of the stable manifold, and are onto.
* `range_unstableFrame`, `injective_unstableFrame`: the frame is an isomorphism onto the tangent
  space of the unstable manifold.
* `stableNormal_mfderiv_flow`, `unstableFrame_flow`: along the flow, the derivative of the time-`t`
  map carries the normal coordinates and the frame to positive multiples of themselves.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 and Chapter 4.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)

/-- The **times of linear forward flow** of `y` in the Morse chart `φ`: the times `T` at which the
orbit of `y` lies in the chart, with coordinates whose linear forward orbit stays in the chart. -/
def linearForwardTimes (y : M) : Set ℝ :=
  {T | hX.flow T y ∈ φ.toChart.source ∧ ∀ t, 0 ≤ t →
    φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈ φ.toChart.target}

/-- The **times of linear backward flow** of `y` in the Morse chart `φ`: the times `T` at which
the orbit of `y` at time `-T` lies in the chart, with coordinates whose linear backward orbit stays
in the chart. -/
def linearBackwardTimes (y : M) : Set ℝ :=
  {T | hX.flow (-T) y ∈ φ.toChart.source ∧ ∀ t, t ≤ 0 →
    φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow (-T) y)))) ∈ φ.toChart.target}

/-- Membership in the times of linear forward flow. -/
theorem mem_linearForwardTimes {y : M} {T : ℝ} :
    T ∈ hX.linearForwardTimes φ y ↔ hX.flow T y ∈ φ.toChart.source ∧ ∀ t, 0 ≤ t →
      φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈ φ.toChart.target :=
  Iff.rfl

/-- Membership in the times of linear backward flow. -/
theorem mem_linearBackwardTimes {y : M} {T : ℝ} :
    T ∈ hX.linearBackwardTimes φ y ↔ hX.flow (-T) y ∈ φ.toChart.source ∧ ∀ t, t ≤ 0 →
      φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow (-T) y)))) ∈ φ.toChart.target :=
  Iff.rfl

/-- The **normal coordinates** of the stable manifold of the centre of the Morse chart `φ` at a
point `y`: `e^{-T}` times the coordinates of negative weight of the derivative of `φ ∘ Φ_T` at
`y`, for a time `T` of linear forward flow of `y`. When `X` is linear in `φ`, this does not depend
on `T` (`TauCeti.IsAdaptedPseudoGradient.stableNormal_apply`); it is meaningful for the points of
`W^s(x)`, which have such times. -/
noncomputable def stableNormal (y : M) :
    TangentSpace 𝓘(ℝ, E) y →L[ℝ] ({i // φ.weight i < 0} → ℝ) :=
  Real.exp (-Classical.epsilon (· ∈ hX.linearForwardTimes φ y)) •
    (LinearMap.toContinuousLinearMap φ.negativeCoord).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (φ.toChart ∘ hX.flow (Classical.epsilon (· ∈ hX.linearForwardTimes φ y))) y)

/-- The **unstable frame** of the unstable manifold of the centre of the Morse chart `φ` at a point
`y`: it sends `c` to the vector whose image under the derivative of `φ ∘ Φ_{-T}` at `y` is `e^{-T}`
times the vector with coordinates `c` in the directions of negative weight and `0` elsewhere, for a
time `T` of linear backward flow of `y`. When `X` is linear in `φ`, this does not depend on `T`
(`TauCeti.IsAdaptedPseudoGradient.mfderiv_unstableFrame`); it is meaningful for the points of
`W^u(x)`, which have such times. -/
noncomputable def unstableFrame (y : M) :
    ({i // φ.weight i < 0} → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, E) y :=
  Real.exp (-Classical.epsilon (· ∈ hX.linearBackwardTimes φ y)) •
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (φ.toChart ∘ hX.flow (-Classical.epsilon (· ∈ hX.linearBackwardTimes φ y))) y).inverse.comp
      (LinearMap.toContinuousLinearMap φ.negativeExtend)

variable {hX φ}

/-- In the chart `φ` composed with the time-`T` map of the flow, the derivative at a point whose
orbit lies in the chart at time `T` is invertible. -/
theorem isInvertible_mfderiv_toChart_comp_flow {y : M} {T : ℝ}
    (hT : hX.flow T y ∈ φ.toChart.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y).IsInvertible := by
  have hq := (hX.flowDiffeomorph T).transOpenPartialHomeomorph_mem_maximalAtlas φ.mem_maximalAtlas
  have hcoe : ((hX.flowDiffeomorph T).toHomeomorph.transOpenPartialHomeomorph φ.toChart :
      M → E) = φ.toChart ∘ hX.flow T := by
    funext z
    simp
  rw [← hcoe]
  exact isInvertible_mfderiv_chart (IsManifold.maximalAtlas_subset_of_le (by simp) hq)
    (by simpa using hT)

/-- The times of linear forward flow of `Φ_t y` are those of `y`, shifted by `-t`. -/
theorem mem_linearForwardTimes_flow {y : M} {t T : ℝ} :
    T ∈ hX.linearForwardTimes φ (hX.flow t y) ↔ T + t ∈ hX.linearForwardTimes φ y := by
  simp only [mem_linearForwardTimes, ← Flow.map_add]

/-- The times of linear backward flow of `Φ_t y` are those of `y`, shifted by `t`. -/
theorem mem_linearBackwardTimes_flow {y : M} {t T : ℝ} :
    T ∈ hX.linearBackwardTimes φ (hX.flow t y) ↔ T - t ∈ hX.linearBackwardTimes φ y := by
  simp only [mem_linearBackwardTimes, ← Flow.map_add, show -(T - t) = -T + t by ring]

/-- The chain rule for the chart `φ` composed with the time-`s` map of the flow, after the
time-`t` map. -/
private theorem mfderiv_toChart_comp_flow_mfderiv_flow {y : M} {s t : ℝ}
    (hs : hX.flow (s + t) y ∈ φ.toChart.source) (w : TangentSpace 𝓘(ℝ, E) y) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow s) (hX.flow t y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y w) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (s + t)) y w := by
  have hd (t : ℝ) (z : M) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) z :=
    (hX.contMDiff_flow_apply t).mdifferentiable (by simp) z
  have hcomp : φ.toChart ∘ hX.flow (s + t) = (φ.toChart ∘ hX.flow s) ∘ hX.flow t := by
    funext z
    simp [Flow.map_add]
  rw [Flow.map_add] at hs
  rw [hcomp, mfderiv_comp_apply y ((φ.mdifferentiableAt_toChart hs).comp _ (hd s _)) (hd t y)]

variable (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
  fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- **The derivative of the flow along a linear stretch.** If the orbit of `y` lies in the Morse
chart `φ` at time `T` and its linear orbit stays in the chart for the times between `0` and `s`,
then waiting for the further time `s` applies the linear flow to the coordinates of the derivative
of `φ ∘ Φ_T`. -/
theorem coord_mfderiv_toChart_comp_flow_add {y : M} {T s : ℝ}
    (hT : hX.flow T y ∈ φ.toChart.source)
    (hs : ∀ t ∈ uIcc 0 s, φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈
      φ.toChart.target) (w : TangentSpace 𝓘(ℝ, E) y) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (s + T)) y w) =
      φ.linearFlow s (φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y w)) := by
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ hs
  rw [φ.toChart_symm_coord_symm_coord hT] at hflow
  have hsrc : hX.flow (s + T) y ∈ φ.toChart.source := by
    rw [Flow.map_add]
    exact hflow ▸ φ.toChart.map_target (hs s right_mem_uIcc)
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) y :=
    (hX.contMDiff_flow_apply T).mdifferentiable (by simp) y
  rw [← mfderiv_toChart_comp_flow_mfderiv_flow hsrc, hX.coord_mfderiv_toChart_comp_flow φ hφ hT hs,
    mfderiv_comp_apply y (φ.mdifferentiableAt_toChart hT) hd]

/-- The times of linear forward flow are closed under waiting, and along the wait the coordinates
of the orbit follow the linear flow. -/
theorem add_mem_linearForwardTimes {y : M} {T s : ℝ} (hT : T ∈ hX.linearForwardTimes φ y)
    (hs : 0 ≤ s) :
    s + T ∈ hX.linearForwardTimes φ y ∧
      φ.coord (φ.toChart (hX.flow (s + T) y)) =
        φ.linearFlow s (φ.coord (φ.toChart (hX.flow T y))) := by
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ (t := s) fun t ht ↦
    hT.2 t (by rw [uIcc_of_le hs] at ht; exact ht.1)
  rw [φ.toChart_symm_coord_symm_coord hT.1, ← Flow.map_add] at hflow
  have hcoord : φ.coord (φ.toChart (hX.flow (s + T) y)) =
      φ.linearFlow s (φ.coord (φ.toChart (hX.flow T y))) := by
    rw [hflow, φ.toChart.right_inv (hT.2 s hs), LinearEquiv.apply_symm_apply]
  refine ⟨⟨hflow ▸ φ.toChart.map_target (hT.2 s hs), fun t ht ↦ ?_⟩, hcoord⟩
  rw [hcoord, ← φ.linearFlow_add]
  exact hT.2 _ (by linarith)

/-- The times of linear backward flow are closed under waiting, and along the wait the
coordinates of the orbit follow the linear flow backwards. -/
theorem add_mem_linearBackwardTimes {y : M} {T s : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y)
    (hs : 0 ≤ s) :
    T + s ∈ hX.linearBackwardTimes φ y ∧
      φ.coord (φ.toChart (hX.flow (-(T + s)) y)) =
        φ.linearFlow (-s) (φ.coord (φ.toChart (hX.flow (-T) y))) := by
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ (t := -s) fun t ht ↦
    hT.2 t (by rw [uIcc_of_ge (by linarith)] at ht; exact ht.2)
  rw [φ.toChart_symm_coord_symm_coord hT.1, ← Flow.map_add, ← neg_add, add_comm s] at hflow
  have hcoord : φ.coord (φ.toChart (hX.flow (-(T + s)) y)) =
      φ.linearFlow (-s) (φ.coord (φ.toChart (hX.flow (-T) y))) := by
    rw [hflow, φ.toChart.right_inv (hT.2 (-s) (by linarith)), LinearEquiv.apply_symm_apply]
  refine ⟨⟨hflow ▸ φ.toChart.map_target (hT.2 (-s) (by linarith)), fun t ht ↦ ?_⟩, hcoord⟩
  rw [hcoord, ← φ.linearFlow_add]
  exact hT.2 _ (by linarith)

/-! ### The normal coordinates of the stable manifold -/

/-- Near `x`, the orbit of a point of `W^s(x)` eventually enters the part of the Morse chart where
the flow stays linear: all large times are times of linear forward flow. -/
theorem eventually_mem_linearForwardTimes {y : M}
    (hy : y ∈ hX.flow.stableSet x) : ∀ᶠ T in atTop, T ∈ hX.linearForwardTimes φ y := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have hc : ContinuousAt (fun z ↦ ‖φ.coord (φ.toChart z)‖) x :=
    φ.continuous_coord.norm.continuousAt.comp (φ.toChart.continuousAt φ.mem_source)
  have hnear : ∀ᶠ z in 𝓝 x, z ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart z)‖ < min ε r :=
    (φ.toChart.open_source.eventually_mem φ.mem_source).and
      (hc.eventually (gt_mem_nhds (by simp [hε, hr])))
  filter_upwards [(Flow.mem_stableSet.1 hy).eventually hnear] with T hT
  -- The coordinates of negative weight vanish on the local stable set, so the linear forward
  -- orbit is the contraction `e^{-t} c`.
  have hu := (hloc _ hT.1 (hT.2.trans_le (min_le_left _ _))).1
    ((Flow.apply_mem_stableSet_iff hX.flow T).2 hy)
  set c := φ.coord (φ.toChart (hX.flow T y))
  refine ⟨hT.1, fun t ht ↦ hrT _ ?_⟩
  have hlin : φ.linearFlow t c = Real.exp (-t) • c := by
    funext i
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · rw [φ.linearFlow_of_weight_eq_neg_one hi, Pi.smul_apply, hu i (by rw [hi]; norm_num),
        mul_zero, smul_zero]
    · rw [φ.linearFlow_of_weight_eq_one hi, Pi.smul_apply, smul_eq_mul]
  rw [hlin, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-t) * ‖c‖ ≤ ‖c‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))
    _ < r := hT.2.trans_le (min_le_right _ _)

/-- Waiting for a time `s ≥ 0` multiplies the coordinates of negative weight of the derivative
of `φ ∘ Φ_T` by `e^{s}`, so `e^{-T}` times these coordinates does not change. -/
private theorem exp_smul_negativeCoord_mfderiv_add {y : M} {T s : ℝ}
    (hT : T ∈ hX.linearForwardTimes φ y) (hs : 0 ≤ s) (w : TangentSpace 𝓘(ℝ, E) y) :
    Real.exp (-(s + T)) •
        φ.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (s + T)) y w) =
      Real.exp (-T) • φ.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y w) := by
  have h := hX.coord_mfderiv_toChart_comp_flow_add hφ hT.1
    (fun t ht ↦ hT.2 t (by rw [uIcc_of_le hs] at ht; exact ht.1)) w
  rw [φ.negativeCoord_eq_exp_smul_of_coord_eq h, smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- **The normal coordinates at an admissible time.** For every time `T` of linear forward flow of
`y`, the normal coordinates of the stable manifold at `y` are `e^{-T}` times the coordinates of
negative weight of the derivative of `φ ∘ Φ_T` at `y`. -/
theorem stableNormal_apply {y : M} {T : ℝ} (hT : T ∈ hX.linearForwardTimes φ y)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    hX.stableNormal φ y w =
      Real.exp (-T) • φ.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y w) := by
  set T₀ := Classical.epsilon (· ∈ hX.linearForwardTimes φ y)
  have hT₀ : T₀ ∈ hX.linearForwardTimes φ y := Classical.epsilon_spec ⟨T, hT⟩
  -- Both values agree with the value at the later time `max T₀ T`.
  have h₀ := exp_smul_negativeCoord_mfderiv_add hφ hT₀ (sub_nonneg.2 (le_max_left T₀ T)) w
  have h₁ := exp_smul_negativeCoord_mfderiv_add hφ hT (sub_nonneg.2 (le_max_right T₀ T)) w
  rw [sub_add_cancel] at h₀ h₁
  exact h₀.symm.trans h₁

/-- **The tangent space of the stable manifold, read along the flow.** At a point `y` of `W^s(x)`,
for all large times `T`, the span of the tangent cone of `W^s(x)` at `y` is the preimage of the
stable subspace of `φ` under the derivative of `φ ∘ Φ_T` at `y`. -/
theorem eventually_span_mtangentConeAt_stableSet_eq_comap {y : M}
    (hy : y ∈ hX.flow.stableSet x) :
    ∀ᶠ T in atTop, Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet x) y) =
      φ.stableSubspace.comap (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y).toLinearMap := by
  obtain ⟨D, hD, hxD, hDs, hslice⟩ := hX.exists_isSliceChart_stableSet_flow φ hφ
  filter_upwards [(Flow.mem_stableSet.1 hy).eventually (hD.mem_nhds hxD)] with T hTD
  -- `φ ∘ Φ_T`, restricted to the preimage of `D`, is a slice chart of `W^s(x)` at `y`.
  set q := (hX.flowDiffeomorph T).toHomeomorph.transOpenPartialHomeomorph (φ.toChart.restr D)
  have hq : q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    (hX.flowDiffeomorph T).transOpenPartialHomeomorph_mem_maximalAtlas
      (restr_mem_maximalAtlas _ φ.mem_maximalAtlas hD)
  have hyq : y ∈ q.source := by simpa [q, hD.interior_eq] using ⟨hDs hTD, hTD⟩
  have hqf : (q : M → E) = φ.toChart ∘ hX.flow T := by
    funext z
    simp [q]
  rw [(hslice T).span_mtangentConeAt_eq_comap (by simp) hq
    φ.stableSubspace.isClosed_of_finiteDimensional hyq hy, hqf]

/-- **The normal coordinates vanish exactly on the tangent space of the stable manifold.** At a
point `y` of `W^s(x)`, the normal coordinates of a tangent vector vanish exactly when it lies in
the span of the tangent cone of `W^s(x)` at `y`. -/
theorem stableNormal_eq_zero_iff {y : M}
    (hy : y ∈ hX.flow.stableSet x) (v : TangentSpace 𝓘(ℝ, E) y) :
    hX.stableNormal φ y v = 0 ↔
      v ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet x) y) := by
  obtain ⟨T, hT, hspan⟩ := ((hX.eventually_mem_linearForwardTimes hφ hy).and
    (eventually_span_mtangentConeAt_stableSet_eq_comap hφ hy)).exists
  rw [hspan, stableNormal_apply hφ hT, smul_eq_zero_iff_right (Real.exp_ne_zero _)]
  -- Membership in the preimage `Submodule.comap` is membership of the image.
  exact φ.mem_stableSubspace_iff_negativeCoord_eq_zero.symm

/-- **The normal coordinates are onto.** -/
theorem surjective_stableNormal {y : M} {T : ℝ} (hT : T ∈ hX.linearForwardTimes φ y) :
    Surjective (hX.stableNormal φ y) := by
  intro c
  have hD := (isInvertible_mfderiv_toChart_comp_flow hT.1).self_apply_inverse
    (φ.negativeExtend (Real.exp T • c) : TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow T) y))
  refine ⟨(mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y).inverse
    (φ.negativeExtend (Real.exp T • c)), ?_⟩
  rw [stableNormal_apply hφ hT, hD, φ.negativeCoord_negativeExtend, smul_smul, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_smul]

/-- **The normal coordinates along the flow.** Moving a point of `W^s(x)` by the time-`t` map of
the flow multiplies its normal coordinates by `e^{t}`: the normal coordinates at `Φ_t y` of the
image of `w` under the derivative of `Φ_t` are `e^{t}` times the normal coordinates of `w` at
`y`. -/
theorem stableNormal_mfderiv_flow {y : M} {T : ℝ} (hT : T ∈ hX.linearForwardTimes φ y) (t : ℝ)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    hX.stableNormal φ (hX.flow t y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y w) =
      Real.exp t • hX.stableNormal φ y w := by
  have hT' : T - t ∈ hX.linearForwardTimes φ (hX.flow t y) := by
    rw [mem_linearForwardTimes_flow, sub_add_cancel]
    exact hT
  have hsrc : hX.flow (T - t + t) y ∈ φ.toChart.source := by
    rw [sub_add_cancel]
    exact hT.1
  rw [stableNormal_apply hφ hT', mfderiv_toChart_comp_flow_mfderiv_flow hsrc, sub_add_cancel,
    stableNormal_apply hφ hT, smul_smul, ← Real.exp_add]
  congr 2
  ring

/-! ### The frame of the unstable manifold -/

omit hφ in
/-- The times of linear forward flow of `-X` in the negated Morse chart are the times of linear
backward flow of `X`. -/
theorem neg_linearForwardTimes (hf : IsMorse 𝓘(ℝ, E) f)
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) (y : M) :
    (hX.neg hf).linearForwardTimes (φ.neg h) y = hX.linearBackwardTimes φ y := by
  ext T
  simp only [linearForwardTimes, linearBackwardTimes, mem_ofPred_eq, hX.neg_flow hf,
    Flow.reverse_apply, MorseChart.neg_toChart, MorseChart.neg_coord, φ.neg_linearFlow h]
  refine and_congr_right fun _ ↦ ⟨fun h t ht ↦ ?_, fun h t ht ↦ h _ (by linarith)⟩
  simpa using h (-t) (by linarith)

/-- The orbit of a point of `W^u(x)` eventually enters, backwards in time, the part of the Morse
chart where the backward flow stays linear: all large times are times of linear backward flow. -/
theorem eventually_mem_linearBackwardTimes (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) : ∀ᶠ T in atTop, T ∈ hX.linearBackwardTimes φ y := by
  have h := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX.mfderiv_eq_zero_of_mem_unstableSet hy)
  rw [hX.unstableSet_eq_stableSet_neg hf] at hy
  simpa only [neg_linearForwardTimes (hX := hX) hf h] using
    (hX.neg hf).eventually_mem_linearForwardTimes (φ.coord_mfderiv_neg hφ h) hy

/-- Waiting for a further time `s ≥ 0` backwards multiplies a vector of negative weight in the
derivative of `φ ∘ Φ_{-T}` by `e^{-s}`. -/
private theorem mfderiv_toChart_comp_flow_neg_add {y : M} {T s : ℝ}
    (hT : T ∈ hX.linearBackwardTimes φ y) (hs : 0 ≤ s) {w : TangentSpace 𝓘(ℝ, E) y}
    {c : {i // φ.weight i < 0} → ℝ}
    (hw : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y w =
      Real.exp (-T) • φ.negativeExtend c) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-(T + s))) y w =
      Real.exp (-(T + s)) • φ.negativeExtend c := by
  have h := hX.coord_mfderiv_toChart_comp_flow_add hφ (T := -T) (s := -s) hT.1
    (fun t ht ↦ hT.2 t (by rw [uIcc_of_ge (by linarith)] at ht; exact ht.2)) w
  rw [show -s + -T = -(T + s) by ring, hw, map_smul, φ.linearFlow_smul,
    φ.linearFlow_neg_coord_negativeExtend, smul_smul, ← Real.exp_add, ← map_smul] at h
  refine φ.coord.injective (h.trans ?_)
  congr 3
  ring

/-- **The unstable frame at an admissible time.** For every time `T` of linear backward flow of
`y`, the derivative of `φ ∘ Φ_{-T}` at `y` sends the unstable frame on `c` to `e^{-T}` times the
vector with coordinates `c` in the directions of negative weight and `0` elsewhere. -/
theorem mfderiv_unstableFrame {y : M} {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y)
    (c : {i // φ.weight i < 0} → ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y (hX.unstableFrame φ y c) =
      Real.exp (-T) • φ.negativeExtend c := by
  set T₀ := Classical.epsilon (· ∈ hX.linearBackwardTimes φ y)
  have hT₀ : T₀ ∈ hX.linearBackwardTimes φ y := Classical.epsilon_spec ⟨T, hT⟩
  have h₀ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T₀)) y (hX.unstableFrame φ y c) =
      Real.exp (-T₀) • φ.negativeExtend c := by
    have hD := (isInvertible_mfderiv_toChart_comp_flow hT₀.1).self_apply_inverse
      (φ.negativeExtend c : TangentSpace 𝓘(ℝ, E) ((φ.toChart ∘ hX.flow (-T₀)) y))
    simp only [unstableFrame, smul_apply, ContinuousLinearMap.comp_apply, map_smul]
    exact congrArg _ hD
  -- Compare the frame with the vector `w` given by the formula at `T`, at the later time
  -- `max T₀ T`, where the derivative of `φ ∘ Φ_{-max T₀ T}` is injective.
  have hinv := isInvertible_mfderiv_toChart_comp_flow hT.1
  set w := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y).inverse
    (Real.exp (-T) • φ.negativeExtend c)
  have hw : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y w =
      Real.exp (-T) • φ.negativeExtend c := hinv.self_apply_inverse _
  have hs : 0 ≤ max T₀ T - T := sub_nonneg.2 (le_max_right T₀ T)
  have h₁ := mfderiv_toChart_comp_flow_neg_add hφ hT₀ (sub_nonneg.2 (le_max_left T₀ T)) h₀
  have h₂ := mfderiv_toChart_comp_flow_neg_add hφ hT hs hw
  rw [add_sub_cancel] at h₁ h₂
  have hinv₁ := isInvertible_mfderiv_toChart_comp_flow
    (add_mem_linearBackwardTimes hφ hT hs).1.1
  rw [add_sub_cancel] at hinv₁
  rw [hinv₁.injective (h₁.trans h₂.symm), hw]

/-- **The unstable frame is injective.** -/
theorem injective_unstableFrame {y : M} {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) :
    Injective (hX.unstableFrame φ y) := by
  intro c c' hcc'
  have h := congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y) hcc'
  rw [mfderiv_unstableFrame hφ hT, mfderiv_unstableFrame hφ hT] at h
  exact φ.injective_negativeExtend (smul_right_injective E (Real.exp_ne_zero _) h)

/-- **The unstable frame along the flow.** Moving a point of `W^u(x)` by the time-`t` map of the
flow carries the unstable frame to `e^{t}` times the unstable frame: the unstable frame at `Φ_t y`
is `e^{-t}` times the derivative of `Φ_t` applied to the unstable frame at `y`. -/
theorem unstableFrame_flow {y : M} {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) (t : ℝ)
    (c : {i // φ.weight i < 0} → ℝ) :
    hX.unstableFrame φ (hX.flow t y) c =
      Real.exp (-t) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y (hX.unstableFrame φ y c) := by
  have hT' : T + t ∈ hX.linearBackwardTimes φ (hX.flow t y) := by
    rw [mem_linearBackwardTimes_flow, add_sub_cancel_right]
    exact hT
  have hsrc : hX.flow (-(T + t) + t) y ∈ φ.toChart.source := by
    rw [show -(T + t) + t = -T by ring]
    exact hT.1
  refine (isInvertible_mfderiv_toChart_comp_flow hT'.1).injective ?_
  rw [mfderiv_unstableFrame hφ hT', map_smul, mfderiv_toChart_comp_flow_mfderiv_flow hsrc,
    show -(T + t) + t = -T by ring, mfderiv_unstableFrame hφ hT]
  -- Both sides are vectors of the model space `E`.
  change Real.exp (-(T + t)) • φ.negativeExtend c =
    Real.exp (-t) • Real.exp (-T) • φ.negativeExtend c
  rw [smul_smul, ← Real.exp_add, show -t + -T = -(T + t) by ring]

/-- **The unstable frame spans the tangent space of the unstable manifold.** At a point `y` of
`W^u(x)`, the range of the unstable frame is the span of the tangent cone of `W^u(x)` at `y`. -/
theorem range_unstableFrame (hf : IsMorse 𝓘(ℝ, E) f) {y : M} (hy : y ∈ hX.flow.unstableSet x) :
    range (hX.unstableFrame φ y) =
      (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) : Set E) := by
  -- `W^u(x)` is the stable manifold of `x` for `-X`, read in the negated Morse chart.
  have h := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX.mfderiv_eq_zero_of_mem_unstableSet hy)
  have hφ' := φ.coord_mfderiv_neg hφ h
  rw [hX.unstableSet_eq_stableSet_neg hf] at hy ⊢
  have hev := hX.eventually_mem_linearBackwardTimes hφ hf
    ((hX.unstableSet_eq_stableSet_neg hf x).symm ▸ hy)
  obtain ⟨T, hT, hspan⟩ := (hev.and
    (eventually_span_mtangentConeAt_stableSet_eq_comap (hX := hX.neg hf) hφ' hy)).exists
  have hqf : ((φ.neg h).toChart ∘ (hX.neg hf).flow T : M → E) = φ.toChart ∘ hX.flow (-T) := by
    funext z
    simp [hX.neg_flow hf]
  rw [hspan, hqf]
  have hinv := isInvertible_mfderiv_toChart_comp_flow (hX := hX) (φ := φ) hT.1
  ext v
  rw [mem_range]
  -- Membership in the preimage `Submodule.comap` is membership of the image.
  refine Iff.trans ?_ (φ.mem_neg_stableSubspace_iff h
    (v := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y v)).symm
  constructor
  · rintro ⟨c, rfl⟩ i hi
    rw [mfderiv_unstableFrame hφ hT, map_smul, Pi.smul_apply,
      φ.coord_negativeExtend_of_not_weight_neg c hi, smul_zero]
  · intro hv
    refine ⟨Real.exp T • φ.negativeCoord
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y v), hinv.injective ?_⟩
    rw [mfderiv_unstableFrame hφ hT, map_smul, smul_smul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, one_smul]
    exact φ.negativeExtend_negativeCoord hv

end IsAdaptedPseudoGradient

end TauCeti
