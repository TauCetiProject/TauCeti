/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Derivative
public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
public import TauCeti.Geometry.Manifold.TangentCone.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Geometry.Manifold.Morse.Stable.Transversality

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

One time serves a whole neighbourhood: a point of `W^s(x)` has a neighbourhood whose points on
`W^s(x)` share a time of linear forward flow
(`TauCeti.IsAdaptedPseudoGradient.exists_eventually_mem_linearForwardTimes`), and likewise for
`W^u(x)` and backward times. With the time fixed, the frame is read in the single chart
`φ ∘ Φ_{-T}`, so it varies continuously along `W^u(x)`: for a function `g`, `C¹` at `y₀`, the
derivative of `g` along the frame, `y ↦ dg_y ∘ F_y`, a map between fixed spaces, is continuous at
`y₀` within `W^u(x)`
(`TauCeti.IsAdaptedPseudoGradient.continuousWithinAt_mvfderiv_comp_unstableFrame`).

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `linearForwardTimes`, `linearBackwardTimes`: the times at which the forward, respectively
  backward, orbit of a point has entered the part of the chart where the flow stays linear.
* `stableNormal`: the normal coordinates of the stable manifold.
* `unstableFrame`: the frame of the unstable manifold.

## Main results

* `eventually_mem_linearForwardTimes`, `eventually_mem_linearBackwardTimes`: points of the
  stable, respectively unstable, manifold have admissible times.
* `exists_eventually_mem_linearForwardTimes`, `exists_eventually_mem_linearBackwardTimes`: one
  admissible time serves all nearby points of the stable, respectively unstable, manifold.
* `stableNormal_apply`, `mfderiv_unstableFrame`: the two maps read at any admissible time.
* `zero_mem_linearForwardTimes_self`, `zero_mem_linearBackwardTimes_self`,
  `stableNormal_unstableFrame_self`: at the centre of the chart the time `0` is admissible, and the
  normal coordinates invert the unstable frame.
* `mfderiv_unstableFrame_eq_exp_smul_self`: read at an admissible time, the unstable frame is a
  positive multiple of the frame at the critical point, read in the chart.
* `eventually_span_mtangentConeAt_stableSet_eq_comap`: for all large times `T`, the tangent space
  of the stable manifold is read off the derivative of `φ ∘ Φ_T`.
* `stableNormal_eq_comp_mvfderiv`: at a time `T` of linear forward flow, the normal coordinates are
  read off the derivative of `φ ∘ Φ_T`, which is smooth (`contMDiffAt_toChart_comp_flow`).
* `stableNormal_eq_zero_iff`, `surjective_stableNormal`: the normal coordinates vanish exactly on
  the tangent space of the stable manifold, and are onto.
* `range_unstableFrame`, `injective_unstableFrame`: the frame is an isomorphism onto the tangent
  space of the unstable manifold.
* `mem_linearForwardTimes_self`, `mem_linearBackwardTimes_self`: every time is a time of linear
  flow of the centre of the chart.
* `neg_linearForwardTimes`, `neg_linearBackwardTimes`: the times of linear flow of `-X` in the
  negated Morse chart are those of `X`, in the opposite direction.
* `neg_toChart_comp_neg_flow`: the flow of `-X` read in the negated Morse chart is the flow of `X`
  read in the chart, in the opposite direction.
* `bijective_unstableFrame`: at a critical point of top index, the frame is an isomorphism onto the
  whole tangent space.
* `stableNormal_mfderiv_flow`, `unstableFrame_flow`: along the flow, the derivative of the time-`t`
  map carries the normal coordinates and the frame to positive multiples of themselves.
* `injective_unstableFrame_of_mem`, `surjective_stableNormal_of_mem`: the frame is injective and
  the normal coordinates are onto at every point of the unstable, respectively stable, manifold.
* `exact_unstableFrame_neg_stableNormal`, `exact_neg_unstableFrame_stableNormal`: the unstable
  frame of `X` and the normal coordinates of the stable manifold of `-X`, read in the negated Morse
  chart, form a short exact sequence `0 → V⁻ → T_y M → V⁺ → 0` at the points of the unstable
  manifold, and symmetrically at the points of the stable manifold.
* `coord_toChart_flow_neg_eq_zero_of_not_weight_neg`: once the backward orbit of a point of the
  unstable manifold is linear in the chart, its coordinates of positive weight vanish.
* `negativeCoord_toChart_flow_eq_zero_of_mem_stableSet`: once the forward orbit of a point of the
  stable manifold is linear in the chart, its coordinates of negative weight vanish.
* `flow_add_mem_source_of_forall_mem_uIcc`, `coord_toChart_flow_add`: along a linear stretch of an
  orbit in the chart, the orbit stays in the chart and its coordinates follow the linear flow.
* `unstableFrame_exp_smul_negativeCoord`: the frame sends the direction in which a trajectory leaves
  the critical point to its velocity.
* `negativeCoord_toChart_flow_neg_ne_zero`: that direction is nonzero away from the critical point.
* `flow_log_eq_of_exp_smul_negativeCoord_eq`: two points of the unstable manifold whose directions
  are positive multiples of each other lie on the same orbit.
* `eventually_mem_unstableSet_and_unstableFrame_eq`: on the unstable axis of a Morse chart, the
  unstable frame of the coordinates is the velocity.
* `eventually_mem_unstableSet_and_unstableFrame_eq_and_neg`: the same at `c` and at `-c`.
* `mvfderiv_comp_unstableFrame_eq`: the derivative of a function along the unstable frame, read in
  the chart `φ ∘ Φ_{-T}` at a time `T` of linear backward flow.
* `contDiffAt_comp_symm_transOpenPartialHomeomorph`: a `C¹` function read in the chart
  `φ ∘ Φ_{-T}` is `C¹`.
* `continuousWithinAt_mvfderiv_comp_unstableFrame`: the derivative of a `C¹` function along the
  unstable frame is continuous along the unstable manifold.
* `stableNormal_comp_unstableFrame_flow`: the normal coordinates of `W^s(q)` along the unstable
  frame of `W^u(p)` are invariant under the flow.

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
  have hq := (hX.flowDiffeomorph T).transOpenPartialHomeomorph_mem_maximalAtlas le_rfl
    φ.mem_maximalAtlas
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

/-- At its critical point, the centre of the Morse chart has linear forward flow at every
time. -/
theorem mem_linearForwardTimes_self (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (T : ℝ) :
    T ∈ hX.linearForwardTimes φ x := by
  refine (mem_linearForwardTimes hX φ).2
    ⟨by rw [hX.flow_apply_of_mfderiv_eq_zero hx]; exact φ.mem_source, fun t _ ↦ ?_⟩
  rw [hX.flow_apply_of_mfderiv_eq_zero hx, φ.apply_self, map_zero, φ.linearFlow_zero_right,
    map_zero, ← φ.apply_self]
  exact φ.toChart.map_source φ.mem_source

/-- At its critical point, the centre of the Morse chart has linear backward flow at every
time. -/
theorem mem_linearBackwardTimes_self (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (T : ℝ) :
    T ∈ hX.linearBackwardTimes φ x := by
  refine (mem_linearBackwardTimes hX φ).2
    ⟨by rw [hX.flow_apply_of_mfderiv_eq_zero hx]; exact φ.mem_source, fun t _ ↦ ?_⟩
  rw [hX.flow_apply_of_mfderiv_eq_zero hx, φ.apply_self, map_zero, φ.linearFlow_zero_right,
    map_zero, ← φ.apply_self]
  exact φ.toChart.map_source φ.mem_source

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

/-- The linear forward orbit of the centre of a Morse chart is the centre, so `0` is a time of
linear forward flow of the centre. -/
theorem zero_mem_linearForwardTimes_self : (0 : ℝ) ∈ hX.linearForwardTimes φ x := by
  refine (hX.mem_linearForwardTimes φ).2 ⟨by simp, fun t _ ↦ ?_⟩
  have h0 : φ.linearFlow t 0 = 0 := funext fun i ↦ by simp
  rw [Flow.map_zero_apply, φ.apply_self, map_zero, h0, map_zero, ← φ.apply_self]
  exact φ.toChart.map_source φ.mem_source

/-- The linear backward orbit of the centre of a Morse chart is the centre, so `0` is a time of
linear backward flow of the centre. -/
theorem zero_mem_linearBackwardTimes_self : (0 : ℝ) ∈ hX.linearBackwardTimes φ x := by
  refine (hX.mem_linearBackwardTimes φ).2 ⟨by simp, fun t _ ↦ ?_⟩
  have h0 : φ.linearFlow t 0 = 0 := funext fun i ↦ by simp
  rw [neg_zero, Flow.map_zero_apply, φ.apply_self, map_zero, h0, map_zero, ← φ.apply_self]
  exact φ.toChart.map_source φ.mem_source

variable (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
  fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- Along a linear stretch of an orbit in the Morse chart `φ`, the orbit stays in the source of the
chart: if `Φ_T y` lies in the chart and its linear orbit stays in the chart for the times between
`0` and `s`, then `Φ_{s + T} y` lies in the source of the chart. -/
theorem flow_add_mem_source_of_forall_mem_uIcc {y : M} {T s : ℝ}
    (hT : hX.flow T y ∈ φ.toChart.source)
    (hs : ∀ t ∈ uIcc 0 s, φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈
      φ.toChart.target) :
    hX.flow (s + T) y ∈ φ.toChart.source := by
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ hs
  rw [φ.toChart_symm_coord_symm_coord hT, ← Flow.map_add] at hflow
  exact hflow ▸ φ.toChart.map_target (hs s right_mem_uIcc)

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
  have hsrc := flow_add_mem_source_of_forall_mem_uIcc hφ hT hs
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) y :=
    (hX.contMDiff_flow_apply T).mdifferentiable (by simp) y
  rw [← mfderiv_toChart_comp_flow_mfderiv_flow hsrc, hX.coord_mfderiv_toChart_comp_flow φ hφ hT hs,
    mfderiv_comp_apply y (φ.mdifferentiableAt_toChart hT) hd]

/-- **The flow along a linear stretch.** If the orbit of `y` lies in the Morse chart `φ` at time
`T` and its linear orbit stays in the chart for the times between `0` and `s`, then the coordinates
of `Φ_{s + T} y` are those of `Φ_T y` moved by the linear flow for the time `s`. -/
theorem coord_toChart_flow_add {y : M} {T s : ℝ} (hT : hX.flow T y ∈ φ.toChart.source)
    (hs : ∀ t ∈ uIcc 0 s, φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈
      φ.toChart.target) :
    φ.coord (φ.toChart (hX.flow (s + T) y)) =
      φ.linearFlow s (φ.coord (φ.toChart (hX.flow T y))) := by
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ hs
  rw [φ.toChart_symm_coord_symm_coord hT, ← Flow.map_add] at hflow
  rw [hflow, φ.toChart.right_inv (hs s right_mem_uIcc), LinearEquiv.apply_symm_apply]

/-- The times of linear forward flow are closed under waiting, and along the wait the coordinates
of the orbit follow the linear flow. -/
theorem add_mem_linearForwardTimes {y : M} {T s : ℝ} (hT : T ∈ hX.linearForwardTimes φ y)
    (hs : 0 ≤ s) :
    s + T ∈ hX.linearForwardTimes φ y ∧
      φ.coord (φ.toChart (hX.flow (s + T) y)) =
        φ.linearFlow s (φ.coord (φ.toChart (hX.flow T y))) := by
  have hs' : ∀ t ∈ uIcc 0 s, φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart (hX.flow T y)))) ∈
      φ.toChart.target := fun t ht ↦ hT.2 t (by rw [uIcc_of_le hs] at ht; exact ht.1)
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ hs'
  rw [φ.toChart_symm_coord_symm_coord hT.1, ← Flow.map_add] at hflow
  have hcoord := coord_toChart_flow_add hφ hT.1 hs'
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
  have hs' : ∀ t ∈ uIcc 0 (-s), φ.coord.symm (φ.linearFlow t (φ.coord (φ.toChart
      (hX.flow (-T) y)))) ∈ φ.toChart.target := fun t ht ↦
    hT.2 t (by rw [uIcc_of_ge (by linarith)] at ht; exact ht.2)
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ hs'
  rw [φ.toChart_symm_coord_symm_coord hT.1, ← Flow.map_add, ← neg_add, add_comm s] at hflow
  have hcoord : φ.coord (φ.toChart (hX.flow (-(T + s)) y)) =
      φ.linearFlow (-s) (φ.coord (φ.toChart (hX.flow (-T) y))) := by
    rw [neg_add_rev]
    exact coord_toChart_flow_add hφ hT.1 hs'
  refine ⟨⟨hflow ▸ φ.toChart.map_target (hT.2 (-s) (by linarith)), fun t ht ↦ ?_⟩, hcoord⟩
  rw [hcoord, ← φ.linearFlow_add]
  exact hT.2 _ (by linarith)

/-- **Points of the stable manifold have no coordinates of negative weight along their linear
forward orbits.** If `T` is a time of linear forward flow of a point `y` of `W^s(x)`, then the
coordinates of negative weight of `Φ_T y` vanish: waiting for the time `s` multiplies them by
`e^{s}`, whereas the orbit tends to the centre of the chart. This is the forward counterpart of
`TauCeti.IsAdaptedPseudoGradient.coord_toChart_flow_neg_eq_zero_of_not_weight_neg`. -/
theorem negativeCoord_toChart_flow_eq_zero_of_mem_stableSet {y : M}
    (hy : y ∈ hX.flow.stableSet x) {T : ℝ} (hT : T ∈ hX.linearForwardTimes φ y) :
    φ.negativeCoord (φ.toChart (hX.flow T y)) = 0 := by
  set v := φ.negativeCoord (φ.toChart (hX.flow T y))
  have hlin : ∀ s, 0 ≤ s → φ.negativeCoord (φ.toChart (hX.flow (s + T) y)) = Real.exp s • v :=
    fun s hs ↦ φ.negativeCoord_eq_exp_smul_of_coord_eq (add_mem_linearForwardTimes hφ hT hs).2
  -- The orbit tends to `x`, where the chart vanishes.
  have hlim : Tendsto (fun s ↦ φ.negativeCoord (φ.toChart (hX.flow (s + T) y))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun s ↦ hX.flow (s + T) y) atTop (𝓝 x) :=
      (Flow.mem_stableSet.1 hy).comp (tendsto_atTop_add_const_right atTop T tendsto_id)
    have h₂ := (φ.negativeCoord.continuous_of_finiteDimensional.tendsto _).comp
      ((φ.toChart.continuousAt φ.mem_source).tendsto.comp h₁)
    rwa [φ.apply_self, map_zero] at h₂
  have hnorm : Tendsto (fun s ↦ ‖Real.exp s • v‖) atTop (𝓝 0) := by
    simpa using (hlim.congr' ((eventually_ge_atTop 0).mono hlin)).norm
  -- But `‖e^{s} v‖ ≥ ‖v‖` for `s ≥ 0`.
  refine norm_le_zero_iff.1 (le_of_tendsto_of_tendsto tendsto_const_nhds hnorm ?_)
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos s).le]
  exact le_mul_of_one_le_left (norm_nonneg v) (Real.one_le_exp hs)

/-! ### The normal coordinates of the stable manifold -/

/-- Near the centre of the Morse chart, the points of `W^s(x)` already lie in the part of the chart
where the forward flow stays linear: there is an open neighbourhood `S` of `x` such that `0` is a
time of linear forward flow of every point of `S` on `W^s(x)`. -/
theorem exists_isOpen_forall_zero_mem_linearForwardTimes :
    ∃ S : Set M, IsOpen S ∧ x ∈ S ∧
      ∀ z ∈ S, z ∈ hX.flow.stableSet x → 0 ∈ hX.linearForwardTimes φ z := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨r, hr, hrT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  refine ⟨φ.toChart.source ∩ (fun z ↦ ‖φ.coord (φ.toChart z)‖) ⁻¹' Iio (min ε r),
    (φ.continuous_coord.norm.comp_continuousOn φ.toChart.continuousOn).isOpen_inter_preimage
      φ.toChart.open_source isOpen_Iio, ⟨φ.mem_source, by simp [hε, hr]⟩, fun z hz hzs ↦ ?_⟩
  have hzc : ‖φ.coord (φ.toChart z)‖ < min ε r := hz.2
  -- The coordinates of negative weight vanish on the local stable set, so the linear forward
  -- orbit is the contraction `e^{-t} c`.
  have hu := (hloc z hz.1 (hzc.trans_le (min_le_left _ _))).1 hzs
  rw [mem_linearForwardTimes, Flow.map_zero_apply]
  set c := φ.coord (φ.toChart z)
  refine ⟨hz.1, fun t ht ↦ hrT _ ?_⟩
  have hlin : φ.linearFlow t c = Real.exp (-t) • c := by
    funext i
    rcases φ.weight_eq_neg_one_or_eq_one i with hi | hi
    · rw [φ.linearFlow_of_weight_eq_neg_one hi, Pi.smul_apply, hu i (by rw [hi]; norm_num),
        mul_zero, smul_zero]
    · rw [φ.linearFlow_of_weight_eq_one hi, Pi.smul_apply, smul_eq_mul]
  rw [hlin, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-t) * ‖c‖ ≤ ‖c‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))
    _ < r := hzc.trans_le (min_le_right _ _)

/-- Near `x`, the orbit of a point of `W^s(x)` eventually enters the part of the Morse chart where
the flow stays linear: all large times are times of linear forward flow. -/
theorem eventually_mem_linearForwardTimes {y : M}
    (hy : y ∈ hX.flow.stableSet x) : ∀ᶠ T in atTop, T ∈ hX.linearForwardTimes φ y := by
  obtain ⟨S, hS, hxS, hS0⟩ := hX.exists_isOpen_forall_zero_mem_linearForwardTimes hφ
  filter_upwards [(Flow.mem_stableSet.1 hy).eventually (hS.mem_nhds hxS)] with T hT
  simpa using mem_linearForwardTimes_flow.1
    (hS0 _ hT ((Flow.apply_mem_stableSet_iff hX.flow T).2 hy))

/-- **Uniform times of linear forward flow.** A point `y₀` of `W^s(x)` has a neighbourhood with a
common time of linear forward flow `T` for all of its points on `W^s(x)`. -/
theorem exists_eventually_mem_linearForwardTimes {y₀ : M} (hy₀ : y₀ ∈ hX.flow.stableSet x) :
    ∃ T, ∀ᶠ y in 𝓝 y₀, y ∈ hX.flow.stableSet x → T ∈ hX.linearForwardTimes φ y := by
  obtain ⟨S, hS, hxS, hS0⟩ := hX.exists_isOpen_forall_zero_mem_linearForwardTimes hφ
  obtain ⟨T, hT⟩ := ((Flow.mem_stableSet.1 hy₀).eventually (hS.mem_nhds hxS)).exists
  refine ⟨T, ?_⟩
  filter_upwards [(hX.flow.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
    (hS.mem_nhds hT)] with y hy hys
  simpa using mem_linearForwardTimes_flow.1
    (hS0 _ hy ((Flow.apply_mem_stableSet_iff hX.flow T).2 hys))

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

/-- At a time `0` of linear forward flow, the normal coordinates of the stable manifold are the
coordinates of negative weight of the derivative of the chart. -/
theorem stableNormal_apply_of_zero_mem {y : M} (hy : 0 ∈ hX.linearForwardTimes φ y)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    hX.stableNormal φ y w = φ.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w) := by
  rw [stableNormal_apply hφ hy, neg_zero, Real.exp_zero, one_smul, Flow.map_zero, comp_id]

omit hφ in
/-- If the orbit of `y` lies in the Morse chart `φ` at time `T`, the function `φ ∘ Φ_T` is smooth
at `y`. -/
theorem contMDiffAt_toChart_comp_flow {y : M} {T : ℝ} (hy : hX.flow T y ∈ φ.toChart.source) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (φ.toChart ∘ hX.flow T) y :=
  (contMDiffAt_of_mem_maximalAtlas φ.mem_maximalAtlas hy).comp _
    (hX.contMDiff_flow_apply T).contMDiffAt

/-- At a time `T` of linear forward flow, the normal coordinates of the stable manifold are
`e^{-T}` times the coordinates of negative weight of the derivative of `φ ∘ Φ_T`, as a map of the
model space. -/
theorem stableNormal_eq_comp_mvfderiv {y : M} {T : ℝ} (hT : T ∈ hX.linearForwardTimes φ y) :
    hX.stableNormal φ y = (Real.exp (-T) • LinearMap.toContinuousLinearMap φ.negativeCoord).comp
      (mvfderiv 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y) := by
  ext w : 1
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', stableNormal_apply hφ hT]
  rw [mvfderiv_apply_eq_mfderiv_apply]

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
    (hX.flowDiffeomorph T).transOpenPartialHomeomorph_mem_maximalAtlas le_rfl
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

omit hφ in
/-- The times of linear backward flow of `-X` in the negated Morse chart are the times of linear
forward flow of `X`. -/
theorem neg_linearBackwardTimes (hf : IsMorse 𝓘(ℝ, E) f)
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) (y : M) :
    (hX.neg hf).linearBackwardTimes (φ.neg h) y = hX.linearForwardTimes φ y := by
  ext T
  simp only [linearForwardTimes, linearBackwardTimes, mem_ofPred_eq, hX.neg_flow hf,
    Flow.reverse_apply, neg_neg, MorseChart.neg_toChart, MorseChart.neg_coord, φ.neg_linearFlow h]
  refine and_congr_right fun _ ↦ ⟨fun h t ht ↦ ?_, fun h t ht ↦ h _ (by linarith)⟩
  simpa using h (-t) (by linarith)

omit hφ in
/-- Read in the negated Morse chart, the time-`t` map of `-X` is the time-`-t` map of `X` read in
the Morse chart. -/
theorem neg_toChart_comp_neg_flow (hf : IsMorse 𝓘(ℝ, E) f)
    (h : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) (t : ℝ) :
    ((φ.neg h).toChart ∘ (hX.neg hf).flow t : M → E) = φ.toChart ∘ hX.flow (-t) := by
  funext z
  simp [hX.neg_flow hf]

/-- The orbit of a point of `W^u(x)` eventually enters, backwards in time, the part of the Morse
chart where the backward flow stays linear: all large times are times of linear backward flow. -/
theorem eventually_mem_linearBackwardTimes (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) : ∀ᶠ T in atTop, T ∈ hX.linearBackwardTimes φ y := by
  have h := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX.mfderiv_eq_zero_of_mem_unstableSet hy)
  rw [hX.unstableSet_eq_stableSet_neg hf] at hy
  simpa only [neg_linearForwardTimes (hX := hX) hf h] using
    (hX.neg hf).eventually_mem_linearForwardTimes (φ.coord_mfderiv_neg hφ h) hy

/-- **Uniform times of linear backward flow.** A point `y₀` of `W^u(x)` has a neighbourhood with a
common time of linear backward flow `T` for all of its points on `W^u(x)`. -/
theorem exists_eventually_mem_linearBackwardTimes (hf : IsMorse 𝓘(ℝ, E) f) {y₀ : M}
    (hy₀ : y₀ ∈ hX.flow.unstableSet x) :
    ∃ T, ∀ᶠ y in 𝓝 y₀, y ∈ hX.flow.unstableSet x → T ∈ hX.linearBackwardTimes φ y := by
  have h := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX.mfderiv_eq_zero_of_mem_unstableSet hy₀)
  rw [hX.unstableSet_eq_stableSet_neg hf] at hy₀ ⊢
  simpa only [neg_linearForwardTimes (hX := hX) hf h] using
    (hX.neg hf).exists_eventually_mem_linearForwardTimes (φ.coord_mfderiv_neg hφ h) hy₀

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
    φ.linearFlow_coord_negativeExtend, smul_smul, ← Real.exp_add, ← map_smul] at h
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

/-- **The unstable frame compared with the frame at the critical point.** For every time `T` of
linear backward flow of `y`, the derivative of `φ ∘ Φ_{-T}` at `y` sends the unstable frame at `y`
to `e^{-T}` times the image of the unstable frame at `x` under the derivative of `φ`. -/
theorem mfderiv_unstableFrame_eq_exp_smul_self (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) {y : M}
    {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) (c : {i // φ.weight i < 0} → ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y (hX.unstableFrame φ y c) =
      Real.exp (-T) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart x (hX.unstableFrame φ x c) := by
  have h0 := mfderiv_unstableFrame hφ (mem_linearBackwardTimes_self (hX := hX) hx 0) c
  rw [neg_zero, Flow.map_zero, Function.comp_id, Real.exp_zero, one_smul] at h0
  exact (mfderiv_unstableFrame hφ hT c).trans (congrArg (Real.exp (-T) • ·) h0).symm

/-- **The unstable frame is injective.** -/
theorem injective_unstableFrame {y : M} {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) :
    Injective (hX.unstableFrame φ y) := by
  intro c c' hcc'
  have h := congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow (-T)) y) hcc'
  rw [mfderiv_unstableFrame hφ hT, mfderiv_unstableFrame hφ hT] at h
  exact φ.injective_negativeExtend (smul_right_injective E (Real.exp_ne_zero _) h)

/-- **At a critical point of top index the unstable frame is an isomorphism.** If `x` has Morse
index `n = dim M`, the unstable frame at every point `y` with a time of linear backward flow is a
bijection from the coordinates of negative weight onto the tangent space at `y`. -/
theorem bijective_unstableFrame (hx : manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E)
    {y : M} {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) : Bijective (hX.unstableFrame φ y) := by
  have hinj := injective_unstableFrame hφ hT
  have hdim : Module.finrank ℝ ({i // φ.weight i < 0} → ℝ) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) y) := by
    rw [φ.finrank_negativeWeight_fun, hx]
    -- `TangentSpace 𝓘(ℝ, E) y` is definitionally `E`.
    rfl
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (hX.unstableFrame φ y).toLinearMap) hdim).1 hinj⟩

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
  rw [hspan, neg_toChart_comp_neg_flow (hX := hX) hf h]
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

/-! ### Exactness for the reversed pseudo-gradient -/

/-- **The unstable frame is injective** at every point of the unstable manifold. -/
theorem injective_unstableFrame_of_mem (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) : Injective (hX.unstableFrame φ y) := by
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ hf hy).exists
  exact hX.injective_unstableFrame hφ hT

/-- **The normal coordinates are onto** at every point of the stable manifold. -/
theorem surjective_stableNormal_of_mem {y : M} (hy : y ∈ hX.flow.stableSet x) :
    Surjective (hX.stableNormal φ y) := by
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearForwardTimes hφ hy).exists
  exact hX.surjective_stableNormal hφ hT

/-- At a point of the unstable manifold of `x`, the unstable frame of `X` and the normal
coordinates of the stable manifold of `x` for `-X`, read in the negated Morse chart, form an exact
sequence: both see the tangent space of `W^u(x)`, which is the stable manifold of `-X`. -/
theorem exact_unstableFrame_neg_stableNormal (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) :
    Exact (hX.unstableFrame φ y) ((hX.neg hf).stableNormal (φ.neg hx) y) := by
  intro v
  rw [(hX.neg hf).stableNormal_eq_zero_iff (φ.coord_mfderiv_neg hφ hx)
      (by rwa [← hX.unstableSet_eq_stableSet_neg hf]), ← hX.unstableSet_eq_stableSet_neg hf]
  exact (Set.ext_iff.1 (hX.range_unstableFrame hφ hf hy) v).symm

/-- At a point of the stable manifold of `x`, the unstable frame of `-X`, read in the negated Morse
chart, and the normal coordinates of the stable manifold of `x` for `X` form an exact sequence:
both see the tangent space of `W^s(x)`, which is the unstable manifold of `-X`. -/
theorem exact_neg_unstableFrame_stableNormal (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) {y : M}
    (hy : y ∈ hX.flow.stableSet x) :
    Exact ((hX.neg hf).unstableFrame (φ.neg hx) y) (hX.stableNormal φ y) := by
  intro v
  rw [hX.stableNormal_eq_zero_iff hφ hy, hX.stableSet_eq_unstableSet_neg hf]
  exact (Set.ext_iff.1 ((hX.neg hf).range_unstableFrame (φ.coord_mfderiv_neg hφ hx) hf.neg
    ((hX.stableSet_eq_unstableSet_neg hf x).subset hy)) v).symm

/-! ### The direction of a trajectory leaving the critical point -/

/-- At a time `T` of linear backward flow of a point `y` of `W^u(x)`, the velocity `X y` is the
unstable frame of some vector `a`, and the image of `X y` under the derivative of `φ ∘ Φ_{-T}`
has the coordinates of the linear field at `Φ_{-T} y`. -/
private theorem exists_unstableFrame_eq_and_coord (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) :
    ∃ a, hX.unstableFrame φ y a = X y ∧ ∀ i, Real.exp (-T) * φ.coord (φ.negativeExtend a) i =
      -(φ.weight i * φ.coord (φ.toChart (hX.flow (-T) y)) i) := by
  -- The velocity is tangent to the invariant set `W^u(x)`, so it lies in the range of the frame.
  have hXy : (X y : E) ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) :=
    Submodule.subset_span
      (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet x) hy)
  obtain ⟨a, ha⟩ : X y ∈ range (hX.unstableFrame φ y) := by
    rw [range_unstableFrame hφ hf hy]
    exact hXy
  refine ⟨a, ha, fun i ↦ ?_⟩
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow (-T)) y :=
    (hX.contMDiff_flow_apply (-T)).mdifferentiable (by simp) y
  have h := mfderiv_unstableFrame hφ hT a
  rw [ha, mfderiv_comp_apply y (φ.mdifferentiableAt_toChart hT.1) hd,
    hX.mfderiv_flow_apply_self] at h
  have hi := congrFun (congrArg φ.coord h) i
  rw [hφ _ hT.1, map_smul, Pi.smul_apply, smul_eq_mul] at hi
  exact hi.symm

/-- **Along the backward orbit, a point of the unstable manifold has no coordinates of positive
weight.** If `T` is a time of linear backward flow of a point `y` of `W^u(x)`, then the
coordinates of positive weight of `Φ_{-T} y` in the Morse chart vanish. -/
theorem coord_toChart_flow_neg_eq_zero_of_not_weight_neg (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y)
    {i : Fin (Module.finrank ℝ E)} (hi : ¬φ.weight i < 0) :
    φ.coord (φ.toChart (hX.flow (-T) y)) i = 0 := by
  obtain ⟨a, -, ha⟩ := exists_unstableFrame_eq_and_coord hφ hf hy hT
  have h := ha i
  rw [φ.coord_negativeExtend_of_not_weight_neg a hi, mul_zero] at h
  have hw : φ.weight i = 1 := (φ.weight_eq_neg_one_or_eq_one i).resolve_left (by
    intro h'
    rw [h'] at hi
    norm_num at hi)
  rw [hw, one_mul] at h
  linarith

/-- **The unstable frame sends the direction of a trajectory to its velocity.** Let `T` be a time
of linear backward flow of a point `y` of `W^u(x)`. The unstable frame at `y` sends `e^{T}` times
the coordinates of negative weight of `Φ_{-T} y` to the velocity `X y`. These coordinates shrink
like `e^{-T}` as `T` grows, so `e^{T}` times them is the direction in which the trajectory of `y`
leaves `x`. -/
theorem unstableFrame_exp_smul_negativeCoord (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y) :
    hX.unstableFrame φ y (Real.exp T • φ.negativeCoord (φ.toChart (hX.flow (-T) y))) = X y := by
  obtain ⟨a, ha, hcoord⟩ := exists_unstableFrame_eq_and_coord hφ hf hy hT
  -- In each direction of negative weight, of weight `-1`, the coordinates of `Φ_{-T} y` are
  -- `e^{-T}` times those of `a`.
  have he : φ.negativeCoord (φ.toChart (hX.flow (-T) y)) = Real.exp (-T) • a := by
    funext i
    have hw : φ.weight i = -1 :=
      (φ.weight_eq_neg_one_or_eq_one i).resolve_right ((φ.weight_ne_one_iff i).2 i.property)
    have h := hcoord i
    rw [φ.coord_negativeExtend_of_weight_neg a i, hw] at h
    rw [φ.negativeCoord_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  rw [he, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul, ha]

/-- **The direction in which a trajectory leaves the critical point is nonzero.** Let `T` be a
time of linear backward flow of a point `y ≠ x` of `W^u(x)`. Then the coordinates of negative
weight of `Φ_{-T} y` do not all vanish: `e^{T}` times them is sent to the velocity `X y` by the
unstable frame (`unstableFrame_exp_smul_negativeCoord`), and `X` vanishes only at the critical
points, which are rest points of the flow. -/
theorem negativeCoord_toChart_flow_neg_ne_zero (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) (hyx : y ≠ x) {T : ℝ}
    (hT : T ∈ hX.linearBackwardTimes φ y) :
    φ.negativeCoord (φ.toChart (hX.flow (-T) y)) ≠ 0 := by
  intro h
  have hX0 : X y = 0 := by
    rw [← unstableFrame_exp_smul_negativeCoord hφ hf hy hT, h, smul_zero, map_zero]
  exact hyx (hX.eq_of_mem_unstableSet_of_mfderiv_eq_zero (hX.eq_zero_iff.1 hX0) hy)

/-- **Points leaving the critical point in the same direction lie on the same trajectory.** Let
`T₁` and `T₂` be times of linear backward flow of points `y₁` and `y₂` of `W^u(x)`. If the direction
`e^{T₂}` times the coordinates of negative weight of `Φ_{-T₂} y₂` is a positive multiple `μ` of the
corresponding direction for `y₁`, then `y₂` is the image of `y₁` under the flow for the time
`log μ`. -/
theorem flow_log_eq_of_exp_smul_negativeCoord_eq (hf : IsMorse 𝓘(ℝ, E) f) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ hX.flow.unstableSet x) (hy₂ : y₂ ∈ hX.flow.unstableSet x) {T₁ T₂ : ℝ}
    (hT₁ : T₁ ∈ hX.linearBackwardTimes φ y₁) (hT₂ : T₂ ∈ hX.linearBackwardTimes φ y₂) {μ : ℝ}
    (hμ : 0 < μ)
    (h : Real.exp T₂ • φ.negativeCoord (φ.toChart (hX.flow (-T₂) y₂)) =
      μ • Real.exp T₁ • φ.negativeCoord (φ.toChart (hX.flow (-T₁) y₁))) :
    hX.flow (Real.log μ) y₁ = y₂ := by
  -- Flow both points back to the common time `S`, respectively `S + log μ`, where the linear flow
  -- has shrunk both directions to the same vector.
  set S := max T₁ (T₂ - Real.log μ)
  have hs₁ : 0 ≤ S - T₁ := sub_nonneg.2 (le_max_left _ _)
  have hs₂ : 0 ≤ S + Real.log μ - T₂ := by linarith [le_max_right T₁ (T₂ - Real.log μ)]
  -- The coordinates of a point of the unstable manifold reached by linear backward flow are
  -- those of `negativeExtend` of its coordinates of negative weight, and waiting a further time
  -- `s` scales them by `e^{-s}`.
  have hlin {y : M} (hy : y ∈ hX.flow.unstableSet x) {T s : ℝ}
      (hT : T ∈ hX.linearBackwardTimes φ y) (hcs : φ.coord (φ.toChart (hX.flow (-(T + s)) y)) =
        φ.linearFlow (-s) (φ.coord (φ.toChart (hX.flow (-T) y)))) :
      φ.toChart (hX.flow (-(T + s)) y) =
        φ.negativeExtend (Real.exp (-(T + s)) • Real.exp T •
          φ.negativeCoord (φ.toChart (hX.flow (-T) y))) := by
    set b := φ.negativeCoord (φ.toChart (hX.flow (-T) y))
    have hz : φ.toChart (hX.flow (-T) y) = φ.negativeExtend b :=
      (φ.negativeExtend_negativeCoord fun _ hi ↦
        coord_toChart_flow_neg_eq_zero_of_not_weight_neg hφ hf hy hT hi).symm
    refine φ.coord.injective ?_
    rw [hcs, hz, φ.linearFlow_coord_negativeExtend, smul_smul, map_smul, map_smul,
      ← Real.exp_add]
    congr 2
    ring
  obtain ⟨h₁, hc₁⟩ := add_mem_linearBackwardTimes hφ hT₁ hs₁
  obtain ⟨h₂, hc₂⟩ := add_mem_linearBackwardTimes hφ hT₂ hs₂
  have he₁ := hlin hy₁ hT₁ hc₁
  have he₂ := hlin hy₂ hT₂ hc₂
  rw [add_sub_cancel] at h₁ he₁
  rw [add_sub_cancel] at h₂ he₂
  have hk : Real.exp (-(S + Real.log μ)) * μ = Real.exp (-S) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log μ), Real.exp_log hμ,
      inv_mul_cancel_right₀ hμ.ne']
  -- Both points are in the chart, with the same image, so they agree.
  have heq : hX.flow (-S) y₁ = hX.flow (-(S + Real.log μ)) y₂ := by
    refine φ.toChart.injOn h₁.1 h₂.1 ?_
    rw [he₁, he₂, h]
    simp only [smul_smul]
    congr 2
    linear_combination (-Real.exp T₁) * hk
  have := congrArg (hX.flow (S + Real.log μ)) heq
  rwa [← Flow.map_add, ← Flow.map_add, add_neg_cancel, Flow.map_zero_apply,
    show S + Real.log μ + -S = Real.log μ by ring] at this

/-- **At the centre of a Morse chart, the normal coordinates invert the unstable frame.** At the
critical point `x` itself, both maps are read off the derivative of the chart: the frame sends `c`
to the vector with coordinates `c` in the directions of negative weight and `0` elsewhere, and the
normal coordinates read the coordinates of negative weight. -/
@[simp]
theorem stableNormal_unstableFrame_self (c : {i // φ.weight i < 0} → ℝ) :
    hX.stableNormal φ x (hX.unstableFrame φ x c) = c := by
  have h := hX.mfderiv_unstableFrame hφ zero_mem_linearBackwardTimes_self c
  rw [hX.stableNormal_apply hφ zero_mem_linearForwardTimes_self]
  rw [neg_zero, Flow.map_zero, comp_id, Real.exp_zero, one_smul] at h ⊢
  rw [h, φ.negativeCoord_negativeExtend]

/-- A point of the unstable axis whose linear backward orbit stays in the chart lies on the
unstable manifold: for `t ≤ 0` its flow is the linear flow, which tends to the centre. -/
private theorem toChart_symm_negativeExtend_mem_unstableSet {c : {i // φ.weight i < 0} → ℝ}
    (hmem : ∀ t ≤ 0, φ.coord.symm (φ.linearFlow t (φ.coord (φ.negativeExtend c))) ∈
      φ.toChart.target) :
    φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet x := by
  set z := φ.coord (φ.negativeExtend c)
  rw [Flow.mem_unstableSet]
  have hflow : ∀ᶠ t in atBot, φ.toChart.symm (φ.coord.symm (Real.exp t • z)) =
      hX.flow t (φ.toChart.symm (φ.negativeExtend c)) := by
    filter_upwards [eventually_le_atBot 0] with t ht
    rw [← LinearEquiv.symm_apply_apply φ.coord (φ.negativeExtend c),
      flow_toChart_symm_of_forall_mem_uIcc hX φ hφ fun s hs ↦
        hmem s (by rw [uIcc_of_ge ht] at hs; exact hs.2), φ.linearFlow_coord_negativeExtend]
  refine Tendsto.congr' hflow ?_
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp t • z) atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.smul_const z
  exact φ.tendsto_toChart_symm_coord_symm_nhds_zero.comp hexp

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

/-- **The unstable axis of a Morse chart.** Let `X` be linear in the Morse chart `φ` at `x`. For
every small `c` in the space of coordinates of negative weight, the point `y` of the chart whose
coordinates are `c` in the directions of negative weight and `0` elsewhere lies on the unstable
manifold of `x`, and the unstable frame at `y` sends `c` to the velocity `X y`. -/
theorem eventually_mem_unstableSet_and_unstableFrame_eq :
    ∀ᶠ c in 𝓝 (0 : {i // φ.weight i < 0} → ℝ), φ.negativeExtend c ∈ φ.toChart.target ∧
      φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet x ∧
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
    rw [φ.linearFlow_coord_negativeExtend, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ht)).trans_lt hc
  exact ⟨by simpa using hmem 0 le_rfl, toChart_symm_negativeExtend_mem_unstableSet hφ hmem,
    unstableFrame_toChart_symm_negativeExtend hφ hmem⟩

/-- **The unstable axis on both sides.** The conclusions of
`eventually_mem_unstableSet_and_unstableFrame_eq` hold at both `c` and `-c`, for every small `c`. -/
theorem eventually_mem_unstableSet_and_unstableFrame_eq_and_neg :
    ∀ᶠ c in 𝓝 (0 : {i // φ.weight i < 0} → ℝ),
      (φ.negativeExtend c ∈ φ.toChart.target ∧
        φ.toChart.symm (φ.negativeExtend c) ∈ hX.flow.unstableSet x ∧
          hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend c)) c =
            X (φ.toChart.symm (φ.negativeExtend c))) ∧
      (φ.negativeExtend (-c) ∈ φ.toChart.target ∧
        φ.toChart.symm (φ.negativeExtend (-c)) ∈ hX.flow.unstableSet x ∧
          hX.unstableFrame φ (φ.toChart.symm (φ.negativeExtend (-c))) (-c) =
            X (φ.toChart.symm (φ.negativeExtend (-c)))) :=
  have h := eventually_mem_unstableSet_and_unstableFrame_eq (hX := hX) hφ
  h.and ((continuous_neg.tendsto' 0 0 neg_zero).eventually h)

/-! ### Continuity of the frame along the unstable manifold -/

/-- **The unstable frame read in a chart.** At a point `y` with a time `T` of linear backward flow,
let `e` be the chart `φ ∘ Φ_{-T}`. The derivative at `y` of a function `g` along the unstable frame
is `e^{-T}` times the derivative of `g ∘ e⁻¹` at `e y` along the coordinates of negative weight. -/
theorem mvfderiv_comp_unstableFrame_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : M → F} {y : M} {T : ℝ} (hT : T ∈ hX.linearBackwardTimes φ y)
    (hg : DifferentiableAt ℝ
      (g ∘ ((hX.flowDiffeomorph (-T)).toHomeomorph.transOpenPartialHomeomorph φ.toChart).symm)
      (φ.toChart (hX.flow (-T) y))) :
    (mvfderiv 𝓘(ℝ, E) g y).comp (hX.unstableFrame φ y) = Real.exp (-T) •
      (fderiv ℝ (g ∘ ((hX.flowDiffeomorph (-T)).toHomeomorph.transOpenPartialHomeomorph
        φ.toChart).symm) (φ.toChart (hX.flow (-T) y))).comp
        (LinearMap.toContinuousLinearMap φ.negativeExtend) := by
  set e := (hX.flowDiffeomorph (-T)).toHomeomorph.transOpenPartialHomeomorph φ.toChart
  have hecoe : (e : M → E) = φ.toChart ∘ hX.flow (-T) := by
    funext z
    simp [e]
  have hye : y ∈ e.source := by simpa [e] using hT.1
  have hloc : g =ᶠ[𝓝 y] (g ∘ e.symm) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hye] with z hz
    simp [e.left_inv hz]
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e y := by
    rw [hecoe]
    exact (φ.mdifferentiableAt_toChart hT.1).comp _
      ((hX.contMDiff_flow_apply (-T)).mdifferentiable (by simp) y)
  have hey : e y = φ.toChart (hX.flow (-T) y) := by rw [hecoe, Function.comp_apply]
  have hg' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) (g ∘ e.symm) (e y) :=
    mdifferentiableAt_iff_differentiableAt.2 (hey ▸ hg)
  ext c : 1
  have hL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (hX.unstableFrame φ y c) =
      Real.exp (-T) • φ.negativeExtend c := by
    rw [hecoe]
    exact hX.mfderiv_unstableFrame hφ hT c
  rw [ContinuousLinearMap.comp_apply, hloc.mvfderiv_eq, mvfderiv_comp_apply y hg' hd,
    mvfderiv_eq_fderiv_apply, hL, hey]
  exact (fderiv ℝ (g ∘ e.symm) _).map_smul _ _

omit hφ in
/-- **Functions read in the chart `φ ∘ Φ_{-T}`.** If the orbit of `z` lies in the Morse chart `φ` at
time `-T`, a function `g` which is `C¹` at `z` becomes, in the chart `e = φ ∘ Φ_{-T}`, the function
`g ∘ e⁻¹` of the model space, `C¹` at `e z`. -/
theorem contDiffAt_comp_symm_transOpenPartialHomeomorph {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : M → F} {z : M} {T : ℝ} (hz : hX.flow (-T) z ∈ φ.toChart.source)
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 g z) :
    ContDiffAt ℝ 1
      (g ∘ ((hX.flowDiffeomorph (-T)).toHomeomorph.transOpenPartialHomeomorph φ.toChart).symm)
      (((hX.flowDiffeomorph (-T)).toHomeomorph.transOpenPartialHomeomorph φ.toChart) z) :=
  ContMDiffAt.contDiffAt_comp_symm_of_mem_maximalAtlas hg
    (IsManifold.maximalAtlas_subset_of_le (by norm_cast)
      ((hX.flowDiffeomorph (-T)).transOpenPartialHomeomorph_mem_maximalAtlas le_rfl
        φ.mem_maximalAtlas)) (by simpa using hz)

/-- **The unstable frame is continuous along the unstable manifold.** For a function `g` which is
`C¹` at a point `y₀` of `W^u(x)`, the derivative of `g` along the unstable frame,
`y ↦ dg_y ∘ F_y`, is continuous at `y₀` within `W^u(x)`. The frame `F_y` maps the fixed space of
coordinates of negative weight of `φ` to the tangent space at `y`, so its composite with `dg_y` is
a map between fixed spaces, and this expresses the continuity of the frame. -/
theorem continuousWithinAt_mvfderiv_comp_unstableFrame (hf : IsMorse 𝓘(ℝ, E) f) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : M → F} {y₀ : M}
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 g y₀) (hy₀ : y₀ ∈ hX.flow.unstableSet x) :
    ContinuousWithinAt (fun y ↦ (mvfderiv 𝓘(ℝ, E) g y).comp (hX.unstableFrame φ y))
      (hX.flow.unstableSet x) y₀ := by
  obtain ⟨T, hT⟩ := hX.exists_eventually_mem_linearBackwardTimes hφ hf hy₀
  set e := (hX.flowDiffeomorph (-T)).toHomeomorph.transOpenPartialHomeomorph φ.toChart
  have hecoe (z : M) : e z = φ.toChart (hX.flow (-T) z) := by simp [e]
  have hT₀ := hT.self_of_nhds hy₀
  have hy₀e : y₀ ∈ e.source := by simpa [e] using hT₀.1
  -- In the chart `e = φ ∘ Φ_{-T}`, the function `g` is `C¹` near `e y₀`.
  have hge : ContDiffAt ℝ 1 (g ∘ e.symm) (e y₀) :=
    contDiffAt_comp_symm_transOpenPartialHomeomorph hT₀.1 hg
  have hK : ContinuousAt (fun y ↦ Real.exp (-T) • (fderiv ℝ (g ∘ e.symm) (e y)).comp
      (LinearMap.toContinuousLinearMap φ.negativeExtend)) y₀ :=
    (((hge.continuousAt_fderiv one_ne_zero).comp (e.continuousAt hy₀e)).clm_comp
      continuousAt_const).tendsto.const_smul _
  have hdiff : ∀ᶠ y in 𝓝 y₀, DifferentiableAt ℝ (g ∘ e.symm) (e y) :=
    (e.continuousAt hy₀e).eventually ((hge.eventually (by simp)).mono fun z hz ↦
      hz.differentiableAt one_ne_zero)
  refine hK.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ hy₀
  filter_upwards [nhdsWithin_le_nhds (hT.and hdiff), self_mem_nhdsWithin] with y ⟨hyT, hyd⟩ hy
  rw [mvfderiv_comp_unstableFrame_eq hφ (hyT hy) (hecoe y ▸ hyd), hecoe]

/-! ### Normal coordinates along the unstable frame of another critical point -/

section TwoCharts

variable {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}

omit hφ in
/-- **The normal coordinates along the unstable frame are invariant under the flow.** At a point
`y` of `W^u(p) ∩ W^s(q)`, the normal coordinates of `W^s(q)` of the unstable frame of `W^u(p)` are
the same at `y` and at `Φ_t y`: the flow multiplies the frame by `e^{-t}` and the normal coordinates
by `e^{t}`. This is the second component of the comparison map, whatever the indices of `p` and
`q`. -/
theorem stableNormal_comp_unstableFrame_flow
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hf : IsMorse 𝓘(ℝ, E) f) {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (t : ℝ) :
    (hX.stableNormal φq (hX.flow t y)).comp (hX.unstableFrame φp (hX.flow t y)) =
      (hX.stableNormal φq y).comp (hX.unstableFrame φp y) := by
  obtain ⟨Tp, hTp⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hy.1).exists
  obtain ⟨Tq, hTq⟩ := (hX.eventually_mem_linearForwardTimes hφq hy.2).exists
  ext c : 1
  have hN := stableNormal_mfderiv_flow hφq hTq t (hX.unstableFrame φp y c)
  simp only [ContinuousLinearMap.comp_apply]
  rw [unstableFrame_flow hφp hTp t c,
    ((hX.stableNormal φq (hX.flow t y)).map_smul _ _).trans (congrArg _ hN), smul_smul,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

end TwoCharts

end IsAdaptedPseudoGradient

end TauCeti
