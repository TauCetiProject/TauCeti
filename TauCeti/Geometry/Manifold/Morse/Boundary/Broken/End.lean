/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Broken.Direction
public import TauCeti.Geometry.Manifold.Morse.Boundary.Compactification
import TauCeti.Dynamics.Flow.Basic

/-!
# The broken ends of the compactified space of index-two trajectories

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold, and let
`p`, `r` be critical points. The trajectories from `p` to `r` are recorded by their pairs of points
`(y, z)` on two levels `c₁ > c₂` (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPairs`), and
when `ind p = ind r + 2` the closure of these pairs adds the trajectories broken once, at a
critical point `q` of intermediate index: the pairs `x = (x₁, x₂)` with `x₁` on a trajectory from
`p` to `q` and `x₂` on a trajectory from `q` to `r`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryPairs`). This file describes the unbroken
pairs near such a broken end `x`, in the form needed to compare the orientation of the arcs of the
compactified space with the signs of broken trajectories.

* **The crossing times diverge.** The time `T` taking the first point of an unbroken pair to its
  second point, which is positive since `f` decreases along the flow, tends to `+∞` as the pairs
  tend to `x` (`tendsto_atTop_of_tendsto_morseTrajectoryPairs`): no time takes `x₁ ∈ W^s(q)` to
  `x₂ ∈ W^s(r)`, so by `Flow.tendsto_abs_atTop_of_forall_apply_ne` the times cannot stay bounded.
  These are the times along which the nearby orbits cross the Morse chart of `q` linearly, as in
  `TauCeti.IsAdaptedPseudoGradient.eventually_forall_linearFlow_mem_target_of_broken`.
* **The comparison maps converge.** For Morse charts `φp`, `φq`, `φr` in which `X` is linear, the
  comparison maps `C_{pr}(y)` of the unbroken pairs `(y, z)` tend to `(id × B₂) ∘ C_{pq}(x₁)`, where
  `B₂` is the second component of `C_{qr}(x₂)`
  (`tendsto_trajectoryComparison_of_tendsto_morseTrajectoryPairs`). Their kernels are the tangent
  lines of the arc of unbroken trajectories, and the kernel of the limit is the line spanned by the
  gluing direction (`TauCeti.LinearAlgebra.Orientation.Breaking`).
* **The broken end is a strict local minimum of the leaving coordinate.** Let `a` be a time of
  linear forward flow of `x₁` in the chart `φq`, and `ℓ` a linear form positive on the direction in
  which `x₂` leaves `q`. The function `h (y, z) = ℓ (N(φq (Φ_a y)))`, which reads the coordinates
  `N` of negative weight in `φq`, vanishes at `x`, since `x₁ ∈ W^s(q)`
  (`TauCeti.IsAdaptedPseudoGradient.negativeCoord_toChart_flow_eq_zero_of_mem_stableSet`), and is
  positive at the unbroken pairs near `x`
  (`eventually_pos_negativeCoord_toChart_flow_of_tendsto_morseTrajectoryPairs`). Under the
  Morse–Smale condition, near `x` the compactified space consists of `x` and unbroken pairs, so `h`
  is positive on the compactified space near `x` away from `x`
  (`IsMorseSmale.eventually_pos_negativeCoord_toChart_flow_nhdsWithin_closure`). Along the gluing
  direction `h` decreases
  (`apply_negativeCoord_mfderiv_unstableFrame_lt_zero_of_trajectoryComparison_eq`),
  so this direction points out of the compactified space at its broken end.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `tendsto_atTop_of_tendsto_morseTrajectoryPairs`: the crossing times of unbroken pairs tending
  to a broken end tend to `+∞`.
* `exists_tendsto_atTop_tendsto_flow_of_tendsto_morseTrajectoryPairs`: such pairs have crossing
  times tending to `+∞` along which their first points flow to their second points, as the
  broken-trajectory limit theorems require.
* `tendsto_trajectoryComparison_of_tendsto_morseTrajectoryPairs`: their comparison maps converge.
* `eventually_pos_negativeCoord_toChart_flow_of_tendsto_morseTrajectoryPairs`: they lie on the
  positive side of the leaving coordinate.
* `IsMorseSmale.eventually_pos_negativeCoord_toChart_flow_nhdsWithin_closure`: the broken end is a
  strict local minimum of the leaving coordinate on the compactified space.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the boundary of the compactified space of index-two
  trajectories and its orientation at the broken trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (the compactified space of index-two trajectories as a manifold with boundary).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p q r : M} {c₁ c₂ : ℝ}

/-! ### Crossing times -/

/-- **The crossing times diverge at a broken end.** Let unbroken pairs `w n` on the levels
`c₁ > c₂` tend to a pair `x` whose first point lies in `W^s(q)` and whose second point lies in
`W^s(r)`, for `q ≠ r`, as the broken trajectory pairs through `q` do. Then the times `T n` taking
the first point of `w n` to its second point tend to `+∞`. -/
theorem tendsto_atTop_of_tendsto_morseTrajectoryPairs (h₂₁ : c₂ < c₁) {x : M × M}
    (hx₁ : x.1 ∈ hX.flow.stableSet q) (hx₂ : x.2 ∈ hX.flow.stableSet r) (hqr : q ≠ r)
    {ι : Type*} {l : Filter ι} {w : ι → M × M} {T : ι → ℝ} (hw : Tendsto w l (𝓝 x))
    (hwP : ∀ᶠ n in l, w n ∈ hX.morseTrajectoryPairs p r c₁ c₂)
    (hT : ∀ᶠ n in l, hX.flow (T n) (w n).1 = (w n).2) :
    Tendsto T l atTop := by
  -- No time takes `x₁ ∈ W^s(q)` to `x₂ ∈ W^s(r)`, so the times are unbounded.
  have hne : ∀ t, hX.flow t x.1 ≠ x.2 := fun t ht ↦
    (Flow.disjoint_stableSet hqr).notMem_of_mem_left
      ((Flow.apply_mem_stableSet_iff hX.flow t).2 hx₁) (ht ▸ hx₂)
  have habs := hX.flow.tendsto_abs_atTop_of_forall_apply_ne hne
    ((continuous_fst.tendsto x).comp hw)
    (((continuous_snd.tendsto x).comp hw).congr' (hT.mono fun _ hn ↦ hn.symm))
  -- The times are positive, since `f` decreases along the flow from the level `c₁` to `c₂`.
  refine habs.congr' ((hwP.and hT).mono fun n ⟨hn, hTn⟩ ↦ abs_of_pos ?_)
  obtain ⟨-, hn₁, hn₂, -⟩ := hX.mem_morseTrajectoryPairs.1 hn
  exact (hX.antitone_flow (w n).1).reflect_lt (by simpa [hTn, hn₁, hn₂] using h₂₁)

/-- **Crossing times at a broken end.** Let unbroken pairs `w n` on the levels `c₁ > c₂` tend to a
pair `x` whose first point lies in `W^s(q)` and whose second point lies in `W^s(r)`, for `q ≠ r`.
Then there are times `T n → +∞` with `Φ_{T n}` of the first point of `w n` tending to `x₂`: the time
hypotheses of the limit theorems near a broken trajectory, such as
`TauCeti.IsAdaptedPseudoGradient.tendsto_trajectoryComparison_of_broken`. -/
theorem exists_tendsto_atTop_tendsto_flow_of_tendsto_morseTrajectoryPairs (h₂₁ : c₂ < c₁)
    {x : M × M} (hx₁ : x.1 ∈ hX.flow.stableSet q) (hx₂ : x.2 ∈ hX.flow.stableSet r) (hqr : q ≠ r)
    {ι : Type*} {l : Filter ι} {w : ι → M × M} (hw : Tendsto w l (𝓝 x))
    (hwP : ∀ᶠ n in l, w n ∈ hX.morseTrajectoryPairs p r c₁ c₂) :
    ∃ T : ι → ℝ, Tendsto T l atTop ∧ Tendsto (fun n ↦ hX.flow (T n) (w n).1) l (𝓝 x.2) := by
  -- Choose a crossing time for every unbroken pair.
  have hex : ∀ n, ∃ t, w n ∈ hX.morseTrajectoryPairs p r c₁ c₂ → hX.flow t (w n).1 = (w n).2 :=
    fun n ↦ by
      by_cases hn : w n ∈ hX.morseTrajectoryPairs p r c₁ c₂
      · exact ⟨_, fun _ ↦ (hX.mem_morseTrajectoryPairs.1 hn).2.2.2.choose_spec⟩
      · exact ⟨0, fun h ↦ absurd h hn⟩
  choose T hT using hex
  replace hT : ∀ᶠ n in l, hX.flow (T n) (w n).1 = (w n).2 := hwP.mono hT
  exact ⟨T, tendsto_atTop_of_tendsto_morseTrajectoryPairs h₂₁ hx₁ hx₂ hqr hw hwP hT,
    ((continuous_snd.tendsto x).comp hw).congr' (hT.mono fun _ hn ↦ hn.symm)⟩

/-! ### Comparison maps and the leaving coordinate near a broken end -/

variable {φp : MorseChart E f p} {φq : MorseChart E f q} {φr : MorseChart E f r}

variable (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφq

/-- **Unbroken pairs near a broken end lie on the positive side of the leaving coordinate.** Let
`x = (x₁, x₂)` be a pair with `x₁ ∈ W^s(q)` and `x₂ ∈ W^u(q) ∩ W^s(r)`, for `q ≠ r`, let `a` be a
time of linear forward flow of `x₁` and `b` a time of linear backward flow of `x₂` in the Morse
chart `φq`, and let `ℓ` be a linear form positive on the leaving direction, the coordinates of
negative weight of `Φ_{-b} x₂`. If unbroken pairs `w n` on the levels `c₁ > c₂` tend to `x`, then
eventually `ℓ` is positive on the coordinates of negative weight of `Φ_a` of their first points.
At `x₁` itself these coordinates vanish
(`TauCeti.IsAdaptedPseudoGradient.negativeCoord_toChart_flow_eq_zero_of_mem_stableSet`). -/
theorem eventually_pos_negativeCoord_toChart_flow_of_tendsto_morseTrajectoryPairs
    (hf : IsMorse 𝓘(ℝ, E) f) (h₂₁ : c₂ < c₁) {x : M × M} (hx₁ : x.1 ∈ hX.flow.stableSet q)
    (hx₂ : x.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) (hqr : q ≠ r) {a b : ℝ}
    (ha : a ∈ hX.linearForwardTimes φq x.1) (hb : b ∈ hX.linearBackwardTimes φq x.2)
    (ℓ : ({i // φq.weight i < 0} → ℝ) →ₗ[ℝ] ℝ)
    (hℓ : 0 < ℓ (φq.negativeCoord (φq.toChart (hX.flow (-b) x.2))))
    {ι : Type*} {l : Filter ι} {w : ι → M × M} (hw : Tendsto w l (𝓝 x))
    (hwP : ∀ᶠ n in l, w n ∈ hX.morseTrajectoryPairs p r c₁ c₂) :
    ∀ᶠ n in l, 0 < ℓ (φq.negativeCoord (φq.toChart (hX.flow a (w n).1))) := by
  obtain ⟨T, hT, hz⟩ :=
    exists_tendsto_atTop_tendsto_flow_of_tendsto_morseTrajectoryPairs h₂₁ hx₁ hx₂.2 hqr hw hwP
  exact eventually_pos_negativeCoord_toChart_flow_of_broken hφq hf hx₁ ha hx₂.1 hb
    ((continuous_fst.tendsto x).comp hw) hT hz ℓ hℓ

variable (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
include hφp hφr

/-- **Comparison maps near a broken end.** Let `x = (x₁, x₂)` be a pair with
`x₁ ∈ W^u(p) ∩ W^s(q)` and `x₂ ∈ W^u(q) ∩ W^s(r)`, for `q ≠ r`, let `a` be a time of linear forward
flow of `x₁` and `b` a time of linear backward flow of `x₂` in the Morse chart `φq`. If unbroken
pairs `w n` on the levels `c₁ > c₂` tend to `x`, then the comparison maps `C_{pr}` at their first
points tend to `(id × B₂) ∘ C_{pq}(x₁)`, where `B₂ = N_r(x₂) ∘ F_q(x₂)` is the second component of
`C_{qr}(x₂)`. -/
theorem tendsto_trajectoryComparison_of_tendsto_morseTrajectoryPairs (hf : IsMorse 𝓘(ℝ, E) f)
    (h₂₁ : c₂ < c₁) {x : M × M} (hx₁ : x.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hx₂ : x.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) (hqr : q ≠ r) {a b : ℝ}
    (ha : a ∈ hX.linearForwardTimes φq x.1) (hb : b ∈ hX.linearBackwardTimes φq x.2)
    {ι : Type*} {l : Filter ι} {w : ι → M × M} (hw : Tendsto w l (𝓝 x))
    (hwP : ∀ᶠ n in l, w n ∈ hX.morseTrajectoryPairs p r c₁ c₂) :
    Tendsto (fun n ↦ hX.trajectoryComparison φp φr (w n).1) l
      (𝓝 (((ContinuousLinearMap.id ℝ ℝ).prodMap
        ((hX.stableNormal φr x.2).comp (hX.unstableFrame φq x.2))).comp
          (hX.trajectoryComparison φp φq x.1))) := by
  obtain ⟨T, hT, hz⟩ :=
    exists_tendsto_atTop_tendsto_flow_of_tendsto_morseTrajectoryPairs h₂₁ hx₁.2 hx₂.2 hqr hw hwP
  exact tendsto_trajectoryComparison_of_broken hφp hφq hφr hf hx₁.1 hx₁.2 ha hx₂.1 hb hx₂.2
    ((continuous_fst.tendsto x).comp hw) (hwP.mono fun _ hn ↦ (hX.mem_morseTrajectoryPairs.1 hn).1)
    hT hz

omit hφp hφr

namespace IsMorseSmale

variable (h : hX.IsMorseSmale)

include h in
/-- **The broken end is a strict local minimum of the leaving coordinate.** Let `p` and `r` be
critical points with `ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every
critical value strictly between `f r` and `f p` from `f r` and `f p`. Let `x = (x₁, x₂)` be a
broken pair through `q`, with `x₁ ∈ W^s(q)` and `x₂ ∈ W^u(q) ∩ W^s(r)`, let `a` and `b` be times of
linear forward and backward flow of `x₁` and `x₂` in the Morse chart `φq`, and let `ℓ` be a linear
form positive on the leaving direction. Then, on the compactified space of trajectories near `x`,
the function `(y, z) ↦ ℓ (N(φq (Φ_a y)))` is positive away from `x`, where it vanishes
(`TauCeti.IsAdaptedPseudoGradient.negativeCoord_toChart_flow_eq_zero_of_mem_stableSet`). -/
theorem eventually_pos_negativeCoord_toChart_flow_nhdsWithin_closure (hf : IsMorse 𝓘(ℝ, E) f)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2)
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁)
    {x : M × M} (hx₁ : x.1 ∈ hX.flow.stableSet q)
    (hx₂ : x.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) (hqr : q ≠ r) {a b : ℝ}
    (ha : a ∈ hX.linearForwardTimes φq x.1) (hb : b ∈ hX.linearBackwardTimes φq x.2)
    (ℓ : ({i // φq.weight i < 0} → ℝ) →ₗ[ℝ] ℝ)
    (hℓ : 0 < ℓ (φq.negativeCoord (φq.toChart (hX.flow (-b) x.2)))) :
    ∀ᶠ w in 𝓝[closure (hX.morseTrajectoryPairs p r c₁ c₂)] x, w ≠ x →
      0 < ℓ (φq.negativeCoord (φq.toChart (hX.flow a w.1))) := by
  set P := hX.morseTrajectoryPairs p r c₁ c₂
  -- Near `x`, the points of the compactified space other than `x` are unbroken pairs.
  have hF : ((closure P \ P) \ {x})ᶜ ∈ 𝓝 x :=
    ((h.finite_closure_diff_morseTrajectoryPairs hf hind hr₂ h₂₁ h₁p hgap).sdiff.isClosed
      ).isOpen_compl.mem_nhds fun hx ↦ hx.2 rfl
  have hpos := eventually_nhdsWithin_iff.1
    (eventually_pos_negativeCoord_toChart_flow_of_tendsto_morseTrajectoryPairs hφq hf h₂₁ hx₁ hx₂
      hqr ha hb ℓ hℓ (l := 𝓝[P] x) nhdsWithin_le_nhds self_mem_nhdsWithin)
  refine eventually_nhdsWithin_iff.2 ?_
  filter_upwards [hF, hpos] with w hwF hw hwP hwx
  exact hw (by_contra fun hwP' ↦ hwF ⟨⟨hwP, hwP'⟩, hwx⟩)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
