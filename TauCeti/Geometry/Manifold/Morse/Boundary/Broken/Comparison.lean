/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Frame
import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Crossing

/-!
# Comparison maps near a broken trajectory

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold, linear in Morse
charts `φp`, `φr`, `φq` at critical points `p`, `r`, `q`. At a point `y` of `W^u(p) ∩ W^s(q)` the
comparison map `C_{pq}(y) : Vp → ℝ × Vq`, `v ↦ (df_y (F_p v), N_q (F_p v))`
(`TauCeti.IsAdaptedPseudoGradient.trajectoryComparison`), reads the unstable frame `F_p` of
`W^u(p)` through the differential of `f` and the normal coordinates `N_q` of `W^s(q)`. Its kernel
is the tangent space of the space of trajectories from `p` to `q`, which the orientations of the
integral Morse complex orient.

This file computes the limit of the comparison maps along trajectories from `p` to `q` converging
to a broken trajectory `(u, v)`, with `u` from `p` to `r` through `y₀` and `v` from `r` to `q`
through `z₀`. Write `A = C_{pr}(y₀)` and `B = (B₁, B₂) = C_{rq}(z₀)`. Then

`C_{pq}(yₙ) → (id × B₂) ∘ A = (df_{y₀} ∘ F_p(y₀), B₂ ∘ N_r(y₀) ∘ F_p(y₀))`

(`TauCeti.IsAdaptedPseudoGradient.tendsto_trajectoryComparison_of_broken`), for points `yₙ` of
`W^u(p) ∩ W^s(q)` tending to `y₀` whose orbits reach points `zₙ` tending to `z₀` at times
`Tₙ → ∞`. Such orbits cross the Morse chart of `r` along its linear flow
(`TauCeti.IsAdaptedPseudoGradient.eventually_forall_linearFlow_mem_target_of_broken`). This is the
convergence used in `TauCeti.LinearAlgebra.Orientation.Breaking`, which computes the orientation of
the kernel of `(id × B₂) ∘ A` from those of the kernels of `A` and `B`: when
`ind p = ind r + 1 = ind q + 2`, the line `ker ((id × B₂) ∘ A)` is oriented by `-ε(u) ε(v)` times
the gluing direction, where `ε(u)` and `ε(v)` are the signs of the two trajectories. It is the
analytic input for comparing the boundary orientation of the compactified space of index-two
trajectories at a broken end with the sign of the broken trajectory, which the integral
`∂ ∘ ∂ = 0` needs.

No rescaling is needed: along the flow the unstable frame of `p` is multiplied by `e^{-t}` and the
normal coordinates of `W^s(q)` by `e^{t}`, so the second component of `C_{pq}` is the same at `yₙ`
and at `zₙ` (`TauCeti.IsAdaptedPseudoGradient.stableNormal_comp_unstableFrame_flow`). At `zₙ` the
unstable frame of `p` converges, by the λ-lemma on frames
(`TauCeti.IsAdaptedPseudoGradient.tendsto_mvfderiv_comp_unstableFrame_flow`), to
`F_r(z₀) ∘ N_r(y₀) ∘ F_p(y₀)`, and the normal coordinates of `W^s(q)` are read near `z₀` in a single
chart `φq ∘ Φ_c`. The first component converges to `df_{y₀} ∘ F_p(y₀)` by continuity of the frame
along `W^u(p)`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.tendsto_stableNormal_comp_unstableFrame_of_broken`: the second
  component of the comparison maps near a broken trajectory.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_trajectoryComparison_of_broken`: the comparison maps
  along trajectories converging to a broken trajectory tend to `(id × B₂) ∘ A`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the spaces of trajectories and the
  boundary of the compactified space of index-two trajectories).
* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the λ-lemma).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p r q : M} {φp : MorseChart E f p}
  {φr : MorseChart E f r} {φq : MorseChart E f q}

variable (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφp hφr hφq

/-- **Normal coordinates along the unstable frame near a broken trajectory.** Under the hypotheses
of `TauCeti.IsAdaptedPseudoGradient.tendsto_trajectoryComparison_of_broken`, the normal coordinates
of `W^s(q)` along the unstable frame of `W^u(p)` at `yₙ`, the second component of the comparison
map `C_{pq}(yₙ)`, tend to `N_q(z₀) ∘ F_r(z₀) ∘ N_r(y₀) ∘ F_p(y₀)`. -/
theorem tendsto_stableNormal_comp_unstableFrame_of_broken (hf : IsMorse 𝓘(ℝ, E) f) {y₀ z₀ : M}
    {a b : ℝ} (hy₀ : y₀ ∈ hX.flow.unstableSet p) (hy₀r : y₀ ∈ hX.flow.stableSet r)
    (ha : a ∈ hX.linearForwardTimes φr y₀) (hz₀r : z₀ ∈ hX.flow.unstableSet r)
    (hb : b ∈ hX.linearBackwardTimes φr z₀) (hz₀ : z₀ ∈ hX.flow.stableSet q)
    {ι : Type*} {l : Filter ι} {y : ι → M} {T : ι → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (hyl : ∀ᶠ n in l, y n ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hT : Tendsto T l atTop)
    (hz : Tendsto (fun n ↦ hX.flow (T n) (y n)) l (𝓝 z₀)) :
    Tendsto (fun n ↦ (hX.stableNormal φq (y n)).comp (hX.unstableFrame φp (y n))) l
      (𝓝 ((hX.stableNormal φq z₀).comp ((hX.unstableFrame φr z₀).comp
        ((hX.stableNormal φr y₀).comp (hX.unstableFrame φp y₀))))) := by
  -- The second component is invariant under the flow, so it may be read at `zₙ`; near `z₀` on
  -- `W^s(q)` the normal coordinates are read at one time `c` of linear forward flow, through the
  -- function `φq ∘ Φ_c`, and the λ-lemma on frames applies to it.
  obtain ⟨c, hc⟩ := hX.exists_eventually_mem_linearForwardTimes hφq hz₀
  have hc₀ : c ∈ hX.linearForwardTimes φq z₀ := hc.self_of_nhds hz₀
  have hlam := hX.tendsto_mvfderiv_comp_unstableFrame_flow hφp hφr hf hy₀ ha hb
    ((contMDiffAt_toChart_comp_flow ((hX.mem_linearForwardTimes φq).1 hc₀).1).of_le
      (by norm_cast)) hy (hyl.mono fun _ h ↦ h.1) hT
      (eventually_forall_linearFlow_mem_target_of_broken hφr hf hy₀r ha hz₀r hb hy hz) hz
  rw [stableNormal_eq_comp_mvfderiv hφq hc₀, ContinuousLinearMap.comp_assoc]
  refine ((isBoundedBilinearMap_comp.continuous.tendsto _).comp
    (tendsto_const_nhds.prodMk_nhds hlam)).congr' ?_
  filter_upwards [hyl, hz.eventually hc] with n hn hcn
  have hzq : hX.flow (T n) (y n) ∈ hX.flow.stableSet q :=
    (Flow.apply_mem_stableSet_iff _ _).2 hn.2
  rw [comp_apply, ← stableNormal_comp_unstableFrame_flow hφp hφq hf hn (T n),
    stableNormal_eq_comp_mvfderiv hφq (hcn hzq), ContinuousLinearMap.comp_assoc]

/-- **Comparison maps near a broken trajectory.** Let `y₀` be a point of `W^u(p) ∩ W^s(r)`, on a
trajectory from `p` to `r`, with a time `a` of linear forward flow in the Morse chart `φr` of `r`,
and `z₀` a point of `W^u(r) ∩ W^s(q)`, on a trajectory from `r` to `q`, with a time `b` of linear
backward flow in `φr`. Let `yₙ ∈ W^u(p) ∩ W^s(q)` tend to `y₀`, and `Tₙ → ∞` with
`Φ_{Tₙ} yₙ → z₀`. Then the comparison maps `C_{pq}(yₙ)` tend to

`(id × B₂) ∘ C_{pr}(y₀)`,

where `B₂ = N_q(z₀) ∘ F_r(z₀)` is the second component of the comparison map `C_{rq}(z₀)`. -/
theorem tendsto_trajectoryComparison_of_broken (hf : IsMorse 𝓘(ℝ, E) f) {y₀ z₀ : M} {a b : ℝ}
    (hy₀ : y₀ ∈ hX.flow.unstableSet p) (hy₀r : y₀ ∈ hX.flow.stableSet r)
    (ha : a ∈ hX.linearForwardTimes φr y₀) (hz₀r : z₀ ∈ hX.flow.unstableSet r)
    (hb : b ∈ hX.linearBackwardTimes φr z₀) (hz₀ : z₀ ∈ hX.flow.stableSet q)
    {ι : Type*} {l : Filter ι} {y : ι → M} {T : ι → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (hyl : ∀ᶠ n in l, y n ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (hT : Tendsto T l atTop)
    (hz : Tendsto (fun n ↦ hX.flow (T n) (y n)) l (𝓝 z₀)) :
    Tendsto (fun n ↦ hX.trajectoryComparison φp φq (y n)) l
      (𝓝 (((ContinuousLinearMap.id ℝ ℝ).prodMap
        ((hX.stableNormal φq z₀).comp (hX.unstableFrame φr z₀))).comp
          (hX.trajectoryComparison φp φr y₀))) := by
  -- The first component converges by continuity of the frame along `W^u(p)`, the second by
  -- `tendsto_stableNormal_comp_unstableFrame_of_broken`.
  have h₁ : Tendsto (fun n ↦ (mvfderiv 𝓘(ℝ, E) f (y n)).comp (hX.unstableFrame φp (y n))) l
      (𝓝 ((mvfderiv 𝓘(ℝ, E) f y₀).comp (hX.unstableFrame φp y₀))) :=
    (hX.continuousWithinAt_mvfderiv_comp_unstableFrame hφp hf
      (hf.contMDiff.contMDiffAt.of_le (by norm_cast)) hy₀).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hy, hyl.mono fun _ h ↦ h.1⟩)
  have h₂ := tendsto_stableNormal_comp_unstableFrame_of_broken hφp hφr hφq hf hy₀ hy₀r ha hz₀r hb
    hz₀ hy hyl hT hz
  -- Both the comparison maps and the limit are pairings of two components by
  -- `ContinuousLinearMap.prodL`.
  have hlim : ((ContinuousLinearMap.id ℝ ℝ).prodMap
        ((hX.stableNormal φq z₀).comp (hX.unstableFrame φr z₀))).comp
          (hX.trajectoryComparison φp φr y₀) =
      ContinuousLinearMap.prodL ℝ ((mvfderiv 𝓘(ℝ, E) f y₀).comp (hX.unstableFrame φp y₀),
        (hX.stableNormal φq z₀).comp ((hX.unstableFrame φr z₀).comp
          ((hX.stableNormal φr y₀).comp (hX.unstableFrame φp y₀)))) := by
    ext v : 1
    simp only [ContinuousLinearMap.prodL_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, trajectoryComparison_apply, ContinuousLinearMap.coe_prodMap',
      Prod.map_apply, ContinuousLinearMap.id_apply]
  rw [trajectoryComparison_eq_prodL, hlim]
  exact (ContinuousLinearMap.prodL ℝ).continuous.continuousAt.tendsto.comp (h₁.prodMk_nhds h₂)

end IsAdaptedPseudoGradient

end TauCeti
