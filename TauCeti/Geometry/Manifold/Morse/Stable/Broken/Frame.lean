/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Frame
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# Unstable frames near a broken trajectory

Let `X` be a pseudo-gradient adapted to a Morse function `f` on a compact manifold, linear in
Morse charts `φp` at a critical point `p` and `φr` at a critical point `r`. Write `F_p` and `F_r`
for the unstable frames of `W^u(p)` and `W^u(r)`, and `N_r` for the normal coordinates of
`W^s(r)` (`TauCeti.Geometry.Manifold.Morse.Stable.Frame`).

Consider a point `y₀` of `W^u(p) ∩ W^s(r)`, on a trajectory `u` from `p` to `r`, and a point `z₀`
of `W^u(r)`, on a trajectory `v` leaving `r`. Points `yₙ ∈ W^u(p)` converging to `y₀` whose
orbits pass close to `r` and arrive, at times `Tₙ → ∞`, at points `zₙ = Φ_{Tₙ} yₙ` converging to
`z₀` follow the broken trajectory `(u, v)`. This file shows that the tangent spaces of `W^u(p)`
along such orbits converge to the image of a tangent space of `W^u(r)`, in the precise form of
frames: tested against any function `g` that is `C¹` at `z₀`,

`dg_{zₙ} ∘ F_p(zₙ) → dg_{z₀} ∘ F_r(z₀) ∘ N_r(y₀) ∘ F_p(y₀)`

(`TauCeti.IsAdaptedPseudoGradient.tendsto_mvfderiv_comp_unstableFrame_flow`). The composites with
`dg` are maps between fixed spaces, so the statement does not depend on charts of `M`. This is
the `C¹` λ-lemma at `r` read on unstable frames: the directions of `W^u(p)` transverse to `W^s(r)`
are carried by the passage near `r` onto `W^u(r)`, through their normal coordinates `N_r`, while
those along `W^s(r)` are crushed. The λ-lemma for discs in the split model of the flow near `r`,
whose forward images become graphs over the unstable set converging in `C^n`, is
`TauCeti.exists_splitQuadraticFlow_graph_tendstoUniformlyOn_iteratedFDeriv`; the statement here
concerns instead the derivative of the flow of `X` along single orbits on `M`, read directly from
the linear flow in the Morse chart.

The orbits must cross the Morse chart of `r` along its linear flow: for times `a` of linear
forward flow of `y₀` and `b` of linear backward flow of `z₀`, the linear orbit of the point
`Φ_a yₙ`, read in the coordinates of `φr`, stays in the chart for the times between `0` and
`Tₙ - a - b`. This is how trajectories near a broken trajectory cross a Morse box
(`TauCeti.IsAdaptedPseudoGradient.splitPassage_splitEntryTime_eq_splitExitTime`).

## Proof

Read the passage through `r` in the chart `φr`. At time `a` the orbit of `yₙ` has entered the
chart and at time `Tₙ - b` it is about to leave it towards `zₙ`. In between, the flow is linear,
so the derivative of `Φ_{Tₙ}` at `yₙ` factors as the derivative of `g ∘ Φ_b ∘ φr⁻¹`, the linear
flow `Λ_s` for the time `s = Tₙ - a - b` and the derivative of `φr ∘ Φ_a`. The linear flow
multiplies the coordinates of negative weight by `e^{s}` and those of positive weight by `e^{-s}`,
so `e^{-s} Λ_s = P + e^{-2s} (1 - P)`, where `P` keeps the coordinates of negative weight
(`TauCeti.MorseChart.exp_neg_smul_coord_symm_linearFlow`). As `s → ∞` this tends to `P`. The
outer derivatives converge by continuity, and the unstable frame of `p` converges along
`W^u(p)` (`TauCeti.IsAdaptedPseudoGradient.continuousWithinAt_mvfderiv_comp_unstableFrame`).
Finally `P` composed with the derivative of `φr ∘ Φ_a` at `y₀` is `e^{a}` times `N_r(y₀)`, and the
derivative of `g ∘ Φ_b ∘ φr⁻¹` on the coordinates of negative weight is `e^{b}` times
`dg_{z₀} ∘ F_r(z₀)`; the unstable frame of `p` at `zₙ` is `e^{-Tₙ}` times the derivative of
`Φ_{Tₙ}` applied to the frame at `yₙ`, and the three exponentials cancel.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.mvfderiv_unstableFrame_flow_eq`: after a linear crossing of the
  chart of `r`, the derivative of a function along the unstable frame of `p` is read off the linear
  flow.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_mvfderiv_comp_unstableFrame_flow`: the unstable
  frames of `p` along orbits near a broken trajectory through `r` converge to
  `F_r(z₀) ∘ N_r(y₀) ∘ F_p(y₀)`.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 2,
  §7 (the λ-lemma).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations near broken trajectories).
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

variable {hX : IsAdaptedPseudoGradient f X} {p r : M} {φp : MorseChart E f p}
  {φr : MorseChart E f r}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφr : ∀ y ∈ φr.toChart.source,
    φr.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φr.toChart y (X y)) =
      fun i ↦ -(φr.weight i * φr.coord (φr.toChart y) i))
include hφp hφr

/-- **The unstable frame after a linear crossing.** Let the orbit of `y` lie in the Morse chart
`φr` at time `a` and cross it along the linear flow for the time `s = T - a - b ≥ 0`. Then the
derivative of a function `g` along the unstable frame of `p` at `Φ_T y` is read off the linear flow:
it is `e^{-T}` times the derivative of `g ∘ e⁻¹`, for the chart `e = φr ∘ Φ_{-b}`, applied to the
vector of the model space whose coordinates are those of the derivative of `φr ∘ Φ_a` along the
frame at `y`, moved by the linear flow for the time `s`. -/
theorem mvfderiv_unstableFrame_flow_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : M → F} {y : M} {a b T Tp : ℝ} (hTp : Tp ∈ hX.linearBackwardTimes φp y)
    (hya : hX.flow a y ∈ φr.toChart.source) (hT : a + b ≤ T)
    (hcross : ∀ t ∈ Icc 0 (T - a - b),
      φr.coord.symm (φr.linearFlow t (φr.coord (φr.toChart (hX.flow a y)))) ∈ φr.toChart.target)
    (hg : DifferentiableAt ℝ
      (g ∘ ((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart).symm)
      (((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart)
        (hX.flow T y)))
    (c : {i // φp.weight i < 0} → ℝ) :
    mvfderiv 𝓘(ℝ, E) g (hX.flow T y) (hX.unstableFrame φp (hX.flow T y) c) =
      Real.exp (-T) • fderiv ℝ
        (g ∘ ((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart).symm)
        (((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart)
          (hX.flow T y))
        (φr.coord.symm (φr.linearFlow (T - a - b)
          (φr.coord (mvfderiv 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y (hX.unstableFrame φp y c))))) := by
  -- Near `z = Φ_T y` write `g = (g ∘ e⁻¹) ∘ e`; then `e ∘ Φ_T = φr ∘ Φ_{s + a}` near `y`, and the
  -- derivative of `φr ∘ Φ_{s + a}` is the linear flow applied to that of `φr ∘ Φ_a`
  -- (`coord_mfderiv_toChart_comp_flow_add`); the frame at `z` is `e^{-T}` times the derivative of
  -- `Φ_T` applied to the frame at `y` (`unstableFrame_flow`).
  set e := (hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart
  set s := T - a - b
  set z := hX.flow T y
  have hs : 0 ≤ s := by simp only [s]; linarith
  have huIcc : ∀ t ∈ uIcc 0 s,
      φr.coord.symm (φr.linearFlow t (φr.coord (φr.toChart (hX.flow a y)))) ∈ φr.toChart.target :=
    fun t ht ↦ hcross t (by rwa [uIcc_of_le hs] at ht)
  have hd (t : ℝ) (w : M) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) w :=
    (hX.contMDiff_flow_apply t).mdifferentiable (by simp) w
  have he' : (e : M → E) = φr.toChart ∘ hX.flow (-b) := funext fun w ↦ by simp [e]
  have hsz : hX.flow (s + a) y = hX.flow (-b) z := by
    rw [← Flow.map_add]
    congr 1
    simp only [s]
    ring
  -- At time `s` the linear orbit is the orbit of the flow, so `Φ_{-b} z` lies in the chart.
  have hzr : hX.flow (-b) z ∈ φr.toChart.source := by
    have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φr hφr huIcc
    rw [φr.toChart_symm_coord_symm_coord hya, ← Flow.map_add] at hflow
    rw [← hsz, hflow]
    exact φr.toChart.map_target (huIcc s right_mem_uIcc)
  have hzen : z ∈ e.source := by simpa [e] using hzr
  -- `g` is `(g ∘ e⁻¹) ∘ e` near `z`, and `e ∘ Φ_T` is `φr ∘ Φ_{s + a}`.
  have hloc : g =ᶠ[𝓝 z] (g ∘ e.symm) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hzen] with w hw
    simp [e.left_inv hw]
  have hed : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e z := by
    rw [he']
    exact (φr.mdifferentiableAt_toChart hzr).comp _ (hd _ _)
  have hcompT : φr.toChart ∘ hX.flow (s + a) = e ∘ hX.flow T := by
    funext w
    rw [he', comp_apply, comp_apply, comp_apply, ← Flow.map_add]
    congr 2
    simp only [s]
    ring
  have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e z
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) y (hX.unstableFrame φp y c)) =
      φr.coord.symm (φr.linearFlow s
        (φr.coord (mvfderiv 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y (hX.unstableFrame φp y c)))) := by
    have hmf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e z
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) y (hX.unstableFrame φp y c)) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φr.toChart ∘ hX.flow (s + a)) y (hX.unstableFrame φp y c) := by
      rw [hcompT, mfderiv_comp_apply y hed (hd _ _)]
    rw [hmf]
    apply φr.coord.injective
    rw [LinearEquiv.apply_symm_apply, hX.coord_mfderiv_toChart_comp_flow_add hφr hya huIcc,
      mvfderiv_apply_eq_mfderiv_apply]
  rw [hloc.mvfderiv_eq, mvfderiv_comp_apply z (mdifferentiableAt_iff_differentiableAt.2 hg) hed,
    mvfderiv_eq_fderiv_apply, unstableFrame_flow hφp hTp T c, ← hchain]
  exact (congrArg _ ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e z).map_smul _ _)).trans
    ((fderiv ℝ _ _).map_smul _ _)

omit hφp in
/-- The limit in the λ-lemma on frames, read in the charts: the derivative of `g ∘ e⁻¹`, for the
chart `e = φr ∘ Φ_{-b}`, on the coordinates of negative weight of the derivative of `φr ∘ Φ_a`
along the frame of `p` at `y₀`, rescaled by `e^{-(a + b)}`. -/
private theorem exp_smul_fderiv_negativeExtend_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : M → F} {y₀ z₀ : M} {a b : ℝ} (ha : a ∈ hX.linearForwardTimes φr y₀)
    (hb : b ∈ hX.linearBackwardTimes φr z₀)
    (hg : DifferentiableAt ℝ
      (g ∘ ((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart).symm)
      (((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart) z₀))
    (c : {i // φp.weight i < 0} → ℝ) :
    Real.exp (-(a + b)) • fderiv ℝ
        (g ∘ ((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart).symm)
        (((hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart) z₀)
        (φr.negativeExtend (φr.negativeCoord
          (mvfderiv 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y₀ (hX.unstableFrame φp y₀ c)))) =
      mvfderiv 𝓘(ℝ, E) g z₀
        (hX.unstableFrame φr z₀ (hX.stableNormal φr y₀ (hX.unstableFrame φp y₀ c))) := by
  set e := (hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart
  have hecoe : e z₀ = φr.toChart (hX.flow (-b) z₀) := by simp [e]
  have hFr := congrArg (fun A ↦ A (hX.stableNormal φr y₀ (hX.unstableFrame φp y₀ c)))
    (hX.mvfderiv_comp_unstableFrame_eq hφr hb (hecoe ▸ hg))
  have hN : φr.negativeCoord
      (mvfderiv 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y₀ (hX.unstableFrame φp y₀ c)) =
        Real.exp a • hX.stableNormal φr y₀ (hX.unstableFrame φp y₀ c) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, stableNormal_apply hφr ha, smul_smul, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, one_smul]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, LinearMap.coe_toContinuousLinearMap']
    at hFr
  rw [hFr, ← hecoe, hN, map_smul, map_smul, smul_smul, ← Real.exp_add,
    show -(a + b) + a = -b by ring]

/-- **Unstable frames near a broken trajectory (the λ-lemma on frames).** Let `y₀` be a point of
`W^u(p)` with a time `a` of linear forward flow in the Morse chart `φr` of `r`, so that
`y₀ ∈ W^s(r)`, and `z₀` a point with a time `b` of linear backward flow in `φr`, so that
`z₀ ∈ W^u(r)`. Let `yₙ ∈ W^u(p)` tend to `y₀`, and `Tₙ → ∞` with `zₙ = Φ_{Tₙ} yₙ → z₀`, the orbits
crossing the chart of `r` linearly between the times `a` and `Tₙ - b`. Then for every function `g`
which is `C¹` at `z₀`, the derivative of `g` along the unstable frame of `p` at `zₙ` tends to

`dg_{z₀} ∘ F_r(z₀) ∘ N_r(y₀) ∘ F_p(y₀)`,

the derivative of `g` along the unstable frame of `r` at `z₀`, applied to the normal coordinates of
`W^s(r)` at `y₀` of the unstable frame of `p` at `y₀`. -/
theorem tendsto_mvfderiv_comp_unstableFrame_flow (hf : IsMorse 𝓘(ℝ, E) f) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : M → F} {y₀ z₀ : M} {a b : ℝ}
    (hy₀ : y₀ ∈ hX.flow.unstableSet p) (ha : a ∈ hX.linearForwardTimes φr y₀)
    (hb : b ∈ hX.linearBackwardTimes φr z₀) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 g z₀)
    {ι : Type*} {l : Filter ι} {y : ι → M} {T : ι → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (hyu : ∀ᶠ n in l, y n ∈ hX.flow.unstableSet p) (hT : Tendsto T l atTop)
    (hcross : ∀ᶠ n in l, ∀ t ∈ Icc 0 (T n - a - b),
      φr.coord.symm (φr.linearFlow t (φr.coord (φr.toChart (hX.flow a (y n))))) ∈
        φr.toChart.target)
    (hz : Tendsto (fun n ↦ hX.flow (T n) (y n)) l (𝓝 z₀)) :
    Tendsto (fun n ↦ (mvfderiv 𝓘(ℝ, E) g (hX.flow (T n) (y n))).comp
        (hX.unstableFrame φp (hX.flow (T n) (y n)))) l
      (𝓝 ((mvfderiv 𝓘(ℝ, E) g z₀).comp ((hX.unstableFrame φr z₀).comp
        ((hX.stableNormal φr y₀).comp (hX.unstableFrame φp y₀))))) := by
  -- In the chart `e = φr ∘ Φ_{-b}` near `z₀`, `g` is the function `h = g ∘ e⁻¹` of the model space,
  -- `C¹` near `e z₀`. By `mvfderiv_unstableFrame_flow_eq`, the derivative along the frame at `zₙ`
  -- is `e^{-(a + b)}` times the derivative of `h` at `e zₙ` after the rescaled linear flow
  -- `e^{-sₙ} Λ_{sₙ} = P + e^{-2sₙ} Q` applied to `L(yₙ)`, the derivative of `φr ∘ Φ_a` along the
  -- frame at `yₙ`. Each factor converges, and the limit is identified by
  -- `exp_smul_fderiv_negativeExtend_eq`.
  set e := (hX.flowDiffeomorph (-b)).toHomeomorph.transOpenPartialHomeomorph φr.toChart
  have hz₀r := ((hX.mem_linearBackwardTimes φr).1 hb).1
  set h : E → F := g ∘ e.symm
  have hh : ContDiffAt ℝ 1 h (e z₀) := contDiffAt_comp_symm_transOpenPartialHomeomorph hz₀r hg
  set P : E →L[ℝ] E := LinearMap.toContinuousLinearMap (φr.negativeExtend ∘ₗ φr.negativeCoord)
  set Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  set L : M → ({i // φp.weight i < 0} → ℝ) →L[ℝ] E :=
    fun y ↦ (mvfderiv 𝓘(ℝ, E) (φr.toChart ∘ hX.flow a) y).comp (hX.unstableFrame φp y)
  have hL : Tendsto (fun n ↦ L (y n)) l (𝓝 (L y₀)) :=
    (hX.continuousWithinAt_mvfderiv_comp_unstableFrame hφp hf
      ((contMDiffAt_toChart_comp_flow ((hX.mem_linearForwardTimes φr).1 ha).1).of_le
        (by norm_cast)) hy₀).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hy, hyu⟩)
  have hez : Tendsto (fun n ↦ e (hX.flow (T n) (y n))) l (𝓝 (e z₀)) :=
    (e.continuousAt (by simpa [e] using hz₀r)).tendsto.comp hz
  have hPQ : Tendsto (fun n ↦ P + Real.exp (-(2 * (T n - a - b))) • Q) l (𝓝 P) := by
    simpa [sub_eq_add_neg] using tendsto_const_nhds.add ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ hT)).const_mul_atTop
        two_pos)).smul_const Q)
  have hK := ((isBoundedBilinearMap_comp.continuous.tendsto _).comp
    (((hh.continuousAt_fderiv one_ne_zero).tendsto.comp hez).prodMk_nhds
      ((isBoundedBilinearMap_comp.continuous.tendsto _).comp (hPQ.prodMk_nhds hL)))).const_smul
        (Real.exp (-(a + b)))
  have hlim : Real.exp (-(a + b)) • (fderiv ℝ h (e z₀)).comp (P.comp (L y₀)) =
      (mvfderiv 𝓘(ℝ, E) g z₀).comp ((hX.unstableFrame φr z₀).comp
        ((hX.stableNormal φr y₀).comp (hX.unstableFrame φp y₀))) := by
    ext c : 1
    exact exp_smul_fderiv_negativeExtend_eq hφr ha hb (hh.differentiableAt one_ne_zero) c
  rw [← hlim]
  refine hK.congr' ?_
  obtain ⟨Tp, hTp⟩ := hX.exists_eventually_mem_linearBackwardTimes hφp hf hy₀
  have hya : ∀ᶠ n in l, hX.flow a (y n) ∈ φr.toChart.source :=
    ((hX.flow.continuous continuous_const continuous_id).continuousAt.tendsto.comp hy).eventually
      (φr.toChart.open_source.mem_nhds ((hX.mem_linearForwardTimes φr).1 ha).1)
  have hhd : ∀ᶠ n in l, DifferentiableAt ℝ h (e (hX.flow (T n) (y n))) :=
    hez.eventually ((hh.eventually (by simp)).mono fun u hu ↦ hu.differentiableAt one_ne_zero)
  filter_upwards [hy.eventually hTp, hyu, hya, hhd, hcross,
    hT.eventually_ge_atTop (a + b)] with n hTpn hyun hyan hhdn hcrossn hTn
  ext c : 1
  have hPQn : (P + Real.exp (-(2 * (T n - a - b))) • Q) (L (y n) c) =
      Real.exp (-(T n - a - b)) •
        φr.coord.symm (φr.linearFlow (T n - a - b) (φr.coord (L (y n) c))) := by
    simp only [P, Q, add_apply, smul_apply, sub_apply, LinearMap.coe_toContinuousLinearMap',
      ContinuousLinearMap.id_apply, LinearMap.comp_apply, φr.exp_neg_smul_coord_symm_linearFlow]
  simp only [comp_apply, ContinuousLinearMap.comp_apply, smul_apply]
  rw [mvfderiv_unstableFrame_flow_eq hφp hφr (hTpn hyun) hyan hTn hcrossn hhdn c, hPQn,
    (fderiv ℝ h _).map_smul, smul_smul, ← Real.exp_add]
  congr 2
  ring

end IsAdaptedPseudoGradient

end TauCeti
