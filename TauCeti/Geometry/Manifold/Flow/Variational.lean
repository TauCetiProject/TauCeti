/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Dynamics.Flow.Variational
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The variational equation of a flow on a manifold

Let `X` be a time-dependent vector field on a boundaryless manifold `M` modelled on a
finite-dimensional space, jointly `C¹` on `ℝ × M`, and let `Φ_{s,t} = timeDependentFlowOf X s t`
be its maximal flow. A tangent vector `w` at `x` is carried along the orbit of `x` by the
differentials `dΦ_{s,t} w`, which live in the varying tangent spaces `T_{Φ_{s,t} x} M`. Read in a
fixed extended chart `e` whose source contains `Φ_{s,t₀} x`, they become a curve
`J(t) = de(dΦ_{s,t} w)` in the model space, and this curve solves the linear equation

`J'(t) = DX^e_t(e(Φ_{s,t} x)) J(t)`,

where `X^e_t` is the chart expression of `X t`, its pullback along `e.symm`
(`VectorField.mpullbackWithin` on the range of the model). This is the **variational equation**
(`TauCeti.hasDerivAt_mfderiv_extChartAt_timeDependentFlowOf_apply`), and its operator form says
that the chart readings `d(e ∘ Φ_{s,t})_x` of the differentials solve `J' = DX^e_t J`
(`TauCeti.hasDerivAt_mfderiv_extChartAt_comp_timeDependentFlowOf`). Only the spatial derivative of
`X t` enters, and the field need only be `C¹`. The autonomous statements for a `C¹` vector field
`v` and its maximal flow `flowOf v` are
`TauCeti.hasDerivAt_mfderiv_extChartAt_comp_flowOf` and
`TauCeti.hasDerivAt_mfderiv_extChartAt_flowOf_apply`.

The proof reduces to the initial time: near `t₀` the flow from `s` is the flow from `t₀` after the
flow from `s` to `t₀`, and the flow from `t₀` read in the chart is a family of maps of the model
space which is the identity at time `t₀` and whose curves solve the equation of the chart field.
The variational equation of such a family at its initial time is
`TauCeti.hasDerivAt_fderiv_of_eventually_hasDerivAt`, which cuts the chart field off to a globally
Lipschitz one and compares with its global flow. The chart field is jointly `C¹` because the
manifold is `C²`, so that the tangent bundle is a `C¹` vector bundle.

## Main results

* `TauCeti.hasDerivAt_mfderiv_extChartAt_comp_timeDependentFlowOf`,
  `TauCeti.hasDerivAt_mfderiv_extChartAt_timeDependentFlowOf_apply`: the variational equation of a
  time-dependent flow, in a chart.
* `TauCeti.hasDerivAt_mfderiv_extChartAt_comp_flowOf`,
  `TauCeti.hasDerivAt_mfderiv_extChartAt_flowOf_apply`: the variational equation of an autonomous
  flow, in a chart.

## References

* P. Hartman, *Ordinary Differential Equations*, 2nd ed., SIAM, 2002, Chapter V, Theorem 3.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017, §3.1
  (the linearized Hamiltonian flow).
-/

public section

open Function Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]

section TimeDependent

variable {X : ℝ → (x : M) → TangentSpace I x}
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
  {s t : ℝ} {x z : M}
include hX

/-- The flow from time `t`, read in a chart around a point `y` of its source, is at time `t` the
identity near the chart image of `y`, and its differentials there have derivative the derivative of
the chart field `X^e_t`. This is the variational equation at the initial time, in the chart. -/
private theorem hasDerivAt_fderiv_extChartAt_timeDependentFlowOf_extChartAt_symm {y : M}
    (hy : y ∈ (extChartAt I z).source) :
    HasDerivAt (fun u ↦ fderiv ℝ (fun q ↦ extChartAt I z
        (timeDependentFlowOf X t u ((extChartAt I z).symm q))) (extChartAt I z y))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I z).symm (X t) (range I))
        (extChartAt I z y)) t := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  set e := extChartAt I z
  set ψ : ℝ → E → E := fun u q ↦ e (timeDependentFlowOf X t u (e.symm q))
  have hz₀ : e y ∈ e.target := e.map_source hy
  have hyy : e.symm (e y) = y := e.left_inv hy
  have hyt : ((t, t), y) ∈ timeDependentFlowDomain X := mem_timeDependentFlowDomain_self hX t y
  have hyty : timeDependentFlowOf X t t (e.symm (e y)) = y := by
    rw [hyy, timeDependentFlowOf_self]
  -- The flow from time `t`, read in the chart, is a jointly continuous family of maps which is the
  -- identity near `e y` at time `t`.
  have hsymm : ContinuousAt (fun p : ℝ × E ↦ e.symm p.2) (t, e y) :=
    (continuousAt_extChartAt_symm'' hz₀).comp (x := (t, e y)) continuousAt_snd
  have hΦc : ContinuousAt (fun p : ℝ × E ↦ timeDependentFlowOf X t p.1 (e.symm p.2)) (t, e y) :=
    ContinuousAt.comp_of_eq (g := uncurry (timeDependentFlowOf X t))
      (contMDiffAt_uncurry_timeDependentFlowOf le_rfl hX hyt).continuousAt
      (continuousAt_fst.prodMk hsymm) (by simp [hyy])
  have hψc : ContinuousAt (fun p : ℝ × E ↦ ψ p.1 p.2) (t, e y) :=
    ContinuousAt.comp_of_eq (continuousAt_extChartAt' (I := I) hy) hΦc hyty
  have hψ₀ : ∀ᶠ q in 𝓝 (e y), ψ t q = q := by
    filter_upwards [(isOpen_extChartAt_target z).mem_nhds hz₀] with q hq
    simp only [ψ, timeDependentFlowOf_self, e.right_inv hq]
  -- Its curves solve the equation of the chart field, by the equation of the flow on `M`.
  have hψ : ∀ᶠ p in 𝓝 (t, e y), HasDerivAt (fun u ↦ ψ u p.2)
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I e.symm (X p.1) (range I) (ψ p.1 p.2)) p.1 := by
    have h₁ : ∀ᶠ p : ℝ × E in 𝓝 (t, e y),
        ((t, p.1), e.symm p.2) ∈ timeDependentFlowDomain X :=
      ((continuousAt_const.prodMk continuousAt_fst).prodMk hsymm).preimage_mem_nhds
        ((isOpen_timeDependentFlowDomain hX).mem_nhds (by simpa [hyy] using hyt))
    have h₂ : ∀ᶠ p : ℝ × E in 𝓝 (t, e y), timeDependentFlowOf X t p.1 (e.symm p.2) ∈ e.source :=
      hΦc.preimage_mem_nhds ((isOpen_extChartAt_source z).mem_nhds (by rwa [hyty]))
    filter_upwards [h₁, h₂] with p hp₁ hp₂
    have hV := VectorField.mpullbackWithin_extChartAt_symm_apply (X p.1) hp₂
    rw [TangentBundle.trivializationAt_snd_eq_tangentCoordChange] at hV
    exact ((hasMFDerivAt_timeDependentFlowOf hX hp₁).hasDerivAt_extChartAt_comp hp₂).congr_deriv
      hV.symm
  exact hasDerivAt_fderiv_of_eventually_hasDerivAt
    (Y := fun u q ↦ VectorField.mpullbackWithin 𝓘(ℝ, E) I e.symm (X u) (range I) q)
    (hX.contMDiffAt.contDiffAt_uncurry_mpullbackWithin_extChartAt_symm
      (n := 2) (by norm_num) hz₀) hψc hψ₀ hψ

/-- **The variational equation of a time-dependent flow, in a chart.** Let `X` be a jointly `C¹`
time-dependent vector field on a `C²` boundaryless manifold modelled on a finite-dimensional space,
and let `e = extChartAt I z` be an extended chart whose source contains `Φ_{s,t} x`, where
`Φ = timeDependentFlowOf X` and `((s, t), x)` lies in the domain of the flow. Then the chart
readings `u ↦ d(e ∘ Φ_{s,u})_x` of the differentials of the flow solve, at time `t`, the linear
equation `J' = DX^e_t(e(Φ_{s,t} x)) J`, where `X^e_t` is the chart expression of `X t`. -/
theorem hasDerivAt_mfderiv_extChartAt_comp_timeDependentFlowOf
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hz : timeDependentFlowOf X s t x ∈ (extChartAt I z).source) :
    HasDerivAt
      (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ timeDependentFlowOf X s u) x : E →L[ℝ] E))
      ((fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I z).symm (X t) (range I))
          (extChartAt I z (timeDependentFlowOf X s t x))).comp
        (mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ timeDependentFlowOf X s t) x)) t := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  set e := extChartAt I z
  set y := timeDependentFlowOf X s t x
  set ψ : ℝ → E → E := fun u q ↦ e (timeDependentFlowOf X t u (e.symm q))
  set L : E →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (e ∘ timeDependentFlowOf X s t) x
  have hdom := isOpen_timeDependentFlowDomain hX
  have hz₀ : e y ∈ e.target := e.map_source hz
  have hyy : e.symm (e y) = y := e.left_inv hz
  have hyt : ((t, t), y) ∈ timeDependentFlowDomain X := mem_timeDependentFlowDomain_self hX t y
  have hΦst := mdifferentiableAt_timeDependentFlowOf hX h
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm (e y) :=
    ((contMDiffOn_extChartAt_symm (n := 1) z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds hz₀)).mdifferentiableAt one_ne_zero
  have hu₁ : ∀ᶠ u in 𝓝 t, ((t, u), y) ∈ timeDependentFlowDomain X :=
    (continuousAt_const.prodMk continuousAt_id |>.prodMk continuousAt_const).preimage_mem_nhds
      (hdom.mem_nhds hyt)
  have hu₂ : ∀ᶠ u in 𝓝 t, timeDependentFlowOf X t u y ∈ e.source :=
    (hasMFDerivAt_timeDependentFlowOf hX hyt).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source z).mem_nhds (by rwa [timeDependentFlowOf_self]))
  -- Near `t`, the flow from `s` is the flow from `t` after the flow from `s` to `t`, so its chart
  -- reading is that of the flow from `t`, read in the chart, after the chart reading at time `t`.
  have hrel : (fun u ↦ (mfderiv I 𝓘(ℝ, E) (e ∘ timeDependentFlowOf X s u) x : E →L[ℝ] E))
      =ᶠ[𝓝 t] fun u ↦ (fderiv ℝ (ψ u) (e y)).comp L := by
    filter_upwards [hu₁, hu₂] with u hu₁ hu₂
    have hψu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ u) (e y) :=
      (mdifferentiableAt_extChartAt (by rw [hyy]; simpa only [e, extChartAt_source] using hu₂)).comp
        (e y) ((mdifferentiableAt_timeDependentFlowOf hX (by rwa [hyy])).comp (e y) hsymm)
    have heq : e ∘ timeDependentFlowOf X s u =ᶠ[𝓝 x] ψ u ∘ (e ∘ timeDependentFlowOf X s t) := by
      have hx₁ : ∀ᶠ p in 𝓝 x, ((s, t), p) ∈ timeDependentFlowDomain X :=
        (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hdom.mem_nhds h)
      have hx₂ : ∀ᶠ p in 𝓝 x,
          ((t, u), timeDependentFlowOf X s t p) ∈ timeDependentFlowDomain X :=
        (continuousAt_const.prodMk hΦst.continuousAt).preimage_mem_nhds (hdom.mem_nhds hu₁)
      have hx₃ : ∀ᶠ p in 𝓝 x, timeDependentFlowOf X s t p ∈ e.source :=
        hΦst.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source z).mem_nhds hz)
      filter_upwards [hx₁, hx₂, hx₃] with p hp₁ hp₂ hp₃
      simp only [comp_apply, ψ, e.left_inv hp₃, (timeDependentFlowOf_trans_of_mem hX hp₁ hp₂).2]
    rw [heq.mfderiv_eq, mfderiv_comp x hψu
      ((mdifferentiableAt_extChartAt (by simpa [e] using hz)).comp x hΦst), mfderiv_eq_fderiv]
    rfl
  have hfinal := (hasDerivAt_fderiv_extChartAt_timeDependentFlowOf_extChartAt_symm hX hz).clm_comp
    (hasDerivAt_const t L)
  rw [ContinuousLinearMap.comp_zero, add_zero] at hfinal
  exact hfinal.congr_of_eventuallyEq hrel

/-- **The variational equation of a time-dependent flow, applied to a tangent vector.** In the
setting of `TauCeti.hasDerivAt_mfderiv_extChartAt_comp_timeDependentFlowOf`, the chart coordinates
`J(u) = de(dΦ_{s,u} w)` of the image of a tangent vector `w` at `x` under the differentials of the
flow satisfy `J'(t) = DX^e_t(e(Φ_{s,t} x)) J(t)`. -/
theorem hasDerivAt_mfderiv_extChartAt_timeDependentFlowOf_apply
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hz : timeDependentFlowOf X s t x ∈ (extChartAt I z).source) (w : TangentSpace I x) :
    HasDerivAt (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (timeDependentFlowOf X s u x)
        (mfderiv I I (timeDependentFlowOf X s u) x w) : E))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I z).symm (X t) (range I))
          (extChartAt I z (timeDependentFlowOf X s t x))
        (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (timeDependentFlowOf X s t x)
          (mfderiv I I (timeDependentFlowOf X s t) x w))) t := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  -- The chain rule for the chart reading, wherever the flow is defined and lands in the chart.
  set w' : E := w
  have hchain : (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ timeDependentFlowOf X s u) x w' : E))
      =ᶠ[𝓝 t] fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (timeDependentFlowOf X s u x)
        (mfderiv I I (timeDependentFlowOf X s u) x w) : E) := by
    have hu₁ : ∀ᶠ u in 𝓝 t, ((s, u), x) ∈ timeDependentFlowDomain X :=
      (continuousAt_const.prodMk continuousAt_id |>.prodMk continuousAt_const).preimage_mem_nhds
        ((isOpen_timeDependentFlowDomain hX).mem_nhds h)
    have hu₂ : ∀ᶠ u in 𝓝 t, timeDependentFlowOf X s u x ∈ (extChartAt I z).source :=
      (hasMFDerivAt_timeDependentFlowOf hX h).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source z).mem_nhds hz)
    filter_upwards [hu₁, hu₂] with u hu₁ hu₂
    exact mfderiv_comp_apply x (mdifferentiableAt_extChartAt (by simpa using hu₂))
      (mdifferentiableAt_timeDependentFlowOf hX hu₁) w
  -- Evaluation at `w` is linear, so the operator equation gives the equation for `J`.
  have hd := (ContinuousLinearMap.apply ℝ E w').hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mfderiv_extChartAt_comp_timeDependentFlowOf hX h hz)
  have hA := congrArg (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I z).symm
    (X t) (range I)) (extChartAt I z (timeDependentFlowOf X s t x))) hchain.self_of_nhds
  exact (hd.congr_deriv hA).congr_of_eventuallyEq hchain.symm

end TimeDependent

section Autonomous

variable {v : (x : M) → TangentSpace I x}
  (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {t : ℝ} {x z : M}
include hv

/-- Near a point `(t, x)` of the domain of the flow of `v`, its time maps are those of the
time-dependent flow of the time-independent field `v` from time `0`. -/
private theorem eventually_flowOf_eventuallyEq_timeDependentFlowOf (h : (t, x) ∈ flowDomain v) :
    ∀ᶠ u in 𝓝 t, flowOf v u =ᶠ[𝓝 x] timeDependentFlowOf (fun _ ↦ v) 0 u := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have hmem : ∀ᶠ p in 𝓝 t ×ˢ 𝓝 x, p ∈ flowDomain v := by
    rw [← nhds_prod_eq]
    exact (isOpen_flowDomain hv).mem_nhds h
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := eventually_prod_iff.1 hmem
  filter_upwards [hpa] with u hu
  filter_upwards [hpb] with p hp
  have hup := timeDependentFlowOf_const_eq_flowOf hv (s := 0) (t := u) (x := p)
    (by simpa using hP hu hp)
  rw [hup.2, sub_zero]

/-- **The variational equation of an autonomous flow, in a chart.** Let `v` be a `C¹` vector field
on a `C²` boundaryless manifold modelled on a finite-dimensional space, `(t, x)` a point of the
domain of its flow `φ = flowOf v`, and `e = extChartAt I z` an extended chart whose source
contains `φ_t x`. Then the chart readings `u ↦ d(e ∘ φ_u)_x` of the differentials of the flow
solve, at time `t`, the linear equation `J' = Dv^e(e(φ_t x)) J`, where `v^e` is the chart expression
of `v`. -/
theorem hasDerivAt_mfderiv_extChartAt_comp_flowOf (h : (t, x) ∈ flowDomain v)
    (hz : flowOf v t x ∈ (extChartAt I z).source) :
    HasDerivAt (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ flowOf v u) x : E →L[ℝ] E))
      ((fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I z).symm v (range I))
          (extChartAt I z (flowOf v t x))).comp
        (mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ flowOf v t) x)) t := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, v p.2⟩ : TangentBundle I M)) :=
    hv.comp contMDiff_snd
  let F : ℝ → E →L[ℝ] E := fun u ↦
    mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ timeDependentFlowOf (fun _ ↦ v) 0 u) x
  have hmf : (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z ∘ flowOf v u) x : E →L[ℝ] E))
      =ᶠ[𝓝 t] F := by
    filter_upwards [eventually_flowOf_eventuallyEq_timeDependentFlowOf hv h] with u hu
    -- The cast between the tangent spaces of the model space at the two equal points is the
    -- identity.
    rw [(hu.fun_comp (extChartAt I z)).mfderiv_eq]
    rfl
  obtain ⟨h', heq⟩ := timeDependentFlowOf_const_eq_flowOf hv (s := 0) (t := t) (x := x)
    (by simpa using h)
  rw [sub_zero] at heq
  have hmain := hasDerivAt_mfderiv_extChartAt_comp_timeDependentFlowOf hX h' (heq ▸ hz)
  refine (hmain.congr_deriv ?_).congr_of_eventuallyEq hmf
  exact congrArg₂ (fun q (L : E →L[ℝ] E) ↦ (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I
    (extChartAt I z).symm v (range I)) q).comp L) (by rw [heq]) hmf.self_of_nhds.symm

/-- **The variational equation of an autonomous flow, applied to a tangent vector.** In the setting
of `TauCeti.hasDerivAt_mfderiv_extChartAt_comp_flowOf`, the chart coordinates `J(u) = de(dφ_u w)`
of the image of a tangent vector `w` at `x` under the differentials of the flow satisfy
`J'(t) = Dv^e(e(φ_t x)) J(t)`. -/
theorem hasDerivAt_mfderiv_extChartAt_flowOf_apply (h : (t, x) ∈ flowDomain v)
    (hz : flowOf v t x ∈ (extChartAt I z).source) (w : TangentSpace I x) :
    HasDerivAt (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (flowOf v u x)
        (mfderiv I I (flowOf v u) x w) : E))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I z).symm v (range I))
          (extChartAt I z (flowOf v t x))
        (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (flowOf v t x) (mfderiv I I (flowOf v t) x w))) t := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, v p.2⟩ : TangentBundle I M)) :=
    hv.comp contMDiff_snd
  have hev := eventually_flowOf_eventuallyEq_timeDependentFlowOf hv h
  have hJ : (fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (flowOf v u x)
      (mfderiv I I (flowOf v u) x w) : E)) =ᶠ[𝓝 t]
      fun u ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z) (timeDependentFlowOf (fun _ ↦ v) 0 u x)
        (mfderiv I I (timeDependentFlowOf (fun _ ↦ v) 0 u) x w) : E) := by
    filter_upwards [hev] with u hu
    -- The cast between the tangent spaces at the two equal points is the identity.
    have hmf : (mfderiv I I (flowOf v u) x : E →L[ℝ] E) =
        mfderiv I I (timeDependentFlowOf (fun _ ↦ v) 0 u) x := by
      rw [hu.mfderiv_eq]
      rfl
    exact congrArg₂ (fun (q : M) (J : E) ↦ (mfderiv I 𝓘(ℝ, E) (extChartAt I z) q J : E))
      hu.self_of_nhds (congrArg (fun L : E →L[ℝ] E ↦ L w) hmf)
  obtain ⟨h', heq⟩ := timeDependentFlowOf_const_eq_flowOf hv (s := 0) (t := t) (x := x)
    (by simpa using h)
  rw [sub_zero] at heq
  have hmain := hasDerivAt_mfderiv_extChartAt_timeDependentFlowOf_apply hX h' (heq ▸ hz) w
  refine (hmain.congr_deriv ?_).congr_of_eventuallyEq hJ
  exact congrArg₂ (fun q (J : E) ↦ fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I
    (extChartAt I z).symm v (range I)) q J) (by rw [heq]) hJ.self_of_nhds.symm

end Autonomous

end TauCeti
