/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Geometry.Manifold.Flow.Basic

/-!
# Integrals along trajectories and the transport equation

Let `v` be a vector field on a manifold `M`, with maximal flow `φ` (`TauCeti.flowOf`), and let
`f : M → F` be a function with values in a Banach space. The **trajectory integral**

`I(t, x) = ∫₀ᵗ f(φₛ x) ds`

(`TauCeti.flowIntegral v f t x`) integrates `f` along the trajectory of `v` through `x`. On the
domain of the flow it vanishes at `t = 0`, has time derivative `f(φₜ x)`
(`TauCeti.hasDerivAt_flowIntegral`), and is additive along trajectories,
`I(s + t, x) = I(s, x) + I(t, φₛ x)` (`TauCeti.flowIntegral_add`). It is as regular as `v` and `f`
jointly in time and point (`TauCeti.contMDiffOn_flowIntegral`): adjoining the equation `r' = f(x)`
to `x' = v(x)` gives the vector field `(r, x) ↦ (f x, v x)` on `F × M`, whose flow is
`(r, x) ↦ (r + I(t, x), φₜ x)`, and the flow of a smooth field is smooth.

The trajectory integral solves the **transport equation** `v h = f`, that is `dh(v) = f`, with
prescribed zero values on a hypersurface. Let `ι : S → M` be a map and let `e` be a partial
diffeomorphism from an open subset of `ℝ × S` onto an open subset of `M` that agrees there with the
flow-out `(t, s) ↦ φₜ(ι s)` of `ι`; by the flow-out theorem this is the situation near a
hypersurface to which `v` is transverse. Reading the trajectory integral in the coordinates `e`
gives the function `h(φₜ(ι s)) = ∫₀ᵗ f(φᵤ(ι s)) du` on the target of `e`, which is as regular as
`v` and `f`, vanishes at the points `ι s` with `(0, s)` in the source of `e`, and satisfies
`dh(v) = f` (`TauCeti.exists_mvfderiv_apply_eq_of_flowOut`).

This is how the Reeb-direction equation `R_α h = β(R_α)` of the strict contact Moser method is
solved near a hypersurface transverse to the Reeb field.

## Main definitions

* `TauCeti.flowIntegral v f t x`: the integral of `f` along the trajectory of `v` through `x`
  from time `0` to time `t`.

## Main results

* `TauCeti.hasDerivAt_flowIntegral`: its time derivative is `f(φₜ x)`.
* `TauCeti.flowIntegral_add`: additivity along trajectories.
* `TauCeti.contMDiffOn_flowIntegral`: joint `C^n` regularity on the domain of the flow.
* `TauCeti.exists_mvfderiv_apply_eq_of_flowOut`: the transport equation `dh(v) = f`, with zero
  values on a hypersurface, has a `C^n` solution on the image of a flow-out chart.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9 (flows, the flow-out theorem, and first-order partial differential
  equations solved along a flow-out).
-/

public section

noncomputable section

open Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **trajectory integral** `∫₀ᵗ f(φₛ x) ds` of `f` along the trajectory of the vector field
`v` through `x`, where `φ` is the maximal flow of `v`. It is meaningful for `(t, x)` in the domain
of the flow, where it solves `∂ₜ I = f ∘ φₜ` (`TauCeti.hasDerivAt_flowIntegral`). -/
def flowIntegral (v : (x : M) → TangentSpace I x) (f : M → F) (t : ℝ) (x : M) : F :=
  ∫ s in (0 : ℝ)..t, f (flowOf v s x)

/-- The trajectory integral is the interval integral of `f` along the trajectory. -/
theorem flowIntegral_def (v : (x : M) → TangentSpace I x) (f : M → F) (t : ℝ) (x : M) :
    flowIntegral v f t x = ∫ s in (0 : ℝ)..t, f (flowOf v s x) :=
  (rfl)

/-- The trajectory integral vanishes at time `0`. -/
@[simp]
theorem flowIntegral_zero (v : (x : M) → TangentSpace I x) (f : M → F) (x : M) :
    flowIntegral v f 0 x = 0 :=
  intervalIntegral.integral_same

variable [CompleteSpace E] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x} {f : M → F}

variable [CompleteSpace F]

/-- **The time derivative of the trajectory integral** is the value of `f` at the current point:
`∂ₜ ∫₀ᵗ f(φₛ x) ds = f(φₜ x)`, for a continuous `f` and a time `t` of the flow domain. -/
theorem hasDerivAt_flowIntegral (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hf : Continuous f) {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) :
    HasDerivAt (fun s ↦ flowIntegral v f s x) (f (flowOf v t x)) t := by
  have hcont : ContinuousOn (fun s ↦ f (flowOf v s x)) {s | (s, x) ∈ flowDomain v} :=
    hf.comp_continuousOn (isMIntegralCurveOn_flowOf hv x).continuousOn
  have hopen : IsOpen {s | (s, x) ∈ flowDomain v} :=
    isOpen_setOf_mem_flowDomain hv continuous_id continuous_const
  exact intervalIntegral.integral_hasDerivAt_right
    ((hcont.mono (uIcc_subset_setOf_mem_flowDomain ht)).intervalIntegrable)
    (hcont.stronglyMeasurableAtFilter hopen t ht) (hcont.continuousAt (hopen.mem_nhds ht))

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Additivity of the trajectory integral.** If time `s` is defined at `x` and time `t` is
defined at `φₛ x`, then `∫₀^(s+t) f(φᵤ x) du = ∫₀ˢ f(φᵤ x) du + ∫₀ᵗ f(φᵤ(φₛ x)) du`. -/
theorem flowIntegral_add (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hf : Continuous f) {s t : ℝ} {x : M} (hs : (s, x) ∈ flowDomain v)
    (ht : (t, flowOf v s x) ∈ flowDomain v) :
    flowIntegral v f (s + t) x = flowIntegral v f s x + flowIntegral v f t (flowOf v s x) := by
  have hst := (flowOf_add hv hs ht).1
  have hcont : ContinuousOn (fun u ↦ f (flowOf v u x)) {u | (u, x) ∈ flowDomain v} :=
    hf.comp_continuousOn (isMIntegralCurveOn_flowOf hv x).continuousOn
  -- The integral from `s` to `s + t` along the trajectory through `x` is the integral from `0`
  -- to `t` along the trajectory through `φₛ x`.
  have hshift : ∫ u in s..s + t, f (flowOf v u x) = flowIntegral v f t (flowOf v s x) := by
    have h := intervalIntegral.integral_comp_add_left (fun u ↦ f (flowOf v u x)) s (a := 0)
      (b := t)
    rw [add_zero] at h
    rw [← h, flowIntegral_def]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [(flowOf_add hv hs (uIcc_subset_setOf_mem_flowDomain ht hu)).2]
  rw [flowIntegral_def, flowIntegral_def, ← intervalIntegral.integral_add_adjacent_intervals
    ((hcont.mono (uIcc_subset_setOf_mem_flowDomain hs)).intervalIntegrable)
    ((hcont.mono
      ((ordConnected_setOf_mem_flowDomain v x).uIcc_subset hs hst)).intervalIntegrable), hshift]

/-! ### Joint regularity -/

/-- The vector field `(r, x) ↦ (f x, v x)` on `F × M`: the equation `x' = v x` with the equation
`r' = f x` of the trajectory integral adjoined. -/
private def integralField (v : (x : M) → TangentSpace I x) (f : M → F) :
    (p : F × M) → TangentSpace (𝓘(ℝ, F).prod I) p :=
  fun p ↦ (f p.2, v p.2)

omit [CompleteSpace E] [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
  [CompleteSpace F] in
/-- The field `(f, v)` at `p` is `(f p.2, v p.2)`. -/
private theorem integralField_apply (v : (x : M) → TangentSpace I x) (f : M → F) (p : F × M) :
    integralField v f p = (f p.2, v p.2) :=
  rfl

omit [CompleteSpace E] [T2Space M] [BoundarylessManifold I M] [CompleteSpace F] in
/-- The field `(f, v)` is as regular as `v` and `f`. -/
private theorem contMDiff_integralField {n : ℕ∞}
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hf : ContMDiff I 𝓘(ℝ, F) n f) :
    ContMDiff (𝓘(ℝ, F).prod I) (𝓘(ℝ, F).prod I).tangent n
      (fun p : F × M ↦ (⟨p, integralField v f p⟩ : TangentBundle (𝓘(ℝ, F).prod I) (F × M))) := by
  have h₁ : ContMDiff (𝓘(ℝ, F).prod I) 𝓘(ℝ, F).tangent n
      (fun p : F × M ↦ (⟨p.1, f p.2⟩ : TangentBundle 𝓘(ℝ, F) F)) := by
    -- The tangent bundle of the model space `F` is `F × F`: by
    -- `tangentBundleModelSpaceHomeomorph_coe_symm` the inverse homeomorphism is
    -- `(TotalSpace.toProd F F).symm`, which sends `(a, b)` to `⟨a, b⟩` by definition. The fibre
    -- `TangentSpace 𝓘(ℝ, F) a` is `F` only definitionally, so `Equiv.symm_apply_eq` cannot rewrite.
    have hg : ContMDiff (𝓘(ℝ, F).prod I) 𝓘(ℝ, F × F) n (fun p : F × M ↦ (p.1, f p.2)) :=
      contMDiff_fst.prodMk_space (hf.comp contMDiff_snd)
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, F)) (n := n)).comp hg
  refine ((contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, F)) (M := F) (I' := I)
    (M' := M)).comp (h₁.prodMk (hv.comp contMDiff_snd))).congr fun p ↦ ?_
  rw [Function.comp_apply, eq_comm, Equiv.symm_apply_eq, equivTangentBundleProd_apply,
    integralField_apply]
  simp only [Function.comp_apply]

/-- On an open interval of times of the flow domain at `x`, the curve
`σ ↦ (r + I(σ, x), φ_σ x)` is an integral curve of the field `(f, v)`. -/
private theorem isMIntegralCurveOn_integralField
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hf : Continuous f) (r : F)
    {x : M} {a b : ℝ} (hab : Ioo a b ⊆ {s | (s, x) ∈ flowDomain v}) :
    IsMIntegralCurveOn (fun σ ↦ (r + flowIntegral v f σ x, flowOf v σ x)) (integralField v f)
      (Ioo a b) := by
  intro σ hσ
  have hdom : (σ, x) ∈ flowDomain v := hab hσ
  have h₂ : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ flowOf v s x) σ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (flowOf v σ x))) :=
    ((isMIntegralCurveOn_flowOf hv x).isMIntegralCurveAt
      ((isOpen_setOf_mem_flowDomain hv continuous_id continuous_const).mem_nhds hdom)).hasMFDerivAt
  have h₁ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun s ↦ r + flowIntegral v f s x) σ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f (flowOf v σ x))) :=
    hasMFDerivAt_iff_hasFDerivAt.2 ((hasDerivAt_flowIntegral hv hf hdom).const_add r).hasFDerivAt
  -- Both derivatives send `a` to `(a • f (φ_σ x), a • v (φ_σ x))`: after unfolding the field,
  -- the two sides agree by `ContinuousLinearMap.prod_apply` and `smulRight_apply`, with the
  -- tangent space of `F × M` definitionally the product of tangent spaces.
  refine ((h₁.prodMk h₂).congr_mfderiv (ContinuousLinearMap.ext fun a ↦ ?_)).hasMFDerivWithinAt
  rw [integralField_apply]
  rfl

/-- **The flow of the field `(f, v)`.** Where the flow of `v` is defined, so is that of `(f, v)`,
and it is `(r, x) ↦ (r + I(t, x), φₜ x)`. -/
private theorem flowOf_integralField
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) (r : F) :
    (t, (r, x)) ∈ flowDomain (integralField v f) ∧
      flowOf (integralField v f) t (r, x) = (r + flowIntegral v f t x, flowOf v t x) := by
  obtain ⟨γ, a, b, hγ, hγ0, h0, htab, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq (mem_flowDomain.mp ht)
  have hab : Ioo a b ⊆ {s | (s, x) ∈ flowDomain v} := fun s hs ↦
    mem_flowDomain.mpr (hγ.subset_maximalIntegralCurveInterval h0 hγ0 hs)
  have hc := isMIntegralCurveOn_integralField hv hf.continuous r hab
  have hc0 : (fun σ ↦ (r + flowIntegral v f σ x, flowOf v σ x)) 0 = (r, x) := by
    simp
  refine ⟨mem_flowDomain.mpr (hc.subset_maximalIntegralCurveInterval h0 hc0 htab), ?_⟩
  rw [flowOf_apply]
  exact hc.eqOn_maximalIntegralCurve (contMDiff_integralField hv hf) h0 hc0 htab

/-- **The trajectory integral is jointly regular.** For a `C^n` vector field `v` and a `C^n`
function `f`, `1 ≤ n`, the trajectory integral `(t, x) ↦ ∫₀ᵗ f(φₛ x) ds` is `C^n` on the domain
of the flow of `v`. -/
theorem contMDiffOn_flowIntegral {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hf : ContMDiff I 𝓘(ℝ, F) n f) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n (fun p : ℝ × M ↦ flowIntegral v f p.1 p.2)
      (flowDomain v) := by
  have hv₁ : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) := hv.of_le (by exact_mod_cast hn)
  have hf₁ : ContMDiff I 𝓘(ℝ, F) 1 f := hf.of_le (by exact_mod_cast hn)
  intro p hp
  -- Near `p`, the trajectory integral is the first component of the flow of `(f, v)` from
  -- `(0, x)`, which is `C^n`.
  have hflow : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n
      (fun q : ℝ × M ↦ (flowOf (integralField v f) q.1 ((0 : F), q.2)).1) p :=
    contMDiffAt_fst.comp p (contMDiffAt_flowOf_comp hn (contMDiff_integralField hv hf)
      contMDiffAt_fst (contMDiffAt_const.prodMk contMDiffAt_snd)
      (flowOf_integralField hv₁ hf₁ hp 0).1)
  refine (hflow.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(isOpen_flowDomain hv₁).mem_nhds hp] with q hq
  rw [(flowOf_integralField hv₁ hf₁ hq 0).2, zero_add]

/-! ### The transport equation -/

/-- **The transport equation along a flow-out.** Let `v` be a `C^n` vector field and `f` a `C^n`
function, `1 ≤ n`, let `ι : S → M` be a `C^n` map, and let `e` be a `C^n` partial diffeomorphism
from `ℝ × S` to `M` that agrees on its source with the flow-out `(t, s) ↦ φₜ(ι s)`. Then there is
a function `h`, `C^n` on the target of `e`, with `h(φₜ(ι s)) = ∫₀ᵗ f(φᵤ(ι s)) du` for `(t, s)` in
the source, so that `h` vanishes at `ι s` when `(0, s)` is in the source, and which solves the
transport equation `dh(v) = f` on the target. -/
theorem exists_mvfderiv_apply_eq_of_flowOut {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hv : CMDiff n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hf : ContMDiff I 𝓘(ℝ, F) n f)
    {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] {ι : S → M}
    (hι : ContMDiff J I n ι) (e : PartialDiffeomorph (𝓘(ℝ, ℝ).prod J) I (ℝ × S) M n)
    (he : ∀ p ∈ e.source, (p.1, ι p.2) ∈ flowDomain v ∧ e p = flowOf v p.1 (ι p.2)) :
    ∃ h : M → F, ContMDiffOn I 𝓘(ℝ, F) n h e.target ∧
      (∀ p ∈ e.source, h (e p) = flowIntegral v f p.1 (ι p.2)) ∧
      (∀ s, ((0 : ℝ), s) ∈ e.source → h (ι s) = 0) ∧
      ∀ x ∈ e.target, mvfderiv I h x (v x) = f x := by
  have hv₁ : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) := hv.of_le (by exact_mod_cast hn)
  have hf₁ : ContMDiff I 𝓘(ℝ, F) 1 f := hf.of_le (by exact_mod_cast hn)
  set G : ℝ × S → F := fun q ↦ flowIntegral v f q.1 (ι q.2) with hG
  have hGsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, F) n G e.source :=
    (contMDiffOn_flowIntegral hn hv hf).comp
      (contMDiff_fst.prodMk (hι.comp contMDiff_snd)).contMDiffOn fun q hq ↦ (he q hq).1
  have hGe (p : ℝ × S) (hp : p ∈ e.source) : G (e.toPartialEquiv.symm (e p)) = G p :=
    congrArg G (e.toPartialEquiv.left_inv hp)
  have hsmooth : ContMDiffOn I 𝓘(ℝ, F) n (G ∘ e.toPartialEquiv.symm) e.target :=
    hGsmooth.comp e.contMDiffOn_invFun fun x hx ↦ e.toPartialEquiv.map_target hx
  refine ⟨G ∘ e.toPartialEquiv.symm, hsmooth, fun p hp ↦ hGe p hp, fun s hs ↦ ?_,
    fun x hx ↦ ?_⟩
  · have h0 : e (0, s) = ι s := by rw [(he _ hs).2, flowOf_zero]
    rw [← h0, comp_apply, hGe _ hs]
    simp only [hG, flowIntegral_zero]
  · -- Write `x = φ_t(ι s)` with `(t, s) = e⁻¹ x`.
    set p := e.toPartialEquiv.symm x
    have hps : p ∈ e.source := e.toPartialEquiv.map_target hx
    have hxp : e p = x := e.toPartialEquiv.right_inv hx
    obtain ⟨hpdom, hpe⟩ := he p hps
    -- Along the trajectory through `x`, `h(φ_σ x) = I(t, ι s) + I(σ, x)` for small `σ`.
    have hev : (fun σ ↦ (G ∘ e.toPartialEquiv.symm) (flowOf v σ x)) =ᶠ[𝓝 0]
        fun σ ↦ flowIntegral v f p.1 (ι p.2) + flowIntegral v f σ x := by
      have h₁ : ∀ᶠ σ in 𝓝 (0 : ℝ), (p.1 + σ, p.2) ∈ e.source :=
        (Continuous.prodMk (continuous_const.add continuous_id) continuous_const).continuousAt
          |>.preimage_mem_nhds (e.open_source.mem_nhds (by simpa using hps))
      have h₂ : ∀ᶠ σ in 𝓝 (0 : ℝ), (σ, x) ∈ flowDomain v :=
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
          ((isOpen_flowDomain hv₁).mem_nhds (mem_flowDomain_zero hv₁ x))
      filter_upwards [h₁, h₂] with σ hσ₁ hσ₂
      rw [← hxp, hpe] at hσ₂ ⊢
      have hadd := flowOf_add hv₁ hpdom hσ₂
      rw [hadd.2, ← (he _ hσ₁).2, comp_apply, hGe _ hσ₁, hG]
      exact flowIntegral_add hv₁ hf₁.continuous hpdom hσ₂
    have hderiv : HasDerivAt (fun σ ↦ (G ∘ e.toPartialEquiv.symm) (flowOf v σ x)) (f x) 0 := by
      have h := (hasDerivAt_flowIntegral hv₁ hf₁.continuous (mem_flowDomain_zero hv₁ x)).const_add
        (flowIntegral v f p.1 (ι p.2))
      rw [flowOf_zero] at h
      exact h.congr_of_eventuallyEq hev
    have hmd : MDifferentiableAt I 𝓘(ℝ, F) (G ∘ e.toPartialEquiv.symm) (flowOf v 0 x) := by
      rw [flowOf_zero]
      exact (hsmooth.contMDiffAt (e.open_target.mem_nhds hx)).mdifferentiableAt
        (by simpa using (lt_of_lt_of_le zero_lt_one hn).ne')
    have hcomp := hasDerivAt_comp_flowOf hv₁ (mem_flowDomain_zero hv₁ x) hmd
    rw [flowOf_zero] at hcomp
    exact hcomp.unique hderiv

end TauCeti
