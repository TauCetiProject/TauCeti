/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.PDE.HeatKernel.Resolvent
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Laplacian
public import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakLaplacianLp
import TauCeti.Analysis.PDE.HeatKernel.Generator
import TauCeti.Analysis.PDE.Regularity.Hessian.Poisson
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# `W^{2,p}` solutions of `u - Δu = f` on the whole space

Let `E` be a finite-dimensional real inner product space and `1 < p < ∞`. This file shows that
`1 - Δ` is an isomorphism of Banach spaces

`W^{2,p}(E) ≃ Lᵖ(E)`, `w ↦ w - tr D²w`

(`TauCeti.Wkp.oneSubLaplacianEquiv`), where `D²w` is the weak Hessian, and that its inverse is
convolution with the heat resolvent kernel `G₁ = ∫₀^∞ e^{-t} K_t dt`
(`TauCeti.Wkp.value_oneSubLaplacianEquiv_symm_ae`).

This is the solution operator used to upgrade the integrability of strong solutions of
nondivergence equations (Gilbarg–Trudinger, Lemma 9.16): an equation whose principal coefficient
is close to the identity is a small perturbation of `u - Δu = f`, and the solution operator
`(1 - Δ)⁻¹` acts on every `Lᵖ`, `1 < p < ∞`, by the same convolution. So the perturbed equation can
be solved by a contraction in `W^{2,p}` and in `W^{2,r}` simultaneously, with the same iterates.

## The argument

The convolution `G₁ ⋆ f` is the resolvent `(1 - A)⁻¹ f` of the generator `A` of the heat semigroup
on `Lᵖ` (`TauCeti.isResolventAt_generator_heatSemigroup`), and `A` is the distributional Laplacian
on its natural domain `{f ∈ Lᵖ : Δf ∈ Lᵖ}` (`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`).
So `v = G₁ ⋆ f` lies in `Lᵖ` with `Δv = v - f ∈ Lᵖ` in the sense of distributions, and by
`W^{2,p}` regularity for Poisson's equation
(`TauCeti.exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq`) it is the value of an element
`w` of `W^{2,p}(E)` with `tr D²w = v - f`: `1 - Δ` is onto. Conversely, for `w ∈ W^{2,p}(E)` the
trace of the weak Hessian is the distributional Laplacian of `w`, so `(w, tr D²w)` lies on the
graph of `A`, and `(1 - A)⁻¹ (w - tr D²w) = w`. In particular `1 - Δ` is injective, and its inverse
is bounded by the open mapping theorem.

## Main declarations

* `TauCeti.Wkp.oneSubLaplacianL`: the bounded operator `w ↦ w - tr D²w` from `W^{2,p}(E)` to
  `Lᵖ(E)`, which is `w - Δw` for the weak Laplacian
  (`TauCeti.Wkp.oneSubLaplacianL_eq_value_sub_laplacianL`).
* `TauCeti.Wkp.heatResolventKernel_convolution_oneSubLaplacianL_ae_eq`: `G₁ ⋆ (w - tr D²w) = w`.
* `TauCeti.Wkp.oneSubLaplacianL_injective`, `TauCeti.Wkp.oneSubLaplacianL_surjective`: `1 - Δ` is
  a bijection for `1 < p < ∞`.
* `TauCeti.Wkp.oneSubLaplacianEquiv`: `1 - Δ` as an isomorphism `W^{2,p}(E) ≃L[ℝ] Lᵖ(E)`.
* `TauCeti.Wkp.value_oneSubLaplacianEquiv_symm_ae`: its inverse is convolution with `G₁`.
* `TauCeti.exists_wkp_value_ae_eq_heatResolventKernel_convolution`: for `f ∈ Lᵖ(E)`, `G₁ ⋆ f` is
  the value of an element `w` of `W^{2,p}(E)` solving `w - tr D²w = f`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9, Lemma 9.16 and §9.5.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §3.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory TopologicalSpace
open scoped Convolution ENNReal Laplacian

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞}

/-- An element of `Lᵖ` of the volume restricted to the whole space, as a class in `Lᵖ(E)`. -/
private def toVolumeLp (g : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E))) :
    Lp ℝ p (volume : Measure E) :=
  ((Lp.memLp g).mono_measure (Measure.restrict_coe_opens_top (volume : Measure E)).ge).toLp g

/-- The class `TauCeti.toVolumeLp g` is represented by `g`. -/
private theorem coeFn_toVolumeLp (g : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E))) :
    (toVolumeLp g : E → ℝ) =ᵐ[volume] g :=
  MemLp.coeFn_toLp _

variable [Fact (1 ≤ p)]

namespace Wkp

/-- **The operator `1 - Δ` on `W^{2,p}(E)`**: `w ↦ w - tr D²w`, where `D²w` is the weak Hessian. -/
def oneSubLaplacianL :
    Wkp (volume : Measure E) ⊤ p 2 →L[ℝ] Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E)) :=
  valueL 2 - (traceCLM ℝ E).compLpL p _ ∘L iteratedGradientL 1

/-- The defining formula of `TauCeti.Wkp.oneSubLaplacianL`. -/
theorem oneSubLaplacianL_apply (w : Wkp (volume : Measure E) ⊤ p 2) :
    oneSubLaplacianL w = value 2 w - (traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w) := by
  rw [oneSubLaplacianL, _root_.sub_apply, ContinuousLinearMap.comp_apply, valueL_apply,
    iteratedGradientL_apply]

/-- `TauCeti.Wkp.oneSubLaplacianL` sends `w` to the class of `x ↦ w(x) - tr D²w(x)`. -/
theorem oneSubLaplacianL_ae (w : Wkp (volume : Measure E) ⊤ p 2) :
    (oneSubLaplacianL w : E → ℝ) =ᵐ[volume]
      fun x ↦ value 2 w x - LinearMap.trace ℝ E (iteratedGradient 1 w x) := by
  rw [← Measure.ae_restrict_coe_opens_top]
  filter_upwards [Lp.coeFn_sub (value 2 w) ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w)),
    (traceCLM ℝ E).coeFn_compLpL (iteratedGradient 1 w)] with x h₁ h₂
  rw [oneSubLaplacianL_apply, h₁, Pi.sub_apply, h₂, traceCLM_apply]

/-- `TauCeti.Wkp.oneSubLaplacianL` is `1 - Δ` for the weak Laplacian `TauCeti.Wkp.laplacianL`. -/
theorem oneSubLaplacianL_eq_value_sub_laplacianL (w : Wkp (volume : Measure E) ⊤ p 2) :
    oneSubLaplacianL w = value 2 w - value 0 (laplacianL 0 w) := by
  refine Lp.ext ?_
  filter_upwards [(Measure.ae_restrict_coe_opens_top (volume : Measure E)).symm ▸
      oneSubLaplacianL_ae w, Lp.coeFn_sub (value 2 w) (value 0 (laplacianL 0 w)),
    value_laplacianL_zero_ae_eq_trace w] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.sub_apply, h₃]

/-- The value of `w ∈ W^{2,p}(E)` and the trace of its weak Hessian lie on the graph of the
distributional Laplacian on `Lᵖ(E)`. -/
private theorem mem_graph_weakLaplacianLp (w : Wkp (volume : Measure E) ⊤ p 2) :
    (toVolumeLp (value 2 w), toVolumeLp ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w))) ∈
      (weakLaplacianLp E ℝ p).graph := by
  set T := (traceCLM ℝ E).compLpL p ((volume : Measure E).restrict (⊤ : Opens E))
    (iteratedGradient 1 w)
  have hloc : LocallyIntegrableOn (T : E → ℝ) ⊤ volume :=
    (((Lp.memLp T).locallyIntegrable Fact.out).mono_measure
      (Measure.restrict_coe_opens_top (volume : Measure E)).ge).locallyIntegrableOn _
  have htr : (fun x ↦ LinearMap.trace ℝ E (iteratedGradient 1 w x)) =ᵐ[volume.restrict ⊤] T := by
    filter_upwards [(traceCLM ℝ E).coeFn_compLpL (iteratedGradient 1 w)] with x hx
    rw [hx, traceCLM_apply]
  have h := (forall_integral_laplacian_smul_value_eq_iff w hloc).2 htr
  refine mem_graph_weakLaplacianLp_iff.2 fun φ ↦ ?_
  calc ∫ x, Δ (φ : E → ℝ) x • toVolumeLp (value 2 w) x
      = ∫ x, Δ (φ : E → ℝ) x • value 2 w x :=
        integral_congr_ae ((coeFn_toVolumeLp (value 2 w)).mono fun x hx ↦ by simp only [hx])
    _ = ∫ x, (φ : E → ℝ) x • T x := h φ
    _ = ∫ x, φ x • toVolumeLp T x :=
        integral_congr_ae ((coeFn_toVolumeLp T).mono fun x hx ↦ by simp only [hx])

/-- Convolution with the heat resolvent kernel `G₁` is the resolvent of the distributional
Laplacian on `Lᵖ(E)` at `1`. -/
private theorem isResolventAt_weakLaplacianLp (hp_top : p ≠ ⊤) :
    LinearPMap.IsResolventAt (weakLaplacianLp E ℝ p) 1
      (convolutionLp hp_top (heatResolventKernel 1) volume) := by
  rw [← generator_heatSemigroup_eq_weakLaplacianLp hp_top]
  exact isResolventAt_generator_heatSemigroup hp_top one_pos

/-- **Convolution with `G₁` inverts `1 - Δ` on `W^{2,p}(E)`**: for `1 ≤ p < ∞` and
`w ∈ W^{2,p}(E)`, `G₁ ⋆ (w - tr D²w) = w` almost everywhere, where `G₁` is the heat resolvent
kernel at `1`. -/
theorem heatResolventKernel_convolution_oneSubLaplacianL_ae_eq (hp_top : p ≠ ⊤)
    (w : Wkp (volume : Measure E) ⊤ p 2) :
    heatResolventKernel 1 ⋆ (oneSubLaplacianL w : E → ℝ) =ᵐ[volume] value 2 w := by
  set F := toVolumeLp (value 2 w)
  set G := toVolumeLp ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w))
  have hR := ((LinearPMap.isResolventAt_iff_forall_mem_graph.1
    (isResolventAt_weakLaplacianLp (E := E) hp_top)).2 (F, G)) (mem_graph_weakLaplacianLp w)
  have hFG : ((1 : ℝ) • F - G : Lp ℝ p volume) =ᵐ[volume] oneSubLaplacianL w := by
    filter_upwards [Lp.coeFn_sub ((1 : ℝ) • F) G, Lp.coeFn_smul (1 : ℝ) F,
      coeFn_toVolumeLp (value 2 w),
      coeFn_toVolumeLp ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w)),
      (Lp.coeFn_sub (value 2 w) ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w))).filter_mono
        Measure.ae_le_ae_restrict_coe_opens_top] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, one_smul, h₃, h₄, oneSubLaplacianL_apply, h₅,
      Pi.sub_apply]
  rw [← convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _) hFG]
  refine (convolutionLp_ae_eq_convolution_coeFn hp_top (integrable_heatResolventKernel one_pos)
    _).symm.trans ?_
  rw [hR]
  exact coeFn_toVolumeLp _

/-- **`1 - Δ` is injective on `W^{2,p}(E)`**: if `w - tr D²w = 0`, then `w = 0`. -/
theorem oneSubLaplacianL_injective :
    Function.Injective (oneSubLaplacianL (E := E) (p := p)) := by
  refine (injective_iff_map_eq_zero oneSubLaplacianL).2 fun w hw ↦ ?_
  -- The trace of the weak Hessian of `w` is its value, so `(w, 1 • w)` lies on the graph of the
  -- distributional Laplacian.
  set F := toVolumeLp (value 2 w)
  set G := toVolumeLp ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w))
  have hFG : G = (1 : ℝ) • F := by
    refine Lp.ext ?_
    filter_upwards [oneSubLaplacianL_ae w, Lp.coeFn_smul (1 : ℝ) F, coeFn_toVolumeLp (value 2 w),
      coeFn_toVolumeLp ((traceCLM ℝ E).compLpL p _ (iteratedGradient 1 w)),
      ((traceCLM ℝ E).coeFn_compLpL (iteratedGradient 1 w)).filter_mono
        Measure.ae_le_ae_restrict_coe_opens_top,
      (Lp.coeFn_zero ℝ p _).filter_mono Measure.ae_le_ae_restrict_coe_opens_top]
      with x h₁ h₂ h₃ h₄ h₅ h₆
    rw [hw, h₆, Pi.zero_apply, eq_comm, sub_eq_zero] at h₁
    rw [h₂, Pi.smul_apply, one_smul, h₃, h₄, h₅, traceCLM_apply, h₁]
  have hmem : (F, G) ∈ (weakLaplacianLp E ℝ p).graph := mem_graph_weakLaplacianLp w
  rw [hFG] at hmem
  have hF : F = 0 := eq_zero_of_mem_graph_weakLaplacianLp_smul one_pos hmem
  refine ext_ae ((coeFn_toVolumeLp (value 2 w)).symm.trans ?_)
  rw [show toVolumeLp (value 2 w) = 0 from hF, value_zero']
  exact (Lp.coeFn_zero ℝ p _).trans
    ((Lp.coeFn_zero ℝ p _).filter_mono Measure.ae_le_ae_restrict_coe_opens_top).symm

/-- **`1 - Δ` is onto `Lᵖ(E)` from `W^{2,p}(E)`** for `1 < p < ∞`: every `f ∈ Lᵖ(E)` is
`w - tr D²w` for some `w ∈ W^{2,p}(E)`. -/
theorem oneSubLaplacianL_surjective (hp : 1 < p) (hp_top : p ≠ ⊤) :
    Function.Surjective (oneSubLaplacianL (E := E) (p := p)) := by
  intro y
  set y' := toVolumeLp y
  set R := convolutionLp hp_top (heatResolventKernel 1) (volume : Measure E) (F := ℝ)
  have hg := mem_graph_weakLaplacianLp_iff.1 ((LinearPMap.isResolventAt_iff_forall_mem_graph.1
    (isResolventAt_weakLaplacianLp (E := E) hp_top)).1 y')
  obtain ⟨w, hwv, hwtr⟩ := exists_wkp_two_value_ae_eq_of_integral_laplacian_mul_eq hp hp_top
    (Lp.memLp (R y')) (Lp.memLp ((1 : ℝ) • R y' - y')) fun φ hφ hc ↦ by
      exact hg ⟨φ, hφ, hc, fun _ _ ↦ Opens.mem_top _⟩
  refine ⟨w, Lp.ext ?_⟩
  rw [Filter.EventuallyEq, Measure.ae_restrict_coe_opens_top]
  filter_upwards [oneSubLaplacianL_ae w, hwv, hwtr, Lp.coeFn_sub ((1 : ℝ) • R y') y',
    Lp.coeFn_smul (1 : ℝ) (R y'), coeFn_toVolumeLp y] with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃, h₄, Pi.sub_apply, h₅, Pi.smul_apply, one_smul, ← h₆]
  ring

/-- **`1 - Δ` as an isomorphism `W^{2,p}(E) ≃ Lᵖ(E)`** for `1 < p < ∞`: `w ↦ w - tr D²w`, where
`D²w` is the weak Hessian. Its inverse is convolution with the heat resolvent kernel
(`TauCeti.Wkp.value_oneSubLaplacianEquiv_symm_ae`). -/
def oneSubLaplacianEquiv (hp : 1 < p) (hp_top : p ≠ ⊤) :
    Wkp (volume : Measure E) ⊤ p 2 ≃L[ℝ] Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E)) :=
  ContinuousLinearEquiv.ofBijective oneSubLaplacianL
    (LinearMap.ker_eq_bot.2 oneSubLaplacianL_injective)
    (LinearMap.range_eq_top.2 (oneSubLaplacianL_surjective hp hp_top))

/-- `TauCeti.Wkp.oneSubLaplacianEquiv` is `TauCeti.Wkp.oneSubLaplacianL`. -/
theorem oneSubLaplacianEquiv_apply (hp : 1 < p) (hp_top : p ≠ ⊤)
    (w : Wkp (volume : Measure E) ⊤ p 2) :
    oneSubLaplacianEquiv hp hp_top w = oneSubLaplacianL w :=
  congr_fun (ContinuousLinearEquiv.coeFn_ofBijective _ _ _) w

/-- `TauCeti.Wkp.oneSubLaplacianL` undoes the inverse of `TauCeti.Wkp.oneSubLaplacianEquiv`. -/
theorem oneSubLaplacianL_oneSubLaplacianEquiv_symm (hp : 1 < p) (hp_top : p ≠ ⊤)
    (f : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E))) :
    oneSubLaplacianL ((oneSubLaplacianEquiv hp hp_top).symm f) = f :=
  ContinuousLinearEquiv.ofBijective_apply_symm_apply _ _ _ f

/-- The inverse of `TauCeti.Wkp.oneSubLaplacianEquiv` undoes `TauCeti.Wkp.oneSubLaplacianL`. -/
theorem oneSubLaplacianEquiv_symm_oneSubLaplacianL (hp : 1 < p) (hp_top : p ≠ ⊤)
    (w : Wkp (volume : Measure E) ⊤ p 2) :
    (oneSubLaplacianEquiv hp hp_top).symm (oneSubLaplacianL w) = w :=
  ContinuousLinearEquiv.ofBijective_symm_apply_apply _ _ _ w

/-- **The inverse of `1 - Δ` is convolution with the heat resolvent kernel**: for `1 < p < ∞`
and `f ∈ Lᵖ(E)`, the value of `(1 - Δ)⁻¹ f ∈ W^{2,p}(E)` is `G₁ ⋆ f` almost everywhere. -/
theorem value_oneSubLaplacianEquiv_symm_ae (hp : 1 < p) (hp_top : p ≠ ⊤)
    (f : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E))) :
    (value 2 ((oneSubLaplacianEquiv hp hp_top).symm f) : E → ℝ) =ᵐ[volume]
      heatResolventKernel 1 ⋆ (f : E → ℝ) := by
  have h := heatResolventKernel_convolution_oneSubLaplacianL_ae_eq hp_top
    ((oneSubLaplacianEquiv hp hp_top).symm f)
  rw [oneSubLaplacianL_oneSubLaplacianEquiv_symm] at h
  exact h.symm

/-- **The `W^{2,p}` estimate for `u - Δu = f`**: for `1 < p < ∞` there is a constant `K`,
depending only on `E` and `p`, with `‖(1 - Δ)⁻¹ f‖_{W^{2,p}} ≤ K ‖f‖_{Lᵖ}` for every
`f ∈ Lᵖ(E)`. -/
theorem exists_norm_oneSubLaplacianEquiv_symm_le (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E)),
      ‖(oneSubLaplacianEquiv hp hp_top).symm f‖ ≤ K * ‖f‖ := by
  set L : Lp ℝ p ((volume : Measure E).restrict (⊤ : Opens E)) →L[ℝ]
    Wkp (volume : Measure E) ⊤ p 2 :=
      (oneSubLaplacianEquiv (E := E) hp hp_top).symm.toContinuousLinearMap
  exact ⟨‖L‖, norm_nonneg _, fun f ↦ L.le_opNorm f⟩

end Wkp

/-- **`W^{2,p}` solutions of `u - Δu = f` on the whole space.** For `1 < p < ∞` and `f ∈ Lᵖ(E)`,
the convolution `G₁ ⋆ f` with the heat resolvent kernel is the value of an element `w` of
`W^{2,p}(E)`, which solves `w - tr D²w = f` almost everywhere. -/
theorem exists_wkp_value_ae_eq_heatResolventKernel_convolution (hp : 1 < p) (hp_top : p ≠ ⊤)
    {f : E → ℝ} (hf : MemLp f p volume) :
    ∃ w : Wkp (volume : Measure E) ⊤ p 2,
      (Wkp.value 2 w : E → ℝ) =ᵐ[volume] heatResolventKernel 1 ⋆ f ∧
      (fun x ↦ Wkp.value 2 w x - LinearMap.trace ℝ E (Wkp.iteratedGradient 1 w x)) =ᵐ[volume]
        f := by
  have hf' : MemLp f p ((volume : Measure E).restrict (⊤ : Opens E)) :=
    hf.mono_measure Measure.restrict_le_self
  set w := (Wkp.oneSubLaplacianEquiv hp hp_top).symm (hf'.toLp f)
  have hfae : (hf'.toLp f : E → ℝ) =ᵐ[volume] f := by
    rw [← Measure.ae_restrict_coe_opens_top]
    exact hf'.coeFn_toLp
  have hw : Wkp.oneSubLaplacianL w = hf'.toLp f :=
    Wkp.oneSubLaplacianL_oneSubLaplacianEquiv_symm hp hp_top _
  refine ⟨w, ?_, ?_⟩
  · rw [← convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _) hfae]
    exact Wkp.value_oneSubLaplacianEquiv_symm_ae hp hp_top _
  · refine (Wkp.oneSubLaplacianL_ae w).symm.trans ?_
    rw [hw]
    exact hfae

end TauCeti
