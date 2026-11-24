/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Eulerian

/-!
# Tensor-independent pullback variation along flows and isotopies

Differentiating the pullback `φ_u^* s_u` of a section (such as a differential form or a covariant
two-tensor) along a smooth family of maps `φ_u` splits into two parts:

1. a tensor-specific identity-case calculation at a time `t` where `ψ_t = id` near `y`, which reads
   the spatial variational derivative in the preferred chart via
   `TauCeti.hasDerivAt_fderiv_extChartAt_family_of_eq_id` (or its `C¹` counterpart
   `TauCeti.hasDerivAt_fderiv_extChartAt_family_of_eq_id_of_eventually_nhds_prod`) and combines it
   with the flat calculus formula for that fibre; and
2. tensor-independent geometric reductions — moving the base point along `ψ_u =ᶠ χ_u ∘ g`,
   constancy from zero velocity, and the reductions for smooth isotopies
   (`TauCeti.eulerianField`), autonomous maximal flows of `C¹` vector fields (`TauCeti.flowOf`), and
   time-dependent flows (`TauCeti.timeDependentFlowOf`).

`TauCeti.PullbackAction` packages a contravariant fibrewise continuous-linear pullback on a
section type `S` with model fibre `F`, and proves all of the tensor-independent reductions once so
they can be instantiated for both differential forms and covariant two-tensors. This factors out
the shared flow-pullback infrastructure originally developed in
`TauCeti.Geometry.Manifold.DifferentialForm.Flow` (and its `Eulerian` and `TimeDependent`
submodules).

## Main declarations

* `TauCeti.PullbackAction`: a contravariant fibrewise continuous-linear pullback action on a
  section type `S` with model fibre `F`.
* `TauCeti.PullbackAction.hasDerivAt_of_eq_comp`: moving the base point of a pullback derivative
  along a local factorization `ψ_u =ᶠ χ_u ∘ g`.
* `TauCeti.PullbackAction.pull_eq_of_forall_eq_zero`: constancy of pullbacks with vanishing
  velocity.
* `TauCeti.PullbackAction.hasDerivAt_eulerianField_self`,
  `TauCeti.PullbackAction.hasDerivAt_eulerianField`,
  `TauCeti.PullbackAction.forall_pull_eulerianField_eq_iff`: pullback variation and invariance
  along smooth isotopies.
* `TauCeti.PullbackAction.hasDerivAt_flowOf_zero`, `TauCeti.PullbackAction.hasDerivAt_flowOf`,
  `TauCeti.PullbackAction.eval_pull_flowOf_eq_of_eq_zero`: pullback variation and invariance along
  autonomous maximal flows of `C¹` vector fields.
* `TauCeti.PullbackAction.hasDerivAt_timeDependentFlowOf_self`,
  `TauCeti.PullbackAction.hasDerivAt_timeDependentFlowOf_of_mem`,
  `TauCeti.PullbackAction.hasDerivAt_timeDependentFlowOf`,
  `TauCeti.PullbackAction.forall_pull_timeDependentFlowOf_eq_self_iff`: pullback variation and
  invariance along maximal and complete time-dependent flows.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Proposition 12.36,
  Theorem 12.37, and Chapter 22.
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

/-- A contravariant fibrewise continuous-linear pullback action on sections of type `S` over a
manifold `M` with model fibre `F`. Instances include rough differential forms (with
`ContinuousAlternatingMap.compContinuousLinearMapCLM`) and covariant two-tensors (with
`ContinuousLinearMap.pullbackBilinL`). -/
structure PullbackAction {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M F : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : Type*) [Zero S] where
  /-- Pullback of a section along an endomap of `M`. -/
  pull : (M → M) → S → S
  /-- Evaluation of a section at a point `x : M`, viewed in the model fibre `F`. -/
  eval : S → M → F
  /-- Continuous linear pullback operator on the model fibre induced by a linear map `E →L[ℝ] E`. -/
  fibrePull : (E →L[ℝ] E) → (F →L[ℝ] F)
  /-- Pointwise pullback is given by `fibrePull (mfderiv I I f x)` on the fibre at `f x`. -/
  eval_pull (f : M → M) (s : S) (x : M) :
    eval (pull f s) x = fibrePull (mfderiv I I f x) (eval s (f x))
  /-- Pulling back along the identity linear map acts as the identity on the fibre. -/
  fibrePull_id : fibrePull (.id ℝ E) = .id ℝ F
  /-- Pulling back along a composition reverses the order of fibre operators. -/
  fibrePull_comp (A B : E →L[ℝ] E) : fibrePull (B.comp A) = (fibrePull A).comp (fibrePull B)
  /-- The zero section evaluates to zero at every point. -/
  eval_zero (x : M) : eval 0 x = 0
  /-- Sections are determined by their pointwise evaluations. -/
  ext {s₁ s₂ : S} (h : ∀ x, eval s₁ x = eval s₂ x) : s₁ = s₂

namespace PullbackAction

variable {E H M F S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Zero S]
  (A : PullbackAction I M F S)

/-- Maps agreeing on a neighbourhood of `x` induce the same pointwise pullback at `x`. -/
theorem eval_pull_congr {f g : M → M} {x : M} (h : f =ᶠ[𝓝 x] g) (s : S) :
    A.eval (A.pull f s) x = A.eval (A.pull g s) x := by
  rw [A.eval_pull, A.eval_pull, h.eq_of_nhds]
  have hd : (mfderiv I I f x : E →L[ℝ] E) = (mfderiv I I g x : E →L[ℝ] E) := by
    have hm := h.mfderiv_eq (I := I) (I' := I)
    ext v
    exact DFunLike.congr_fun hm v
  rw [hd]

/-- Chain rule for pointwise pullback at differentiable points. -/
theorem eval_pull_comp {f g : M → M} {x : M} (hf : MDifferentiableAt I I f x)
    (hg : MDifferentiableAt I I g (f x)) (s : S) :
    A.eval (A.pull (g ∘ f) s) x = A.eval (A.pull f (A.pull g s)) x := by
  let L₁ : E →L[ℝ] E := mfderiv I I f x
  let L₂ : E →L[ℝ] E := mfderiv I I g (f x)
  have hcomp : (mfderiv I I (g ∘ f) x : E →L[ℝ] E) = L₂.comp L₁ := mfderiv_comp x hg hf
  rw [A.eval_pull, A.eval_pull, A.eval_pull, Function.comp_apply, hcomp,
    A.fibrePull_comp, ContinuousLinearMap.comp_apply]

/-- Pulling back along the identity map fixes every section. -/
theorem pull_id (s : S) : A.pull id s = s := by
  refine A.ext fun x ↦ ?_
  have hid : (mfderiv I I id x : E →L[ℝ] E) = .id ℝ E := mfderiv_id
  rw [A.eval_pull, hid, A.fibrePull_id, ContinuousLinearMap.id_apply, id_eq]

/-- Pulling back the zero section along any map gives the zero section. -/
theorem pull_zero (f : M → M) : A.pull f 0 = 0 := by
  refine A.ext fun x ↦ ?_
  rw [A.eval_pull, A.eval_zero, A.eval_zero, map_zero]

/-- **Moving the base point of pulled-back sections.** If `ψ_u =ᶠ[𝓝 x] χ_u ∘ g` for `u` near `t`,
with `g` differentiable at `x` and each `χ_u` differentiable at `g x`, and the pullbacks
`(χ_u^* s_u)_{g x}` have velocity `β (g x)` at time `t`, then `(ψ_u^* s_u)_x` has velocity
`(g^* β)_x` at time `t`. -/
theorem hasDerivAt_of_eq_comp {ψ χ : ℝ → M → M} {g : M → M} {s : ℝ → S} {β : S}
    {x : M} {t : ℝ} (hψ : ∀ᶠ u in 𝓝 t, ψ u =ᶠ[𝓝 x] χ u ∘ g)
    (hg : MDifferentiableAt I I g x)
    (hχ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I (χ u) (g x))
    (h : HasDerivAt (fun u ↦ A.eval (A.pull (χ u) (s u)) (g x)) (A.eval β (g x)) t) :
    HasDerivAt (fun u ↦ A.eval (A.pull (ψ u) (s u)) x) (A.eval (A.pull g β) x) t := by
  have hL := (A.fibrePull (mfderiv I I g x)).hasFDerivAt.comp_hasDerivAt t h
  refine (hL.congr_of_eventuallyEq ?_).congr_deriv (A.eval_pull g β x).symm
  filter_upwards [hψ, hχ] with u hu hχu
  rw [A.eval_pull_congr hu, A.eval_pull_comp hg hχu, A.eval_pull, Function.comp_apply]

/-- **Pullbacks with vanishing velocity are constant in time.** If at every time `u` and point `x`
the pullbacks `(ψ_u^* s_u)_x` have derivative `(ψ_u^* β_u)_x` and `β_u = 0` for every `u`, then
`ψ_r^* s_r = ψ_t^* s_t` for all `r, t : ℝ`. -/
theorem pull_eq_of_forall_eq_zero {ψ : ℝ → M → M} {s β : ℝ → S}
    (hd : ∀ u x, HasDerivAt (fun r ↦ A.eval (A.pull (ψ r) (s r)) x)
      (A.eval (A.pull (ψ u) (β u)) x) u)
    (hβ : ∀ u, β u = 0) (r t : ℝ) :
    A.pull (ψ r) (s r) = A.pull (ψ t) (s t) := by
  refine A.ext fun x ↦ ?_
  have hderiv (u : ℝ) : HasDerivAt (fun r ↦ A.eval (A.pull (ψ r) (s r)) x) 0 u := by
    have h := hd u x
    rwa [hβ u, A.pull_zero, A.eval_zero] at h
  exact is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) r t

section Isotopy

variable {φ : ℝ → M ≃ M}
  (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ φ p.1 p.2))
  (hφ' : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ (φ p.1).symm p.2))
include hφ hφ'

/-- **Pullback derivative at the base time of a smooth isotopy.** Reduces the derivative of
`u ↦ ((φ_u ∘ φ_t⁻¹)^* s_u)_y` at `u = t` to the identity-case derivative theorem along the
Eulerian velocity field `eulerianField I φ t`. -/
theorem hasDerivAt_eulerianField_self {s : ℝ → S} {β : S} (t : ℝ) (y : M)
    (hid : ∀ {ψ : ℝ → M → M},
      (∀ᶠ x in 𝓝 y, ψ t x = x) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y) →
      (∀ᶠ x in 𝓝 y, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (eulerianField I φ t (ψ t x)))) →
      HasDerivAt (fun u ↦ A.eval (A.pull (ψ u) (s u)) y) (A.eval β y) t) :
    HasDerivAt (fun u ↦ A.eval (A.pull (fun x ↦ φ u ((φ t).symm x)) (s u)) y)
      (A.eval β y) t := by
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ φ p.1 ((φ t).symm p.2)) :=
    hφ.comp (contMDiff_fst.prodMk
      ((hφ'.curry_right (f := fun u y ↦ (φ u).symm y) (x := t)).comp contMDiff_snd))
  refine hid (Eventually.of_forall fun x ↦ (φ t).apply_symm_apply x) hsmooth.contMDiffAt
    (Eventually.of_forall fun x ↦ ?_)
  exact hasMFDerivAt_eulerianField
    ((hφ.curry_left (f := fun u x ↦ φ u x)).mdifferentiable two_ne_zero t)

/-- **Moving the pullback derivative along a smooth isotopy from the base time.** Given the
derivative of `u ↦ ((φ_u ∘ φ_t⁻¹)^* s_u)_{φ_t x}` at `u = t`, pulls it back along `φ_t` to give
the derivative of `u ↦ (φ_u^* s_u)_x` at `u = t`. -/
theorem hasDerivAt_eulerianField {s : ℝ → S} {β : S} (t : ℝ) (x : M)
    (hself : HasDerivAt (fun u ↦ A.eval (A.pull (fun z ↦ φ u ((φ t).symm z)) (s u)) (φ t x))
      (A.eval β (φ t x)) t) :
    HasDerivAt (fun u ↦ A.eval (A.pull (φ u) (s u)) x) (A.eval (A.pull (φ t) β) x) t := by
  have hφu (u : ℝ) : MDifferentiable I I (φ u) :=
    (hφ.curry_right (f := fun u x ↦ φ u x) (x := u)).mdifferentiable two_ne_zero
  have hφt : MDifferentiable I I (φ t).symm :=
    (hφ'.curry_right (f := fun u y ↦ (φ u).symm y) (x := t)).mdifferentiable two_ne_zero
  exact A.hasDerivAt_of_eq_comp (χ := fun u z ↦ φ u ((φ t).symm z))
    (Eventually.of_forall fun u ↦ Eventually.of_forall fun z ↦ by simp) (hφu t x)
    (Eventually.of_forall fun u ↦ ((hφu u).comp hφt) _) hself

/-- **Invariance of a stationary section under a smooth isotopy.** Given the base-time derivative
`L (eulerianField I φ t)` of `u ↦ ((φ_u ∘ φ_t⁻¹)^* s)_y`, the pullbacks `φ_t^* s` are independent
of `t` if and only if `L (eulerianField I φ t) = 0` for all `t`. -/
theorem forall_pull_eulerianField_eq_iff {s : S}
    {L : ((x : M) → TangentSpace I x) → S}
    (hself : ∀ t y, HasDerivAt
      (fun u ↦ A.eval (A.pull (fun z ↦ φ u ((φ t).symm z)) s) y)
      (A.eval (L (eulerianField I φ t)) y) t) :
    (∀ r t, A.pull (φ r) s = A.pull (φ t) s) ↔ ∀ t, L (eulerianField I φ t) = 0 := by
  refine ⟨fun h t ↦ ?_, fun h r t ↦ A.pull_eq_of_forall_eq_zero (s := fun _ ↦ s)
    (fun u x ↦ A.hasDerivAt_eulerianField hφ hφ' u x (hself u (φ u x))) h r t⟩
  refine A.ext fun y ↦ ?_
  have hd := hself t y
  have hconst : (fun u ↦ A.eval (A.pull (fun z ↦ φ u ((φ t).symm z)) s) y) =
      fun _ ↦ A.eval (A.pull (fun z ↦ φ t ((φ t).symm z)) s) y := by
    funext u
    have hcomp (r : ℝ) : (fun z ↦ φ r ((φ t).symm z)) = φ r ∘ (φ t).symm := rfl
    have hφt : MDifferentiableAt I I (φ t).symm y :=
      (hφ'.curry_right (f := fun u y ↦ (φ u).symm y) (x := t)).mdifferentiableAt two_ne_zero
    have hφu (r : ℝ) : MDifferentiable I I (φ r) :=
      (hφ.curry_right (f := fun u x ↦ φ u x) (x := r)).mdifferentiable two_ne_zero
    rw [hcomp, hcomp, A.eval_pull_comp hφt (hφu u _), A.eval_pull_comp hφt (hφu t _), h u t]
  rw [hconst] at hd
  exact (hd.unique (hasDerivAt_const t _)).trans (A.eval_zero y).symm

end Isotopy

variable [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless] [IsManifold I 2 M]

section MaximalFlow

/-- The flow lemmas are applied at smoothness `1`, read in `ℕ∞`. -/
local instance : IsManifold I ((1 : ℕ∞) : WithTop ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)

variable {Z : (x : M) → TangentSpace I x}
  (hZ : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hZ

/-- **Pullback derivative at time zero along a maximal flow.** Reduces the derivative of
`r ↦ ((flowOf Z r)^* s_r)_y` at `r = 0` to the `C¹` identity-case derivative theorem along `Z`. -/
theorem hasDerivAt_flowOf_zero {s : ℝ → S} {β : S} (y : M)
    (hid : ∀ {ψ : ℝ → M → M},
      (∀ᶠ x in 𝓝 y, ψ 0 x = x) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1 (fun p : ℝ × M ↦ ψ p.1 p.2) (0, y) →
      ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, Z x⟩ : TangentBundle I M)) y →
      (∀ᶠ p in 𝓝 (0, y), HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u p.2) p.1
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (ψ p.1 p.2)))) →
      HasDerivAt (fun r ↦ A.eval (A.pull (ψ r) (s r)) y) (A.eval β y) 0) :
    HasDerivAt (fun r ↦ A.eval (A.pull (flowOf Z r) (s r)) y) (A.eval β y) 0 := by
  have hD := isOpen_flowDomain hZ
  refine hid (Eventually.of_forall (flowOf_zero Z))
    ((contMDiffOn_flowOf (n := 1) le_rfl hZ).contMDiffAt
      (hD.mem_nhds (mem_flowDomain_zero hZ y))) (hZ y) ?_
  filter_upwards [hD.mem_nhds (mem_flowDomain_zero hZ y)] with p hp
  exact (isMIntegralCurveAt_flowOf hZ hp).hasMFDerivAt

/-- **Pullback derivative at arbitrary time along a maximal flow.** Uses the local group law
`flowOf Z r = flowOf Z (r - t) ∘ flowOf Z t` near `x` for `r` near `t` to reduce the velocity of
`r ↦ ((flowOf Z r)^* s_r)_x` at `t` to the velocity at time `0` of the time-shifted family
`r ↦ ((flowOf Z r)^* s (r + t))_{flowOf Z t x}`. -/
theorem hasDerivAt_flowOf {s : ℝ → S} {β : S} {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain Z)
    (h0 : HasDerivAt (fun r ↦ A.eval (A.pull (flowOf Z r) (s (r + t))) (flowOf Z t x))
      (A.eval β (flowOf Z t x)) 0) :
    HasDerivAt (fun r ↦ A.eval (A.pull (flowOf Z r) (s r)) x)
      (A.eval (A.pull (flowOf Z t) β) x) t := by
  have hD := isOpen_flowDomain hZ
  have hφ : ContMDiffAt I I 1 (flowOf Z t) x :=
    contMDiffAt_flowOf_comp (n := 1) le_rfl hZ contMDiffAt_const contMDiffAt_id hx
  have hev : ∀ᶠ p in 𝓝 ((0 : ℝ), x),
      (t, p.2) ∈ flowDomain Z ∧ (p.1, flowOf Z t p.2) ∈ flowDomain Z :=
    ((continuous_const.prodMk continuous_snd).continuousAt.eventually_mem (hD.mem_nhds hx)).and
      ((continuousAt_fst.prodMk (hφ.continuousAt.comp continuousAt_snd)).eventually_mem
        (hD.mem_nhds (mem_flowDomain_zero hZ _)))
  rw [nhds_prod_eq] at hev
  have hsub : Tendsto (fun r ↦ r - t) (𝓝 t) (𝓝 0) := by
    simpa using (continuous_sub_right t).tendsto t
  have h0_sub : HasDerivAt
      (fun r ↦ A.eval (A.pull (flowOf Z (r - t)) (s r)) (flowOf Z t x))
      (A.eval β (flowOf Z t x)) t :=
    (HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])).congr_of_eventuallyEq
      (Eventually.of_forall fun r ↦ congrArg
        (fun u ↦ A.eval (A.pull (flowOf Z (r - t)) (s u)) (flowOf Z t x))
        (sub_add_cancel r t).symm)
  refine A.hasDerivAt_of_eq_comp (ψ := flowOf Z) (χ := fun r ↦ flowOf Z (r - t))
    ?_ (hφ.mdifferentiableAt one_ne_zero) ?_ h0_sub
  · filter_upwards [hsub.eventually hev.curry] with r hr
    refine hr.mono fun z hz ↦ ?_
    have h := (flowOf_add hZ hz.1 hz.2).2
    rw [add_sub_cancel] at h
    exact h.symm
  · filter_upwards [hsub.eventually hev.curry] with r hr
    exact (contMDiffAt_flowOf_comp (n := 1) le_rfl hZ contMDiffAt_const contMDiffAt_id
      hr.self_of_nhds.2).mdifferentiableAt one_ne_zero

/-- **Maximal flows preserve stationary sections with zero pullback velocity.** If at every time
`r` where the maximal flow through `x` is defined the pullback `u ↦ ((flowOf Z u)^* s)_x` has
derivative `((flowOf Z r)^* β)_x` with `β = 0`, then `((flowOf Z t)^* s)_x = s_x` wherever
`(t, x) ∈ flowDomain Z`. -/
theorem eval_pull_flowOf_eq_of_eq_zero {s β : S}
    (hd : ∀ r, (r, x) ∈ flowDomain Z →
      HasDerivAt (fun u ↦ A.eval (A.pull (flowOf Z u) s) x)
        (A.eval (A.pull (flowOf Z r) β) x) r)
    (hβ : β = 0) {t : ℝ} (hx : (t, x) ∈ flowDomain Z) :
    A.eval (A.pull (flowOf Z t) s) x = A.eval s x := by
  set J : Set ℝ := {r | (r, x) ∈ flowDomain Z}
  have hJopen : IsOpen J :=
    (isOpen_flowDomain hZ).preimage (continuous_id.prodMk continuous_const)
  have hJc : J.OrdConnected := by
    rw [show J = maximalIntegralCurveInterval Z x from Set.ext fun _ ↦ mem_flowDomain]
    exact ordConnected_maximalIntegralCurveInterval
  set P : ℝ → F := fun r ↦ A.eval (A.pull (flowOf Z r) s) x
  have hP (r : ℝ) (hr : r ∈ J) : HasDerivAt P 0 r := by
    have h := hd r hr
    rwa [hβ, A.pull_zero, A.eval_zero] at h
  have hP0 : P 0 = A.eval s x := by
    simp only [P, show flowOf Z 0 = id from funext (flowOf_zero Z), A.pull_id]
  refine (hJc.convex.is_const_of_fderivWithin_eq_zero
    (fun r hr ↦ (hP r hr).differentiableAt.differentiableWithinAt) (fun r hr ↦ ?_) hx
    (mem_flowDomain_zero hZ x)).trans hP0
  rw [((hP r hr).hasFDerivAt.hasFDerivWithinAt (s := J)).fderivWithin
    (hJopen.uniqueDiffWithinAt hr)]
  ext
  simp

end MaximalFlow

section TimeDependentFlow

variable {X : ℝ → (x : M) → TangentSpace I x}
  (hc : IsCompleteVectorField (timeDependentSuspensionField X))
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **Pullback derivative at the base time of a time-dependent flow.** Reduces the derivative of
`u ↦ ((timeDependentFlowOf X t u)^* s_u)_y` at `u = t` to the identity-case derivative theorem
along `X t`. No completeness is needed. -/
theorem hasDerivAt_timeDependentFlowOf_self {s : ℝ → S} {β : S} (t : ℝ) (y : M)
    (hid : ∀ {ψ : ℝ → M → M},
      (∀ᶠ x in 𝓝 y, ψ t x = x) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y) →
      (∀ᶠ x in 𝓝 y, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (ψ t x)))) →
      HasDerivAt (fun u ↦ A.eval (A.pull (ψ u) (s u)) y) (A.eval β y) t) :
    HasDerivAt (fun u ↦ A.eval (A.pull (timeDependentFlowOf X t u) (s u)) y)
      (A.eval β y) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  exact hid (Eventually.of_forall (timeDependentFlowOf_self X t))
    (contMDiffAt_uncurry_timeDependentFlowOf (n := 2) one_le_two hX
      (mem_timeDependentFlowDomain_self hX₁ t y))
    (Eventually.of_forall fun x ↦
      hasMFDerivAt_timeDependentFlowOf hX₁ (mem_timeDependentFlowDomain_self hX₁ t x))

/-- **Moving the pullback derivative along a maximal time-dependent flow from the base time.**
Uses the local two-time composition law `φ_{s,u} = φ_{t,u} ∘ φ_{s,t}` on `timeDependentFlowDomain X`
to deduce the derivative of `u ↦ ((timeDependentFlowOf X s u)^* b_u)_x` at `t` from the base-time
derivative at `t`. No completeness is needed. -/
theorem hasDerivAt_timeDependentFlowOf_of_mem {b : ℝ → S} {β : S} {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hself : HasDerivAt
      (fun u ↦ A.eval (A.pull (timeDependentFlowOf X t u) (b u)) (timeDependentFlowOf X s t x))
      (A.eval β (timeDependentFlowOf X s t x)) t) :
    HasDerivAt (fun u ↦ A.eval (A.pull (timeDependentFlowOf X s u) (b u)) x)
      (A.eval (A.pull (timeDependentFlowOf X s t) β) x) t := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  have hD := isOpen_timeDependentFlowDomain hX₁
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) x :=
    mdifferentiableAt_timeDependentFlowOf hX₁ h
  have hev : ∀ᶠ p in 𝓝 (t, x), ((s, t), p.2) ∈ timeDependentFlowDomain X ∧
      ((t, p.1), timeDependentFlowOf X s t p.2) ∈ timeDependentFlowDomain X :=
    ((continuous_const.prodMk continuous_snd).continuousAt.eventually_mem (hD.mem_nhds h)).and
      (((continuous_const.prodMk continuous_fst).continuousAt.prodMk
        (hφ.continuousAt.comp continuousAt_snd)).eventually_mem
          (hD.mem_nhds (mem_timeDependentFlowDomain_self hX₁ t _)))
  rw [nhds_prod_eq] at hev
  refine A.hasDerivAt_of_eq_comp (χ := timeDependentFlowOf X t) ?_ hφ ?_ hself
  · filter_upwards [hev.curry] with u hu
    filter_upwards [hu] with y hy
    exact (timeDependentFlowOf_trans_of_mem hX₁ hy.1 hy.2).2.symm
  · filter_upwards [hev.curry] with u hu
    exact mdifferentiableAt_timeDependentFlowOf hX₁ hu.self_of_nhds.2

include hc

/-- **Moving the pullback derivative along a complete time-dependent flow from the base time.** -/
theorem hasDerivAt_timeDependentFlowOf {b : ℝ → S} {β : S} (s t : ℝ) (x : M)
    (hself : HasDerivAt
      (fun u ↦ A.eval (A.pull (timeDependentFlowOf X t u) (b u)) (timeDependentFlowOf X s t x))
      (A.eval β (timeDependentFlowOf X s t x)) t) :
    HasDerivAt (fun u ↦ A.eval (A.pull (timeDependentFlowOf X s u) (b u)) x)
      (A.eval (A.pull (timeDependentFlowOf X s t) β) x) t :=
  A.hasDerivAt_timeDependentFlowOf_of_mem hX
    (mem_timeDependentFlowDomain.2 (hc.mem_flowDomain _ _)) hself

/-- **Invariance of a stationary section under a complete time-dependent flow.** Given the
base-time derivative `L (X t)` of `u ↦ ((timeDependentFlowOf X t u)^* b)_y`, the flow preserves
`b` for all `s, t : ℝ` if and only if `L (X t) = 0` for all `t : ℝ`. -/
theorem forall_pull_timeDependentFlowOf_eq_self_iff {b : S}
    {L : ((x : M) → TangentSpace I x) → S}
    (hself : ∀ t y, HasDerivAt
      (fun u ↦ A.eval (A.pull (timeDependentFlowOf X t u) b) y)
      (A.eval (L (X t)) y) t) :
    (∀ s t, A.pull (timeDependentFlowOf X s t) b = b) ↔ ∀ t, L (X t) = 0 := by
  have hid (s : ℝ) : A.pull (timeDependentFlowOf X s s) b = b := by
    rw [show timeDependentFlowOf X s s = id from funext (timeDependentFlowOf_self X s), A.pull_id]
  refine ⟨fun h t ↦ ?_, fun h s t ↦ ?_⟩
  · refine A.ext fun y ↦ ?_
    have hd := hself t y
    have hconst : (fun u ↦ A.eval (A.pull (timeDependentFlowOf X t u) b) y) =
        fun _ ↦ A.eval b y :=
      funext fun u ↦ congrArg (fun c ↦ A.eval c y) (h t u)
    rw [hconst] at hd
    exact (hd.unique (hasDerivAt_const t (A.eval b y))).trans (A.eval_zero y).symm
  · rw [A.pull_eq_of_forall_eq_zero (s := fun _ ↦ b)
      (fun u x ↦ A.hasDerivAt_timeDependentFlowOf hc hX s u x (hself u _)) h t s, hid s]

end TimeDependentFlow

end PullbackAction

end TauCeti
