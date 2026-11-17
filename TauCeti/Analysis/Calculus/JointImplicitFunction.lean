/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import TauCeti.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Analytic.IteratedDeriv

/-!
# The implicit function theorem with a moving level

Let `f : E₁ × E₂ → F` be strictly differentiable at `u` with invertible partial derivative
`∂₂f(u) : E₂ →L[𝕜] F`. Mathlib's `HasStrictFDerivAt.implicitFunctionOfProdDomain` solves
`f (z, v) = f u` for `v` as a function of `z`, at the fixed level `f u`. Here the level `w` varies
as well: the **joint implicit function** `ψ (z, w)` solves `f (z, ψ (z, w)) = w` for `(z, w)` near
`(u.1, f u)`. For each `z` it is a local inverse of `v ↦ f (z, v)`, and it depends jointly on the
parameter `z` and the value `w`.

The construction applies Mathlib's `ImplicitFunctionData` for `f` and `Prod.fst`
(`HasStrictFDerivAt.implicitFunctionDataOfProdDomain`), that is, the local inverse of
`(z, v) ↦ (f (z, v), z)`, and reads off the second coordinate. So `ψ` inherits the joint
regularity of that local inverse: it is strictly differentiable, `C^n` when `f` is (over `ℝ` or
`ℂ`), and analytic when `f` is. Over `ℂ` in finite dimensions this gives the holomorphic implicit
map of a holomorphic equation, see `TauCeti.Analysis.Complex.ImplicitFunction`.

## Main results

* `HasStrictFDerivAt.jointImplicitFunctionOfProdDomain`: the joint implicit function `ψ`.
* `HasStrictFDerivAt.jointImplicitFunctionOfProdDomain_apply_self`: `ψ (u.1, f u) = u.2`.
* `HasStrictFDerivAt.eventually_apply_jointImplicitFunctionOfProdDomain`: near `(u.1, f u)`,
  `f (z, ψ (z, w)) = w`.
* `HasStrictFDerivAt.eventually_jointImplicitFunctionOfProdDomain_apply`: near `u`,
  `ψ (z, f (z, v)) = v`.
* `HasStrictFDerivAt.eventually_apply_eq_iff_jointImplicitFunctionOfProdDomain`: near
  `(u, f u)`, `f (z, v) = w ↔ ψ (z, w) = v`.
* `HasStrictFDerivAt.eventuallyEq_jointImplicitFunctionOfProdDomain` and
  `HasStrictFDerivAt.eventuallyEq_jointImplicitFunctionOfProdDomain_of_continuousAt`: local
  uniqueness of `ψ`, from a left-inverse identity, or from a right-inverse identity together with
  continuity and the value at the base point.
* `HasStrictFDerivAt.hasStrictFDerivAt_jointImplicitFunctionOfProdDomain`: the derivative of `ψ`
  at `(u.1, f u)` is `(z, w) ↦ ∂₂f(u)⁻¹ (w - ∂₁f(u) z)`.
* `HasStrictFDerivAt.contDiffAt_jointImplicitFunctionOfProdDomain` and
  `HasStrictFDerivAt.analyticAt_jointImplicitFunctionOfProdDomain`: `ψ` is as regular as `f`.
* `AnalyticAt.exists_analyticAt_mul_deriv_eq`: for a scalar analytic coordinate `w : E × 𝕜 → 𝕜`
  with `∂w/∂t ≠ 0` and analytic amplitude `q`, constructs the analytic local inverse `T` and
  transformed amplitude `f(α, u) = q(α, T(α, u)) ∂T/∂u (α, u)` satisfying
  `f(α, w(α, t)) ∂w/∂t (α, t) = q(α, t)`.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Filter
open scoped Topology

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}

/-- The joint implicit function `ψ : E₁ × F → E₂` of `f : E₁ × E₂ → F` at `u`, defined near
`(u.1, f u)` by `f (z, ψ (z, w)) = w`. It is the second coordinate of the local inverse of
`(z, v) ↦ (f (z, v), z)` given by `HasStrictFDerivAt.implicitFunctionDataOfProdDomain`. -/
noncomputable def jointImplicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ × F → E₂ :=
  fun p ↦ ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction p.2 p.1).2

theorem jointImplicitFunctionOfProdDomain_def
    {dfu : HasStrictFDerivAt f f'u u} {if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible} :
    dfu.jointImplicitFunctionOfProdDomain if₂u =
      fun p ↦ ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction p.2 p.1).2 := by
  rfl

/-- At the fixed level `f u`, the joint implicit function is Mathlib's implicit function. -/
theorem implicitFunctionOfProdDomain_eq_jointImplicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    dfu.implicitFunctionOfProdDomain if₂u =
      fun z ↦ dfu.jointImplicitFunctionOfProdDomain if₂u (z, f u) := by
  rw [implicitFunctionOfProdDomain_def, jointImplicitFunctionOfProdDomain_def]

/-- The joint implicit function, written through the uncurried implicit function of
`implicitFunctionDataOfProdDomain`, whose variables are `(w, z)`. -/
private theorem jointImplicitFunctionOfProdDomain_eq_comp
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    dfu.jointImplicitFunctionOfProdDomain if₂u =
      Prod.snd ∘ (dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction.uncurry ∘
        Prod.swap := by
  rw [jointImplicitFunctionOfProdDomain_def]
  rfl

/-- The base point of the implicit function data, `(f u, u.1)`, is `(u.1, f u)` swapped. -/
private theorem prodFun_pt_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).prodFun
      (dfu.implicitFunctionDataOfProdDomain if₂u).pt = Prod.swap (u.1, f u) := by
  simp

/-- `Prod.swap` carries the neighbourhoods of `(u.1, f u)` into those of the base point of the
implicit function data, where its local inverse is defined. -/
private theorem tendsto_swap_prodFun_pt
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    Tendsto Prod.swap (𝓝 (u.1, f u))
      (𝓝 ((dfu.implicitFunctionDataOfProdDomain if₂u).prodFun
        (dfu.implicitFunctionDataOfProdDomain if₂u).pt)) := by
  rw [prodFun_pt_implicitFunctionDataOfProdDomain]
  exact continuous_swap.continuousAt

/-- Near `(u.1, f u)`, the joint implicit function solves `f (z, ψ (z, w)) = w`. -/
theorem eventually_apply_jointImplicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ p in 𝓝 (u.1, f u), f (p.1, dfu.jointImplicitFunctionOfProdDomain if₂u p) = p.2 := by
  filter_upwards [(dfu.tendsto_swap_prodFun_pt if₂u).eventually
    (dfu.implicitFunctionDataOfProdDomain if₂u).prodFun_implicitFunction] with p hp
  simp only [ImplicitFunctionData.prodFun_apply, leftFun_implicitFunctionDataOfProdDomain,
    rightFun_implicitFunctionDataOfProdDomain, Prod.swap, Prod.mk.injEq] at hp
  rw [jointImplicitFunctionOfProdDomain_def, ← hp.2]
  exact hp.1

/-- Near `u`, the joint implicit function inverts `v ↦ f (z, v)`: `ψ (z, f (z, v)) = v`. -/
theorem eventually_jointImplicitFunctionOfProdDomain_apply
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ v in 𝓝 u, dfu.jointImplicitFunctionOfProdDomain if₂u (v.1, f v) = v.2 := by
  have h := (dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction_apply_image
  simp only [pt_implicitFunctionDataOfProdDomain, leftFun_implicitFunctionDataOfProdDomain,
    rightFun_implicitFunctionDataOfProdDomain] at h
  filter_upwards [h] with v hv
  rw [jointImplicitFunctionOfProdDomain_def]
  exact congrArg Prod.snd hv

/-- The joint implicit function takes the value `u.2` at `(u.1, f u)`. -/
@[simp]
theorem jointImplicitFunctionOfProdDomain_apply_self
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    dfu.jointImplicitFunctionOfProdDomain if₂u (u.1, f u) = u.2 :=
  (dfu.eventually_jointImplicitFunctionOfProdDomain_apply if₂u).self_of_nhds

/-- **Local uniqueness of solutions.** For `(z, v)` near `u` and `w` near `f u`, the equation
`f (z, v) = w` holds exactly when `v = ψ (z, w)`. -/
theorem eventually_apply_eq_iff_jointImplicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ q in 𝓝 (u, f u),
      f q.1 = q.2 ↔ dfu.jointImplicitFunctionOfProdDomain if₂u (q.1.1, q.2) = q.1.2 := by
  have hleft := (continuous_fst.tendsto (u, f u)).eventually
    (dfu.eventually_jointImplicitFunctionOfProdDomain_apply if₂u)
  have hright := (((continuous_fst.comp continuous_fst).prodMk continuous_snd).tendsto
    (u, f u)).eventually (dfu.eventually_apply_jointImplicitFunctionOfProdDomain if₂u)
  filter_upwards [hleft, hright] with q hl hr
  constructor
  · intro h
    rw [← h]
    exact hl
  · intro h
    simpa [h] using hr

/-- **Local uniqueness of the joint implicit function**, left-inverse form: a function `φ` with
`φ (z, f (z, v)) = v` for `(z, v)` near `u` agrees with `ψ` near `(u.1, f u)`. -/
theorem eventuallyEq_jointImplicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible)
    {φ : E₁ × F → E₂} (hφ : ∀ᶠ v in 𝓝 u, φ (v.1, f v) = v.2) :
    φ =ᶠ[𝓝 (u.1, f u)] dfu.jointImplicitFunctionOfProdDomain if₂u := by
  set D := dfu.implicitFunctionDataOfProdDomain if₂u
  have h : ∀ᶠ x in 𝓝 D.pt, (fun w z ↦ (z, φ (z, w))) (D.leftFun x) (D.rightFun x) = x := by
    simp only [D, pt_implicitFunctionDataOfProdDomain, leftFun_implicitFunctionDataOfProdDomain,
      rightFun_implicitFunctionDataOfProdDomain]
    filter_upwards [hφ] with x hx
    exact Prod.ext rfl hx
  filter_upwards [(dfu.tendsto_swap_prodFun_pt if₂u).eventually
    (D.eventuallyEq_implicitFunction (ψ := fun w z ↦ (z, φ (z, w))) h)] with p hp
  rw [jointImplicitFunctionOfProdDomain_def]
  exact congrArg Prod.snd hp

/-- **Local uniqueness of the joint implicit function**, right-inverse form: a function `φ`,
continuous at `(u.1, f u)` with value `u.2` there and with `f (z, φ (z, w)) = w` near
`(u.1, f u)`, agrees with `ψ` near `(u.1, f u)`. -/
theorem eventuallyEq_jointImplicitFunctionOfProdDomain_of_continuousAt
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible)
    {φ : E₁ × F → E₂} (hφc : ContinuousAt φ (u.1, f u)) (hφu : φ (u.1, f u) = u.2)
    (hφ : ∀ᶠ p in 𝓝 (u.1, f u), f (p.1, φ p) = p.2) :
    φ =ᶠ[𝓝 (u.1, f u)] dfu.jointImplicitFunctionOfProdDomain if₂u := by
  have hcont : ContinuousAt (fun p : E₁ × F ↦ ((p.1, φ p), p.2)) (u.1, f u) :=
    (continuous_fst.continuousAt.prodMk hφc).prodMk continuous_snd.continuousAt
  have htendsto : Tendsto (fun p : E₁ × F ↦ ((p.1, φ p), p.2)) (𝓝 (u.1, f u)) (𝓝 (u, f u)) := by
    simpa [hφu] using hcont.tendsto
  filter_upwards [htendsto.eventually
    (dfu.eventually_apply_eq_iff_jointImplicitFunctionOfProdDomain if₂u), hφ] with p hp hφp
  exact (hp.1 hφp).symm

/-- The joint implicit function is strictly differentiable at `(u.1, f u)`, with derivative
`(z, w) ↦ ∂₂f(u)⁻¹ (w - ∂₁f(u) z)`. -/
theorem hasStrictFDerivAt_jointImplicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (dfu.jointImplicitFunctionOfProdDomain if₂u)
      ((f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L
        (.snd 𝕜 E₁ F - f'u ∘L .inl 𝕜 E₁ E₂ ∘L .fst 𝕜 E₁ F)) (u.1, f u) := by
  set D := dfu.implicitFunctionDataOfProdDomain if₂u
  set L := D.leftDeriv.equivProdOfSurjectiveOfIsCompl D.rightDeriv D.range_leftDeriv
    D.range_rightDeriv D.isCompl_ker
  -- the uncurried implicit function is the local inverse of `x ↦ (f x, x.1)`
  have hinv : HasStrictFDerivAt D.implicitFunction.uncurry (L.symm : F × E₁ →L[𝕜] E₁ × E₂)
      (D.prodFun D.pt) := by
    rw [ImplicitFunctionData.implicitFunction_def, Function.uncurry_curry,
      ← HasStrictFDerivAt.localInverse_def]
    exact D.hasStrictFDerivAt.to_localInverse
  rw [prodFun_pt_implicitFunctionDataOfProdDomain] at hinv
  have hcomp := hasStrictFDerivAt_snd.comp (u.1, f u)
    (hinv.comp (u.1, f u) (ContinuousLinearEquiv.prodComm 𝕜 E₁ F).hasStrictFDerivAt)
  rw [jointImplicitFunctionOfProdDomain_eq_comp]
  refine hcomp.congr_fderiv ?_
  -- the derivatives recorded in `D` are those of `f` and `Prod.fst`, by uniqueness
  have hl : D.leftDeriv = f'u := by
    have h := D.hasStrictFDerivAt_leftFun
    simp only [D, leftFun_implicitFunctionDataOfProdDomain,
      pt_implicitFunctionDataOfProdDomain] at h
    exact h.hasFDerivAt.unique dfu.hasFDerivAt
  have hr : D.rightDeriv = .fst 𝕜 E₁ E₂ := by
    have h := D.hasStrictFDerivAt_rightFun
    simp only [D, rightFun_implicitFunctionDataOfProdDomain,
      pt_implicitFunctionDataOfProdDomain] at h
    exact h.hasFDerivAt.unique hasFDerivAt_fst
  -- identify `snd ∘ L⁻¹ ∘ swap` with the stated derivative
  refine ContinuousLinearMap.ext fun p ↦ ?_
  set x := L.symm p.swap
  have hx : L x = p.swap := L.apply_symm_apply _
  simp only [L, ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply, hl, hr,
    ContinuousLinearMap.coe_fst', Prod.ext_iff, Prod.fst_swap, Prod.snd_swap] at hx
  have hsplit : f'u x = f'u (x.1, 0) + (f'u ∘L .inr 𝕜 E₁ E₂) x.2 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.prodComm_apply]
  rw [eq_comm, if₂u.inverse_apply_eq, ← hx.1, hsplit, ← hx.2, add_sub_cancel_left]

/-- The joint implicit function of an analytic equation is analytic. -/
theorem analyticAt_jointImplicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u)
    (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) (hf : AnalyticAt 𝕜 f u) :
    AnalyticAt 𝕜 (dfu.jointImplicitFunctionOfProdDomain if₂u) (u.1, f u) := by
  set D := dfu.implicitFunctionDataOfProdDomain if₂u
  have h := D.analyticAt_implicitFunction (by simpa [D] using hf)
    (by simpa [D] using analyticAt_fst)
  rw [prodFun_pt_implicitFunctionDataOfProdDomain] at h
  rw [jointImplicitFunctionOfProdDomain_eq_comp]
  exact analyticAt_snd.comp (h.comp_of_eq (analyticAt_snd.prod analyticAt_fst) rfl)

end HasStrictFDerivAt

end NontriviallyNormedField

namespace AnalyticAt

/-- **Analytic inverse coordinate and transformed amplitude** (DLMF 2.4.20). Given a coordinate
`w : E × 𝕜 → 𝕜` analytic at `(α₀, t₀)` with `∂w/∂t (α₀, t₀) ≠ 0` and an amplitude `q : E × 𝕜 → 𝕜`
analytic at `(α₀, t₀)` (over complete normed spaces `E, 𝕜`), there exist analytic functions `T` and
`f` at `(α₀, w (α₀, t₀))` such that `T(α₀, w(α₀, t₀)) = t₀`, `w(α, T(α, u)) = u` and
`f(α, u) = q(α, T(α, u)) ∂T/∂u (α, u)` near `(α₀, w (α₀, t₀))`, while `T(α, w(α, t)) = t` and
`f(α, w(α, t)) ∂w/∂t (α, t) = q(α, t)` near `(α₀, t₀)`. -/
theorem exists_analyticAt_mul_deriv_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {w q : E × 𝕜 → 𝕜} {α₀ : E} {t₀ : 𝕜}
    (hw : AnalyticAt 𝕜 w (α₀, t₀))
    (hdw : deriv (fun t => w (α₀, t)) t₀ ≠ 0)
    (hq : AnalyticAt 𝕜 q (α₀, t₀)) :
    ∃ T f : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 T (α₀, w (α₀, t₀)) ∧ AnalyticAt 𝕜 f (α₀, w (α₀, t₀)) ∧
      T (α₀, w (α₀, t₀)) = t₀ ∧
      (∀ᶠ u in 𝓝 (α₀, w (α₀, t₀)),
        w (u.1, T u) = u.2 ∧ f u = q (u.1, T u) * deriv (fun s => T (u.1, s)) u.2) ∧
      ∀ᶠ x in 𝓝 (α₀, t₀),
        T (x.1, w x) = x.2 ∧ f (x.1, w x) * deriv (fun t => w (x.1, t)) x.2 = q x := by
  have df : HasStrictFDerivAt w (fderiv 𝕜 w (α₀, t₀)) (α₀, t₀) := hw.hasStrictFDerivAt
  have hinv : (fderiv 𝕜 w (α₀, t₀) ∘L .inr 𝕜 E 𝕜).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut 𝕜 (.mk0 _ hdw), ?_⟩
    have hd : HasFDerivAt (fun t => w (α₀, t))
        (fderiv 𝕜 w (α₀, t₀) ∘L .inr 𝕜 E 𝕜) t₀ :=
      df.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right α₀ t₀)
    ext
    simp [hd.hasDerivAt.deriv]
  let T : E × 𝕜 → 𝕜 := df.jointImplicitFunctionOfProdDomain hinv
  have hTa : AnalyticAt 𝕜 T (α₀, w (α₀, t₀)) :=
    df.analyticAt_jointImplicitFunctionOfProdDomain hinv hw
  have hT0 : T (α₀, w (α₀, t₀)) = t₀ := df.jointImplicitFunctionOfProdDomain_apply_self hinv
  have hT_right : ∀ᶠ u in 𝓝 (α₀, w (α₀, t₀)), w (u.1, T u) = u.2 :=
    df.eventually_apply_jointImplicitFunctionOfProdDomain hinv
  have hT_left : ∀ᶠ x in 𝓝 (α₀, t₀), T (x.1, w x) = x.2 :=
    df.eventually_jointImplicitFunctionOfProdDomain_apply hinv
  set f : E × 𝕜 → 𝕜 := fun u => q (u.1, T u) * deriv (fun s => T (u.1, s)) u.2
  have hfa : AnalyticAt 𝕜 f (α₀, w (α₀, t₀)) :=
    (hq.comp_of_eq (analyticAt_fst.prod hTa) (by simp [hT0])).fun_mul hTa.deriv_snd
  refine ⟨T, f, hTa, hfa, hT0, hT_right.mono fun _ hu => ⟨hu, rfl⟩, ?_⟩
  have hpull : ContinuousAt (fun x : E × 𝕜 => (x.1, w x)) (α₀, t₀) :=
    continuousAt_fst.prodMk hw.continuousAt
  filter_upwards [hT_left.eventually_nhds, hw.eventually_analyticAt,
    hpull.eventually hTa.eventually_analyticAt] with x hx_nhds hwx hTx
  have hx_eq : T (x.1, w x) = x.2 := hx_nhds.self_of_nhds
  refine ⟨hx_eq, ?_⟩
  have hTs : DifferentiableAt 𝕜 (fun s => T (x.1, s)) (w x) :=
    (hTx.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  have hwt : DifferentiableAt 𝕜 (fun t => w (x.1, t)) x.2 :=
    (hwx.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt
  have hchain := (hTs.hasDerivAt.comp x.2 hwt.hasDerivAt).deriv
  simp only [Function.comp_def] at hchain
  have hid : (fun t => T (x.1, w (x.1, t))) =ᶠ[𝓝 x.2] id :=
    ((continuous_const.prodMk continuous_id).tendsto x.2).eventually hx_nhds
  have hjac : deriv (fun s => T (x.1, s)) (w x) * deriv (fun t => w (x.1, t)) x.2 = 1 := by
    rw [← hchain, hid.deriv_eq, deriv_id]
  dsimp [f]
  rw [hx_eq, mul_assoc, hjac, mul_one]

end AnalyticAt

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The joint implicit function of a `C^n` equation is `C^n`. -/
theorem HasStrictFDerivAt.contDiffAt_jointImplicitFunctionOfProdDomain {u : E₁ × E₂}
    {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F} (dfu : HasStrictFDerivAt f f'u u)
    (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) {n : WithTop ℕ∞} (hf : ContDiffAt 𝕜 n f u) :
    ContDiffAt 𝕜 n (dfu.jointImplicitFunctionOfProdDomain if₂u) (u.1, f u) := by
  set D := dfu.implicitFunctionDataOfProdDomain if₂u
  rcases eq_or_ne n 0 with rfl | hn
  · -- `C^0`: the local inverse is continuous on its open target
    have ht : D.toOpenPartialHomeomorph.target ∈ 𝓝 (D.prodFun D.pt) :=
      D.toOpenPartialHomeomorph.open_target.mem_nhds
        (D.prodFun_apply _ ▸ D.map_pt_mem_toOpenPartialHomeomorph_target)
    have hsymm : D.implicitFunction.uncurry = D.toOpenPartialHomeomorph.symm :=
      funext fun _ ↦ D.implicitFunction_apply
    rw [contDiffAt_zero, jointImplicitFunctionOfProdDomain_eq_comp, hsymm]
    exact ⟨_, dfu.tendsto_swap_prodFun_pt if₂u ht, continuous_snd.comp_continuousOn
      (D.toOpenPartialHomeomorph.continuousOn_symm.comp continuous_swap.continuousOn
        (Set.mapsTo_preimage _ _))⟩
  have h := D.contDiffAt_implicitFunction (by simpa [D] using hf)
    (by simpa [D] using contDiffAt_fst) hn
  rw [prodFun_pt_implicitFunctionDataOfProdDomain] at h
  rw [jointImplicitFunctionOfProdDomain_eq_comp]
  exact contDiffAt_snd.comp _ (h.comp _ (contDiffAt_snd.prodMk contDiffAt_fst))

end RCLike
