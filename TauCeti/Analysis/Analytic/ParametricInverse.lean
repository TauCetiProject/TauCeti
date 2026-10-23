/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import TauCeti.Analysis.Analytic.Inverse
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# The implicit function theorem with a varying level

Let `f : E₁ × E₂ → F` be strictly differentiable at `u = (z₀, v₀)`, with invertible partial
derivative `∂f/∂v` there. Mathlib's `HasStrictFDerivAt.implicitFunctionOfProdDomain` solves
`f (z, v) = f u` for `v` as a function of `z`, at the single level `f u`. This file solves
`f (z, v) = w` for `v` jointly in the parameter `z` and the level `w`: the map
`HasStrictFDerivAt.localInverseOfProdDomain`, written `F` below, satisfies `F z₀ (f u) = v₀` and
`f (z, F z w) = w` for `(z, w)` near `(z₀, f u)`. For each fixed `z` near `z₀`, `w ↦ F z w` is
thus a local inverse of `v ↦ f (z, v)`.

`F` is locally unique: near `(u, f u)`, `f (z, v) = w` holds exactly when `F z w = v`, and any
solution `g` which is continuous at `(z₀, f u)` with `g z₀ (f u) = v₀` agrees with `F` near that
point. `F` is jointly as regular as `f`: it is strictly differentiable, `C^n` over `ℝ` or `ℂ` for
`n ≠ 0` and analytic over any complete field when `f` is, and it is holomorphic near
`(z₀, f u)` when `f` is holomorphic near `u` on a finite-dimensional complex space.

The map is the local inverse of `(z, v) ↦ (f (z, v), z)`, the coordinate change in Mathlib's
`HasStrictFDerivAt.implicitFunctionDataOfProdDomain`, whose inverse is
`ImplicitFunctionData.implicitFunction`. Its regularity comes from
`ImplicitFunctionData.contDiffAt_implicitFunction` and
`ImplicitFunctionData.analyticAt_implicitFunction`, which are joint in both arguments of the
implicit function.

## Main definitions

* `HasStrictFDerivAt.localInverseOfProdDomain`: the implicit function of `f (z, v) = w`, as a
  function of the parameter `z` and the level `w`.

## Main results

* `HasStrictFDerivAt.localInverseOfProdDomain_apply_self`,
  `HasStrictFDerivAt.eventually_apply_localInverseOfProdDomain`: `F z₀ (f u) = v₀`, and
  `f (z, F z w) = w` near `(z₀, f u)`.
* `HasStrictFDerivAt.eventually_apply_eq_iff_localInverseOfProdDomain` and
  `HasStrictFDerivAt.eventuallyEq_localInverseOfProdDomain`: local uniqueness.
* `HasStrictFDerivAt.hasStrictFDerivAt_uncurry_localInverseOfProdDomain`: the derivative of `F`
  at `(z₀, f u)` is `(a, b) ↦ (∂f/∂v)⁻¹ (b - ∂f/∂z a)`.
* `HasStrictFDerivAt.contDiffAt_uncurry_localInverseOfProdDomain`,
  `HasStrictFDerivAt.analyticAt_uncurry_localInverseOfProdDomain`: `F` is jointly `C^n`,
  respectively analytic, when `f` is.
* `HasStrictFDerivAt.eventually_differentiableAt_uncurry_localInverseOfProdDomain`: the
  **holomorphic implicit function theorem with a varying level**. If `f` is complex differentiable
  near `u` on a finite-dimensional space, then `F` is complex differentiable near `(z₀, f u)`.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Filter Function
open scoped ContDiff Topology

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}

/-- The implicit function of the equation `f (z, v) = w`, as a function of the parameter `z` and
the level `w`. Here `f` is strictly differentiable at `u` with invertible partial derivative in
`v`. Near `(u.1, f u)` it satisfies `f (z, localInverseOfProdDomain z w) = w`
(`HasStrictFDerivAt.eventually_apply_localInverseOfProdDomain`), so for each `z` near `u.1` the
map `w ↦ localInverseOfProdDomain z w` is a local inverse of `v ↦ f (z, v)`. -/
noncomputable def localInverseOfProdDomain (dfu : HasStrictFDerivAt f f'u u)
    (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : E₁ → F → E₂ :=
  fun z w ↦ ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction w z).2

variable (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible)

/-- Unfolding lemma for `localInverseOfProdDomain`. -/
theorem localInverseOfProdDomain_def :
    dfu.localInverseOfProdDomain if₂u =
      fun z w ↦ ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction w z).2 := by
  rfl

/-- At the level `f u`, the map `localInverseOfProdDomain` is Mathlib's single-level implicit
function `implicitFunctionOfProdDomain`. -/
theorem localInverseOfProdDomain_apply_eq_implicitFunctionOfProdDomain (z : E₁) :
    dfu.localInverseOfProdDomain if₂u z (f u) = dfu.implicitFunctionOfProdDomain if₂u z := by
  rw [implicitFunctionOfProdDomain_def, localInverseOfProdDomain_def]

/-- The function `localInverseOfProdDomain` is the second component of the inverse of
`(z, v) ↦ (f (z, v), z)`, read with its arguments swapped. -/
theorem uncurry_localInverseOfProdDomain :
    uncurry (dfu.localInverseOfProdDomain if₂u) =
      Prod.snd ∘ uncurry (dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction ∘
        Prod.swap := by
  rfl

/-- The implicit function data of `f` sends the point `u` to `(f u, u.1)`, the swap of the base
point `(u.1, f u)` of `localInverseOfProdDomain`. -/
private theorem prodFun_pt :
    (dfu.implicitFunctionDataOfProdDomain if₂u).prodFun
        (dfu.implicitFunctionDataOfProdDomain if₂u).pt = (u.1, f u).swap := by
  simp

/-- Near `(u.1, f u)`, the inverse of `(z, v) ↦ (f (z, v), z)` at `(w, z)` is
`(z, localInverseOfProdDomain z w)`. -/
private theorem eventually_implicitFunction_eq :
    ∀ᶠ p in 𝓝 (u.1, f u), (dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction p.2 p.1 =
      (p.1, dfu.localInverseOfProdDomain if₂u p.1 p.2) := by
  have h := (dfu.implicitFunctionDataOfProdDomain if₂u).rightFun_implicitFunction
  rw [prodFun_pt] at h
  filter_upwards [(continuous_swap.tendsto (u.1, f u)).eventually h] with p hp
  simp only [Prod.fst_swap, Prod.snd_swap, rightFun_implicitFunctionDataOfProdDomain] at hp
  exact Prod.ext hp (by rw [localInverseOfProdDomain_def])

/-- At the base point, `localInverseOfProdDomain` takes the value `u.2`. -/
@[simp]
theorem localInverseOfProdDomain_apply_self :
    dfu.localInverseOfProdDomain if₂u u.1 (f u) = u.2 := by
  have h := (dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction_apply_image.self_of_nhds
  simp only [leftFun_implicitFunctionDataOfProdDomain, rightFun_implicitFunctionDataOfProdDomain,
    pt_implicitFunctionDataOfProdDomain] at h
  exact congrArg Prod.snd h

/-- `localInverseOfProdDomain` solves the equation: `f (z, localInverseOfProdDomain z w) = w` for
`(z, w)` near `(u.1, f u)`. -/
theorem eventually_apply_localInverseOfProdDomain :
    ∀ᶠ p in 𝓝 (u.1, f u), f (p.1, dfu.localInverseOfProdDomain if₂u p.1 p.2) = p.2 := by
  have h := (dfu.implicitFunctionDataOfProdDomain if₂u).leftFun_implicitFunction
  rw [prodFun_pt] at h
  filter_upwards [(continuous_swap.tendsto (u.1, f u)).eventually h,
    dfu.eventually_implicitFunction_eq if₂u] with p hp hp'
  simp only [Prod.fst_swap, Prod.snd_swap, leftFun_implicitFunctionDataOfProdDomain] at hp
  rwa [hp'] at hp

/-- `localInverseOfProdDomain` recovers the second variable: near `u`,
`localInverseOfProdDomain z (f (z, v)) = v`. -/
theorem eventually_localInverseOfProdDomain_apply :
    ∀ᶠ v in 𝓝 u, dfu.localInverseOfProdDomain if₂u v.1 (f v) = v.2 := by
  have h := (dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction_apply_image
  simp only [leftFun_implicitFunctionDataOfProdDomain, rightFun_implicitFunctionDataOfProdDomain,
    pt_implicitFunctionDataOfProdDomain] at h
  filter_upwards [h] with v hv
  exact congrArg Prod.snd hv

/-- **Local uniqueness.** Near `(u, f u)`, the equation `f (z, v) = w` holds exactly when
`localInverseOfProdDomain z w = v`. -/
theorem eventually_apply_eq_iff_localInverseOfProdDomain :
    ∀ᶠ p in 𝓝 (u, f u), f p.1 = p.2 ↔ dfu.localInverseOfProdDomain if₂u p.1.1 p.2 = p.1.2 := by
  set φ : ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ := dfu.implicitFunctionDataOfProdDomain if₂u
  set Θ := φ.toOpenPartialHomeomorph
  have hΘ (x : E₁ × E₂) : Θ x = (f x, x.1) := by simp [Θ, φ]
  have hsource : u ∈ Θ.source := by
    have h := φ.pt_mem_toOpenPartialHomeomorph_source
    simpa only [φ, pt_implicitFunctionDataOfProdDomain] using h
  -- the inverse of `Θ` is defined on a neighbourhood of `(f u, u.1)`
  have htarget : ∀ᶠ p in 𝓝 (u.1, f u), p.swap ∈ Θ.target := by
    refine (continuous_swap.tendsto (u.1, f u)).eventually (Θ.open_target.mem_nhds ?_)
    rw [Prod.swap_prod_mk, ← hΘ u]
    exact Θ.map_source hsource
  have hpr : Tendsto (fun p : (E₁ × E₂) × F ↦ (p.1.1, p.2)) (𝓝 (u, f u)) (𝓝 (u.1, f u)) :=
    (continuous_fst.fst.prodMk continuous_snd).tendsto (u, f u)
  filter_upwards [continuous_fst.continuousAt.eventually_mem (Θ.open_source.mem_nhds hsource),
    hpr.eventually htarget, hpr.eventually (dfu.eventually_implicitFunction_eq if₂u)]
    with ⟨⟨z, v⟩, w⟩ h₁ h₂ h₃
  simp only [Prod.swap_prod_mk] at h₂ h₃
  -- `f (z, v) = w` says that `Θ (z, v) = (w, z)`, that is, `(z, v) = Θ.symm (w, z)`
  have hΘsymm : Θ.symm (w, z) = (z, dfu.localInverseOfProdDomain if₂u z w) :=
    φ.implicitFunction_apply.symm.trans h₃
  rw [show f (z, v) = w ↔ Θ (z, v) = (w, z) by simp [hΘ], ← Θ.eq_symm_apply h₁ h₂, hΘsymm,
    Prod.mk_right_inj, eq_comm]

/-- **Local uniqueness of continuous solutions.** A function `g` which is continuous at
`(u.1, f u)`, takes the value `u.2` there and solves `f (z, g z w) = w` near that point agrees
with `localInverseOfProdDomain` near that point. -/
theorem eventuallyEq_localInverseOfProdDomain {g : E₁ → F → E₂}
    (hg : ContinuousAt (uncurry g) (u.1, f u)) (hgu : g u.1 (f u) = u.2)
    (hfg : ∀ᶠ p in 𝓝 (u.1, f u), f (p.1, g p.1 p.2) = p.2) :
    uncurry g =ᶠ[𝓝 (u.1, f u)] uncurry (dfu.localInverseOfProdDomain if₂u) := by
  have ht : Tendsto (fun p : E₁ × F ↦ ((p.1, uncurry g p), p.2)) (𝓝 (u.1, f u)) (𝓝 (u, f u)) := by
    have := ((continuousAt_fst.prodMk hg).prodMk continuousAt_snd).tendsto
    simpa [hgu] using this
  filter_upwards [hfg, ht.eventually (dfu.eventually_apply_eq_iff_localInverseOfProdDomain if₂u)]
    with p hp hp'
  exact (hp'.1 hp).symm

/-- The derivative of `localInverseOfProdDomain` at `(u.1, f u)` is
`(a, b) ↦ (∂f/∂v)⁻¹ (b - ∂f/∂z a)`. -/
theorem hasStrictFDerivAt_uncurry_localInverseOfProdDomain :
    HasStrictFDerivAt (uncurry (dfu.localInverseOfProdDomain if₂u))
      ((f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L
        (.snd 𝕜 E₁ F - f'u ∘L .inl 𝕜 E₁ E₂ ∘L .fst 𝕜 E₁ F)) (u.1, f u) := by
  set φ : ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ := dfu.implicitFunctionDataOfProdDomain if₂u
  -- the map is strictly differentiable, as a component of a local inverse
  obtain ⟨D, hD⟩ : ∃ D : E₁ × F →L[𝕜] E₂,
      HasStrictFDerivAt (uncurry (dfu.localInverseOfProdDomain if₂u)) D (u.1, f u) := by
    obtain ⟨D', hD'⟩ : ∃ D' : F × E₁ →L[𝕜] E₁ × E₂,
        HasStrictFDerivAt (uncurry φ.implicitFunction) D' (u.1, f u).swap := by
      rw [← prodFun_pt dfu if₂u, ImplicitFunctionData.implicitFunction_def, uncurry_curry,
        ← localInverse_def]
      exact ⟨_, φ.hasStrictFDerivAt.to_localInverse⟩
    have hswap : HasStrictFDerivAt (Prod.swap : E₁ × F → F × E₁)
        ((ContinuousLinearMap.snd 𝕜 E₁ F).prod (.fst 𝕜 E₁ F)) (u.1, f u) :=
      hasStrictFDerivAt_snd.prodMk hasStrictFDerivAt_fst
    have h := hasStrictFDerivAt_snd.comp (u.1, f u) (hD'.comp (u.1, f u) hswap)
    rw [uncurry_localInverseOfProdDomain]
    exact ⟨_, h⟩
  -- differentiating `f (z, F (z, w)) = w` identifies its derivative
  have hcomp : HasFDerivAt (fun p : E₁ × F ↦ f (p.1, dfu.localInverseOfProdDomain if₂u p.1 p.2))
      (f'u ∘L (ContinuousLinearMap.fst 𝕜 E₁ F).prod D) (u.1, f u) := by
    have hdf : HasFDerivAt f f'u (u.1, dfu.localInverseOfProdDomain if₂u u.1 (f u)) := by
      rw [localInverseOfProdDomain_apply_self]
      exact dfu.hasFDerivAt
    exact hdf.comp (u.1, f u) (hasFDerivAt_fst.prodMk hD.hasFDerivAt)
  have hD_eq : f'u ∘L (ContinuousLinearMap.fst 𝕜 E₁ F).prod D = .snd 𝕜 E₁ F :=
    hcomp.unique (hasFDerivAt_snd.congr_of_eventuallyEq
      (dfu.eventually_apply_localInverseOfProdDomain if₂u))
  convert hD using 1
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hx : f'u (x.1, D x) = x.2 := congrArg (fun L : E₁ × F →L[𝕜] F ↦ L x) hD_eq
  have hsplit : f'u (x.1, D x) = f'u (x.1, 0) + (f'u ∘L .inr 𝕜 E₁ E₂) (D x) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.inl_apply]
  rw [if₂u.inverse_apply_eq, ← hx, hsplit, add_sub_cancel_left]

/-- **The analytic implicit function theorem with a varying level.** If `f` is analytic at `u`,
then `localInverseOfProdDomain` is jointly analytic in the parameter and the level at
`(u.1, f u)`. -/
theorem analyticAt_uncurry_localInverseOfProdDomain (hf : AnalyticAt 𝕜 f u) :
    AnalyticAt 𝕜 (uncurry (dfu.localInverseOfProdDomain if₂u)) (u.1, f u) := by
  set φ : ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ := dfu.implicitFunctionDataOfProdDomain if₂u
  have h : AnalyticAt 𝕜 (uncurry φ.implicitFunction) (u.1, f u).swap := by
    rw [← prodFun_pt dfu if₂u]
    exact φ.analyticAt_implicitFunction (by simpa [φ] using hf) (by simpa [φ] using analyticAt_fst)
  rw [uncurry_localInverseOfProdDomain]
  exact analyticAt_snd.comp (h.comp (analyticAt_snd.prod analyticAt_fst))

end HasStrictFDerivAt

end General

section ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}
  (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible)

/-- **The `C^n` implicit function theorem with a varying level.** If `f` is `C^n` at `u`, with
`n ≠ 0`, then `localInverseOfProdDomain` is jointly `C^n` in the parameter and the level at
`(u.1, f u)`. -/
theorem contDiffAt_uncurry_localInverseOfProdDomain {n : ℕ∞ω} (hf : ContDiffAt 𝕜 n f u)
    (hn : n ≠ 0) :
    ContDiffAt 𝕜 n (uncurry (dfu.localInverseOfProdDomain if₂u)) (u.1, f u) := by
  set φ : ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ := dfu.implicitFunctionDataOfProdDomain if₂u
  have h : ContDiffAt 𝕜 n (uncurry φ.implicitFunction) (u.1, f u).swap := by
    rw [← prodFun_pt dfu if₂u]
    exact φ.contDiffAt_implicitFunction (by simpa [φ] using hf) (by simpa [φ] using contDiffAt_fst)
      hn
  rw [uncurry_localInverseOfProdDomain]
  exact contDiffAt_snd.comp _ (h.comp _ (contDiffAt_snd.prodMk contDiffAt_fst))

end HasStrictFDerivAt

end ContDiff

section Holomorphic

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
  [FiniteDimensional ℂ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
  [FiniteDimensional ℂ E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[ℂ] F}
  (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr ℂ E₁ E₂).IsInvertible)

/-- **The holomorphic implicit function theorem with a varying level.** If `f` is complex
differentiable on a neighbourhood of `u` in a finite-dimensional complex space, then
`localInverseOfProdDomain` is jointly complex differentiable in the parameter and the level at
every point of a neighbourhood of `(u.1, f u)`. -/
theorem eventually_differentiableAt_uncurry_localInverseOfProdDomain {s : Set (E₁ × E₂)}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 u) :
    ∀ᶠ p in 𝓝 (u.1, f u), DifferentiableAt ℂ (uncurry (dfu.localInverseOfProdDomain if₂u)) p :=
  (dfu.analyticAt_uncurry_localInverseOfProdDomain if₂u
    (hf.analyticAt_of_finiteDimensional hs)).eventually_analyticAt.mono
      fun _ h ↦ h.differentiableAt

end HasStrictFDerivAt

end Holomorphic
