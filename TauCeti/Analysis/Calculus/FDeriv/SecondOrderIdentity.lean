/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Differentiating identities of operator families twice

Let `T : X → E →L[𝕜] F` and `S : X → Y →L[𝕜] E` be families of continuous linear maps that are
`C²` at `x₀`. If `T x (S x y) = c` for `x` near `x₀`, then differentiating once near `x₀` and once
more at `x₀` expresses `T x₀` applied to the second derivative of `S` through the derivatives of
`T` and the lower derivatives of `S`. Over `ℝ`, an orthogonality relation
`⟪ι (S x y), ι (R x f)⟫ = 0` holding near `x₀`, for a fixed continuous linear map `ι` into an inner
product space, differentiates twice in the same way to a relation among four pairings.

These are the second-order forms of `TauCeti.fderiv_apply_apply_eq_neg_of_eventually_const`.
Second derivatives are written as derivatives of first derivatives applied to fixed vectors, such
as `fderiv 𝕜 (fun x ↦ fderiv 𝕜 S x v y) x₀ w`, which take values in `E`.

## Main results

* `TauCeti.apply_fderiv_fun_fderiv_apply_of_eventually`: differentiating `T x (S x y) = c` twice.
* `TauCeti.inner_fderiv_fun_fderiv_of_eventually`: differentiating
  `⟪ι (S x y), ι (R x f)⟫ = 0` twice.
-/

public section

open Filter
open scoped Topology InnerProductSpace

namespace TauCeti

variable {𝕜 E F X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {x₀ : X}

/-- **Differentiating `T x (S x y) = c` twice.** If `T x (S x y) = c` for `x` near `x₀`, for
families `T` and `S` of continuous linear maps that are `C²` at `x₀`, then
`T x₀ S'' = -(T'' (S x₀ y) + T'_v (S'_w y) + T'_w (S'_v y))`, where `S''` and `T''` are the
derivatives along `w` of `x ↦ S'_v(x) y` and `x ↦ T'_v(x)`. -/
theorem apply_fderiv_fun_fderiv_apply_of_eventually {T : X → E →L[𝕜] F} {S : X → Y →L[𝕜] E}
    (hT : ContDiffAt 𝕜 2 T x₀) (hS : ContDiffAt 𝕜 2 S x₀) (y : Y) {c : F}
    (h : ∀ᶠ x in 𝓝 x₀, T x (S x y) = c) (v w : X) :
    T x₀ (fderiv 𝕜 (fun x ↦ fderiv 𝕜 S x v y) x₀ w) =
      -(fderiv 𝕜 (fun x ↦ fderiv 𝕜 T x v (S x₀ y)) x₀ w + fderiv 𝕜 T x₀ v (fderiv 𝕜 S x₀ w y) +
        fderiv 𝕜 T x₀ w (fderiv 𝕜 S x₀ v y)) := by
  have hT' := (hT.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hS' := (hS.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  rw [fderiv_clm_apply_const_apply₂ hS', fderiv_clm_apply_const_apply₂ hT']
  -- Near `x₀`, differentiating the identity gives `T x (S' v y) + T' v (S x y) = 0`.
  have h1 : ∀ᶠ x in 𝓝 x₀, T x (fderiv 𝕜 S x v y) + fderiv 𝕜 T x v (S x y) = 0 := by
    filter_upwards [hT.eventually (by simp), hS.eventually (by simp), h.eventually_nhds]
      with x hTx hSx hx
    have hd := (hTx.differentiableAt (by simp)).hasFDerivAt.clm_apply
      ((hSx.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const y x))
    have h0 : HasFDerivAt (fun x ↦ T x (S x y)) (0 : X →L[𝕜] F) x :=
      (hasFDerivAt_const c x).congr_of_eventuallyEq hx
    simpa using DFunLike.congr_fun (hd.unique h0) v
  -- Differentiating once more at `x₀` along `w`.
  have hd := ((hT.differentiableAt (by simp)).hasFDerivAt.clm_apply
      ((hS'.hasFDerivAt.clm_apply (hasFDerivAt_const v x₀)).clm_apply (hasFDerivAt_const y x₀))).add
    ((hT'.hasFDerivAt.clm_apply (hasFDerivAt_const v x₀)).clm_apply
      ((hS.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const y x₀)))
  have h0 : HasFDerivAt (fun x ↦ T x (fderiv 𝕜 S x v y) + fderiv 𝕜 T x v (S x y))
      (0 : X →L[𝕜] F) x₀ := (hasFDerivAt_const 0 x₀).congr_of_eventuallyEq h1
  have := DFunLike.congr_fun (hd.unique h0) w
  simp only [ContinuousLinearMap.comp_zero, zero_add, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply] at this
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← this]
  abel

/-- **Differentiating an orthogonality relation twice.** If `⟪ι (S x y), ι (R x f)⟫ = 0` for `x`
near `x₀`, for families `S` and `R` of real continuous linear maps that are `C²` at `x₀` and a
continuous linear map `ι` into a real inner product space, then
`⟪ι S'', ι (R x₀ f)⟫ + ⟪ι (S'_v y), ι (R'_w f)⟫ + ⟪ι (S'_w y), ι (R'_v f)⟫ + ⟪ι (S x₀ y), ι R''⟫`
vanishes, where `S''` and `R''` are the derivatives along `w` of `x ↦ S'_v(x) y` and
`x ↦ R'_v(x) f`. -/
theorem inner_fderiv_fun_fderiv_of_eventually {E H X Y Y' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Y']
    [NormedSpace ℝ Y'] {ι : E →L[ℝ] H} {S : X → Y →L[ℝ] E} {R : X → Y' →L[ℝ] E} {x₀ : X}
    (hS : ContDiffAt ℝ 2 S x₀) (hR : ContDiffAt ℝ 2 R x₀) (y : Y) (f : Y')
    (h : ∀ᶠ x in 𝓝 x₀, ⟪ι (S x y), ι (R x f)⟫_ℝ = 0) (v w : X) :
    ⟪ι (fderiv ℝ (fun x ↦ fderiv ℝ S x v y) x₀ w), ι (R x₀ f)⟫_ℝ +
        ⟪ι (fderiv ℝ S x₀ v y), ι (fderiv ℝ R x₀ w f)⟫_ℝ +
      ⟪ι (fderiv ℝ S x₀ w y), ι (fderiv ℝ R x₀ v f)⟫_ℝ +
        ⟪ι (S x₀ y), ι (fderiv ℝ (fun x ↦ fderiv ℝ R x v f) x₀ w)⟫_ℝ = 0 := by
  have hS' := (hS.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hR' := (hR.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  rw [fderiv_clm_apply_const_apply₂ hS', fderiv_clm_apply_const_apply₂ hR']
  -- Near `x₀`, differentiating the identity gives
  -- `⟪ι (S' v y), ι (R f)⟫ + ⟪ι (S y), ι (R' v f)⟫ = 0`.
  have h1 : ∀ᶠ x in 𝓝 x₀, ⟪ι (fderiv ℝ S x v y), ι (R x f)⟫_ℝ +
      ⟪ι (S x y), ι (fderiv ℝ R x v f)⟫_ℝ = 0 := by
    filter_upwards [hS.eventually (by simp), hR.eventually (by simp), h.eventually_nhds]
      with x hSx hRx hx
    have hd := HasFDerivAt.inner ℝ (ι.hasFDerivAt.comp x
      ((hSx.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const y x)))
      (ι.hasFDerivAt.comp x
        ((hRx.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const f x)))
    have h0 : HasFDerivAt (fun x ↦ ⟪ι (S x y), ι (R x f)⟫_ℝ) (0 : X →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hx
    have := DFunLike.congr_fun (hd.unique h0) v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.flip_apply, fderivInnerCLM_apply, zero_apply] at this
    rwa [add_comm]
  -- Differentiating once more at `x₀` along `w`.
  have hSy := (hS.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const y x₀)
  have hRf := (hR.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const f x₀)
  have hd := (HasFDerivAt.inner ℝ (ι.hasFDerivAt.comp x₀
      ((hS'.hasFDerivAt.clm_apply (hasFDerivAt_const v x₀)).clm_apply (hasFDerivAt_const y x₀)))
      (ι.hasFDerivAt.comp x₀ hRf)).add
    (HasFDerivAt.inner ℝ (ι.hasFDerivAt.comp x₀ hSy) (ι.hasFDerivAt.comp x₀
      ((hR'.hasFDerivAt.clm_apply (hasFDerivAt_const v x₀)).clm_apply (hasFDerivAt_const f x₀))))
  have h0 : HasFDerivAt (fun x ↦ ⟪ι (fderiv ℝ S x v y), ι (R x f)⟫_ℝ +
      ⟪ι (S x y), ι (fderiv ℝ R x v f)⟫_ℝ) (0 : X →L[ℝ] ℝ) x₀ :=
    (hasFDerivAt_const (0 : ℝ) x₀).congr_of_eventuallyEq h1
  have := DFunLike.congr_fun (hd.unique h0) w
  simp only [Function.comp_apply, ContinuousLinearMap.comp_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.flip_apply, fderivInnerCLM_apply, zero_apply] at this
  linarith

end TauCeti
