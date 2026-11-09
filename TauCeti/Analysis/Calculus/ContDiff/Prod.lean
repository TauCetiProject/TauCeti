/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Smoothness of slices of a map on a product

If a map `H` on a product is smooth near every point of `s ×ˢ I`, then each of its slices
`H (·, t)` with `t ∈ I` is smooth on `s` (`TauCeti.contDiffOn_comp_prodMk_left`). For instance,
the time slices of a homotopy smooth near `s × [0, 1]` are smooth on `s`.

A compactly supported `C³` function on `E × ℝ` has compactly supported spatial first and second
derivative fields and a time derivative field of lower smoothness, computing its slice derivatives
at every point (`ContDiff.exists_derivative_fields_of_hasCompactSupport`).
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞} {s : Set E} {I : Set G} {H : E × G → F}

/-- **Slices of a map smooth near `s ×ˢ I` are smooth**: for `t ∈ I`, the slice `H (·, t)` is
smooth on `s`. -/
theorem contDiffOn_comp_prodMk_left (hH : ∀ p ∈ s ×ˢ I, ContDiffAt 𝕜 n H p) {t : G}
    (ht : t ∈ I) : ContDiffOn 𝕜 n (fun x ↦ H (x, t)) s :=
  fun x hx ↦ ((hH (x, t) ⟨hx, ht⟩).comp x (contDiff_prodMk_left t).contDiffAt).contDiffWithinAt

end TauCeti

noncomputable section DerivativeFields

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- These shortcuts keep nested operator-space instance search shallow.
private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The spatial first and second derivative fields and the time derivative field of a compactly
supported `C³` function on a product with a real second factor are compactly supported, of the
expected smoothness, and compute its slice derivatives at every point. -/
theorem ContDiff.exists_derivative_fields_of_hasCompactSupport {f : E × ℝ → F}
    (hf : ContDiff ℝ 3 f) (hs : HasCompactSupport f) :
    ∃ (fx : E × ℝ → E →L[ℝ] F) (fxx : E × ℝ → E →L[ℝ] E →L[ℝ] F) (ft : E × ℝ → F),
      ContDiff ℝ 2 fx ∧ HasCompactSupport fx ∧ ContDiff ℝ 1 fxx ∧ HasCompactSupport fxx ∧
      ContDiff ℝ 2 ft ∧ HasCompactSupport ft ∧
      (∀ p : E × ℝ, HasFDerivAt (fun y ↦ f (y, p.2)) (fx p) p.1) ∧
      (∀ p : E × ℝ, HasFDerivAt (fun y ↦ fx (y, p.2)) (fxx p) p.1) ∧
      (∀ p : E × ℝ, HasDerivAt (fun s : ℝ ↦ f (p.1, s)) (ft p) p.2) := by
  -- Restrict the ordinary derivatives to spatial directions and to the unit time direction.
  let ι : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  let R : (E × ℝ →L[ℝ] F) →L[ℝ] E →L[ℝ] F := ι.precomp F
  let S : (E × ℝ →L[ℝ] E →L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
    ι.precomp (E →L[ℝ] F)
  let fx : E × ℝ → E →L[ℝ] F := R ∘ fderiv ℝ f
  have hfx : ContDiff ℝ 2 fx :=
    (R.contDiff (n := 2)).comp (hf.fderiv_right (by norm_num))
  have hsfx : HasCompactSupport fx := (hs.fderiv ℝ).comp_left (map_zero R)
  let fxx : E × ℝ → E →L[ℝ] E →L[ℝ] F := S ∘ fderiv ℝ fx
  have hfxx : ContDiff ℝ 1 fxx :=
    (S.contDiff (n := 1)).comp (hfx.fderiv_right (by norm_num))
  have hsfxx : HasCompactSupport fxx :=
    (hsfx.fderiv ℝ).comp_left (map_zero S)
  let ft : E × ℝ → F := (ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)) ∘ fderiv ℝ f
  have hft : ContDiff ℝ 2 ft :=
    ((ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)).contDiff (n := 2)).comp
      (hf.fderiv_right (by norm_num))
  have hsft : HasCompactSupport ft :=
    (hs.fderiv ℝ).comp_left (map_zero (ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)))
  refine ⟨fx, fxx, ft, hfx, hsfx, hfxx, hsfxx, hft, hsft, fun p ↦ ?_, fun p ↦ ?_, fun p ↦ ?_⟩
  · simpa [fx, R, ι, Function.comp_def] using
      (hf.differentiable (by norm_num) p).hasFDerivAt_slice_fst
  · simpa [fxx, S, ι, Function.comp_def] using
      (hfx.differentiable (by norm_num) p).hasFDerivAt_slice_fst
  · simpa [ft, Function.comp_def] using
      ((hf.differentiable (by simp) _).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).hasDerivAt

end DerivativeFields
