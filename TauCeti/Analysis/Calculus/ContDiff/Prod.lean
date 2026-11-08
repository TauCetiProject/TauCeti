/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smoothness of slices of a map on a product

If a map `H` on a product is smooth near every point of `s ×ˢ I`, then each of its slices
`H (·, t)` with `t ∈ I` is smooth on `s` (`TauCeti.contDiffOn_comp_prodMk_left`). For instance,
the time slices of a homotopy smooth near `s × [0, 1]` are smooth on `s`.

For a compactly supported `C³` function on `E × ℝ`, the spatial first and second derivative fields
and the time derivative field are compactly supported of the expected smoothness and compute the
derivatives of every translate (`TauCeti.exists_derivative_fields_of_contDiff_three`); the
derivative of a translated slice `y ↦ g (y - a, c)` is `TauCeti.HasFDerivAt.comp_sub_prodMk_left`.
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

/-- **Derivative of a translated slice**: if `g` has derivative `g'` at `(x - a, c)`, then the
slice `y ↦ g (y - a, c)` has derivative `g'.comp (inl 𝕜 E G)` at `x`. -/
theorem HasFDerivAt.comp_sub_prodMk_left {g : E × G → F} {g' : E × G →L[𝕜] F} {a x : E} {c : G}
    (hg : HasFDerivAt g g' (x - a, c)) :
    HasFDerivAt (fun y ↦ g (y - a, c)) (g'.comp (ContinuousLinearMap.inl 𝕜 E G)) x := by
  have h : HasFDerivAt (fun y : E ↦ (y - a, c)) ((ContinuousLinearMap.inl 𝕜 E G).comp
      (ContinuousLinearMap.id 𝕜 E)) x :=
    (hasFDerivAt_prodMk_left (𝕜 := 𝕜) (x - a) c).comp x ((hasFDerivAt_id x).sub_const a)
  simpa [Function.comp_def] using hg.comp x h

noncomputable section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- These shortcuts keep nested operator-space instance search shallow.
private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The spatial first and second derivative fields and the time derivative field of a compactly
supported `C³` function on ordinary space-time are compactly supported, of the expected
smoothness, and compute the derivatives of every translate of the function. -/
theorem exists_derivative_fields_of_contDiff_three {f : E × ℝ → F} (hf : ContDiff ℝ 3 f)
    (hs : HasCompactSupport f) :
    ∃ (fx : E × ℝ → E →L[ℝ] F) (fxx : E × ℝ → E →L[ℝ] E →L[ℝ] F) (ft : E × ℝ → F),
      ContDiff ℝ 2 fx ∧ HasCompactSupport fx ∧ ContDiff ℝ 1 fxx ∧ HasCompactSupport fxx ∧
      ContDiff ℝ 2 ft ∧ HasCompactSupport ft ∧
      (∀ (z : E × ℝ) (t : ℝ) (x : E),
        HasFDerivAt (fun y ↦ f (y - z.1, t - z.2)) (fx (x - z.1, t - z.2)) x) ∧
      (∀ (z : E × ℝ) (t : ℝ) (x : E),
        HasFDerivAt (fun y ↦ fx (y - z.1, t - z.2)) (fxx (x - z.1, t - z.2)) x) ∧
      (∀ (z : E × ℝ) (x : E) (t : ℝ),
        HasDerivAt (fun s : ℝ ↦ f (x - z.1, s - z.2)) (ft (x - z.1, t - z.2)) t) := by
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
  refine ⟨fx, fxx, ft, hfx, hsfx, hfxx, hsfxx, hft, hsft, fun z t x ↦ ?_, fun z t x ↦ ?_,
    fun z x t ↦ ?_⟩
  · simpa [fx, R, ι, Function.comp_def] using
      HasFDerivAt.comp_sub_prodMk_left (hf.differentiable (by norm_num) _).hasFDerivAt
  · simpa [fxx, S, ι, Function.comp_def] using
      HasFDerivAt.comp_sub_prodMk_left (hfx.differentiable (by norm_num) _).hasFDerivAt
  · simpa [ft, Function.comp_def] using
      ((hf.differentiable (by simp) _).hasFDerivAt.comp t
        ((hasFDerivAt_const (x - z.1) t).prodMk ((hasFDerivAt_id t).sub_const z.2))).hasDerivAt

end CompactSupport

end TauCeti
