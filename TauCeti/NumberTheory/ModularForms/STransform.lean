/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The `S`-transformation of the complex extension of a slash-invariant form

For a weight-`k` slash-invariant form `f` whose group `Γ ≤ GL(2, ℝ)` contains the image of
`S = !![0, -1; 1, 0]`, the transformation law `f (S • τ) = τ ^ k * f τ` transports through
`ofComplex` to the identity `(⇑f ∘ ofComplex) (-1 / w) = w ^ k * (⇑f ∘ ofComplex) w` on the
open upper half-plane. Through the same identity the extension is differentiable at `w` exactly
when it is differentiable at `-1 / w`, and differentiating it expresses the logarithmic
derivative at `w` through the logarithmic derivative at `-1 / w` up to the weight term `k / w` —
the integrand identity behind the arc self-pairing of the valence-formula contour integral.

## Main declarations

* `TauCeti.ModularForm.comp_ofComplex_S_transform`: the `S`-transformation law of
  `⇑f ∘ ofComplex`.
* `TauCeti.ModularForm.differentiableAt_comp_ofComplex_S_transform_iff`: differentiability
  at `-1 / w` is equivalent to differentiability at `w`.
* `TauCeti.ModularForm.logDeriv_comp_ofComplex_S_transform`: the `S`-transformation law
  of the logarithmic derivative.
-/

public section

open Complex UpperHalfPlane

open scoped MatrixGroups Topology

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The `S`-transformation law of the complex extension of a slash-invariant form, at the
points of the open upper half-plane. -/
theorem comp_ofComplex_S_transform [SlashInvariantFormClass F Γ k] (f : F)
    (hS : (ModularGroup.S : GL (Fin 2) ℝ) ∈ Γ) {w : ℂ} (hw : 0 < w.im) :
    (⇑f ∘ ofComplex) (-1 / w) = w ^ k * (⇑f ∘ ofComplex) w := by
  have him := im_neg_one_div_pos hw
  have hSw : ModularGroup.S • (⟨w, hw⟩ : ℍ) = ⟨-1 / w, him⟩ :=
    UpperHalfPlane.ext (ModularGroup.coe_S_smul _)
  have hf := congrFun (SlashInvariantForm.slash_action_eqn f _ hS) ⟨w, hw⟩
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, ModularGroup.denom_S, coe_mk,
    hSw] at hf
  have hw0 : w ≠ 0 := fun h ↦ absurd hw (by simp [h])
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos him]
  rw [← hf, zpow_neg]
  field_simp

/-- Differentiability of the complex extension of a slash-invariant form transports
across the `S`-orbit: at a point `w` of the open upper half-plane, the extension is
differentiable at `-1 / w` if and only if it is differentiable at `w`. -/
theorem differentiableAt_comp_ofComplex_S_transform_iff [SlashInvariantFormClass F Γ k]
    (f : F) (hS : (ModularGroup.S : GL (Fin 2) ℝ) ∈ Γ) {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℂ (⇑f ∘ ofComplex) (-1 / w) ↔
      DifferentiableAt ℂ (⇑f ∘ ofComplex) w := by
  have hinv (v : ℂ) : -1 / (-1 / v) = v := by simp [neg_div]
  suffices key : ∀ {w : ℂ}, 0 < w.im → DifferentiableAt ℂ (⇑f ∘ ofComplex) w →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (-1 / w) from
    ⟨fun hd ↦ hinv w ▸ key (im_neg_one_div_pos hw) hd, key hw⟩
  intro w hw hd
  have him := im_neg_one_div_pos hw
  have hiw0 : (-1 : ℂ) / w ≠ 0 := fun h ↦ absurd him (by simp [h])
  have hcomp : DifferentiableAt ℂ (fun v : ℂ ↦ (⇑f ∘ ofComplex) (-1 / v)) (-1 / w) :=
    ((hinv w).symm ▸ hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) (-1 / (-1 / w))).comp _
      ((differentiableAt_const _).div differentiableAt_id hiw0)
  have heq : (⇑f ∘ ofComplex) =ᶠ[𝓝 (-1 / w)]
      fun v ↦ (⇑f ∘ ofComplex) (-1 / v) / v ^ k := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds him] with v hv
    have hv0 : v ≠ 0 := fun h ↦ absurd hv (by simp [h])
    rw [comp_ofComplex_S_transform f hS hv, mul_div_cancel_left₀ _ (zpow_ne_zero k hv0)]
  exact (hcomp.div (differentiableAt_zpow.mpr (.inl hiw0))
    (zpow_ne_zero k hiw0)).congr_of_eventuallyEq heq

/-- The `S`-transformation law of the logarithmic derivative of the complex extension of
a slash-invariant form, at points of the open upper half-plane where the extension is
differentiable and does not vanish. -/
theorem logDeriv_comp_ofComplex_S_transform [SlashInvariantFormClass F Γ k] (f : F)
    (hS : (ModularGroup.S : GL (Fin 2) ℝ) ∈ Γ) {w : ℂ} (hw : 0 < w.im)
    (hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) w) (hfw : (⇑f ∘ ofComplex) w ≠ 0) :
    logDeriv (⇑f ∘ ofComplex) w =
      logDeriv (⇑f ∘ ofComplex) (-1 / w) / w ^ 2 - k / w := by
  have hw0 : w ≠ 0 := fun h ↦ absurd hw (by simp [h])
  have h_eq : (⇑f ∘ ofComplex) ∘ (fun v ↦ -1 / v) =ᶠ[𝓝 w] (· ^ k) * (⇑f ∘ ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with v hv
    exact comp_ofComplex_S_transform f hS hv
  have h_comp := logDeriv_comp (g := fun v ↦ -1 / v)
    ((differentiableAt_comp_ofComplex_S_transform_iff f hS hw).2 hd)
    ((differentiableAt_const (-1 : ℂ)).div differentiableAt_id hw0)
  have h_deriv : deriv (fun v : ℂ ↦ -1 / v) w = 1 / w ^ 2 := by
    simp [neg_div, deriv_inv]
  rw [(logDeriv_congr_nhds h_eq).eq_of_nhds, logDeriv_mul (f := (· ^ k)) w
    (zpow_ne_zero k hw0) hfw (differentiableAt_zpow.mpr (.inl hw0)) hd, logDeriv_zpow,
    h_deriv] at h_comp
  linear_combination h_comp

end ModularForm

end TauCeti

end
