/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smoothness and differentiation of paired wedges

Families of alternating maps can be wedged without loss of regularity. The pairing itself may
vary: differentiating the paired wedge gives three terms, one for each input. For a fixed pairing
the first term vanishes. The relative statements apply to arbitrary sets, including chart ranges
of manifolds with boundary or corners.

The construction uses `ContinuousAlternatingMap.pairedWedgeCLM` and Mathlib's calculus of
application of continuous linear maps. These results provide the coefficient calculus for wedge
products of smooth bundle-valued forms. The wedge normalization follows John M. Lee,
*Introduction to Smooth Manifolds*, second edition, Chapter 14.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousAlternatingMap

variable {X E F₁ F₂ F₃ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {k l : ℕ} {n : WithTop ℕ∞} {s : Set X} {x : X}
  {μ : X → F₁ →L[ℝ] F₂ →L[ℝ] F₃}
  {φ : X → E [⋀^Fin k]→L[ℝ] F₁} {ψ : X → E [⋀^Fin l]→L[ℝ] F₂}

/-- The paired wedge of `C^n` families and a `C^n` pairing is `C^n` within a set at a point. -/
@[fun_prop] theorem _root_.ContDiffWithinAt.pairedWedge
    (hμ : ContDiffWithinAt ℝ n μ s x) (hφ : ContDiffWithinAt ℝ n φ s x)
    (hψ : ContDiffWithinAt ℝ n ψ s x) :
    ContDiffWithinAt ℝ n (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) s x := by
  -- Cache canonical operator-space instances for the nested continuous-linear-map calculus.
  let : NormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let W := pairedWedgeCLM (E := E) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) (k := k) (l := l)
  simpa only [W, Function.comp_apply, pairedWedgeCLM_apply] using
    ((W.contDiff.comp_contDiffWithinAt hμ).clm_apply
      hφ).clm_apply hψ

/-- The paired wedge preserves `C^n` regularity on an arbitrary set. -/
@[fun_prop] theorem _root_.ContDiffOn.pairedWedge
    (hμ : ContDiffOn ℝ n μ s) (hφ : ContDiffOn ℝ n φ s) (hψ : ContDiffOn ℝ n ψ s) :
    ContDiffOn ℝ n (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) s :=
  fun x hx ↦ (hμ x hx).pairedWedge (hφ x hx) (hψ x hx)

/-- The paired wedge preserves `C^n` regularity at a point. -/
@[fun_prop] theorem _root_.ContDiffAt.pairedWedge
    (hμ : ContDiffAt ℝ n μ x) (hφ : ContDiffAt ℝ n φ x) (hψ : ContDiffAt ℝ n ψ x) :
    ContDiffAt ℝ n (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) x := by
  rw [← contDiffWithinAt_univ] at hμ hφ hψ ⊢
  exact hμ.pairedWedge hφ hψ

/-- The paired wedge of `C^n` families and a `C^n` pairing is `C^n`. -/
@[fun_prop] theorem _root_.ContDiff.pairedWedge
    (hμ : ContDiff ℝ n μ) (hφ : ContDiff ℝ n φ) (hψ : ContDiff ℝ n ψ) :
    ContDiff ℝ n (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ hμ.contDiffAt.pairedWedge hφ.contDiffAt hψ.contDiffAt

/-- The paired wedge of differentiable families is differentiable within a set at a point. -/
@[fun_prop] theorem _root_.DifferentiableWithinAt.pairedWedge
    (hμ : DifferentiableWithinAt ℝ μ s x) (hφ : DifferentiableWithinAt ℝ φ s x)
    (hψ : DifferentiableWithinAt ℝ ψ s x) :
    DifferentiableWithinAt ℝ (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) s x := by
  -- Cache canonical operator-space instances for the nested continuous-linear-map calculus.
  let : NormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let W := pairedWedgeCLM (E := E) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) (k := k) (l := l)
  simpa only [W, Function.comp_apply, pairedWedgeCLM_apply] using
    ((W.differentiableAt.comp_differentiableWithinAt x hμ).clm_apply
      (H := (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) hφ).clm_apply
      (H := E [⋀^Fin (k + l)]→L[ℝ] F₃) hψ

/-- The paired wedge of differentiable families is differentiable on a set. -/
@[fun_prop] theorem _root_.DifferentiableOn.pairedWedge
    (hμ : DifferentiableOn ℝ μ s) (hφ : DifferentiableOn ℝ φ s)
    (hψ : DifferentiableOn ℝ ψ s) :
    DifferentiableOn ℝ (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) s :=
  fun x hx ↦ (hμ x hx).pairedWedge (hφ x hx) (hψ x hx)

/-- The paired wedge of differentiable families is differentiable at a point. -/
@[fun_prop] theorem _root_.DifferentiableAt.pairedWedge
    (hμ : DifferentiableAt ℝ μ x) (hφ : DifferentiableAt ℝ φ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    DifferentiableAt ℝ (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) x := by
  rw [← differentiableWithinAt_univ] at hμ hφ hψ ⊢
  exact hμ.pairedWedge hφ hψ

/-- The paired wedge of differentiable families is differentiable. -/
@[fun_prop] theorem _root_.Differentiable.pairedWedge
    (hμ : Differentiable ℝ μ) (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) :
    Differentiable ℝ (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) :=
  fun x ↦ (hμ x).pairedWedge (hφ x) (hψ x)

/-- Derivative witnesses for a pairing and two forms give the three-term derivative of their
paired wedge within an arbitrary set. -/
theorem _root_.HasFDerivWithinAt.pairedWedge
    {μ' : X →L[ℝ] F₁ →L[ℝ] F₂ →L[ℝ] F₃}
    {φ' : X →L[ℝ] E [⋀^Fin k]→L[ℝ] F₁} {ψ' : X →L[ℝ] E [⋀^Fin l]→L[ℝ] F₂}
    (hμ : HasFDerivWithinAt μ μ' s x) (hφ : HasFDerivWithinAt φ φ' s x)
    (hψ : HasFDerivWithinAt ψ ψ' s x) :
    HasFDerivWithinAt (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y))
      ((pairedWedgeCLM (μ x) (φ x)).comp ψ' +
        ((pairedWedgeCLM (μ x)).comp φ' +
          ((pairedWedgeCLM (E := E) (k := k) (l := l)).comp μ').flip
            (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) (E' := X) (F' := E [⋀^Fin k]→L[ℝ] F₁)
            (G' := (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] E [⋀^Fin (k + l)]→L[ℝ] F₃)
            (φ x)).flip (ψ x)) s x := by
  -- Cache canonical operator-space instances for the nested continuous-linear-map calculus.
  let : NormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let W := pairedWedgeCLM (E := E) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) (k := k) (l := l)
  have h := ((W.hasFDerivAt.comp_hasFDerivWithinAt x hμ).clm_apply
    (H := (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃))
    hφ).clm_apply (H := E [⋀^Fin (k + l)]→L[ℝ] F₃) hψ
  simpa only [W, Function.comp_apply, pairedWedgeCLM_apply] using h

/-- Derivative witnesses for a pairing and two forms give the three-term derivative of their
paired wedge at a point. -/
theorem _root_.HasFDerivAt.pairedWedge
    {μ' : X →L[ℝ] F₁ →L[ℝ] F₂ →L[ℝ] F₃}
    {φ' : X →L[ℝ] E [⋀^Fin k]→L[ℝ] F₁} {ψ' : X →L[ℝ] E [⋀^Fin l]→L[ℝ] F₂}
    (hμ : HasFDerivAt μ μ' x) (hφ : HasFDerivAt φ φ' x) (hψ : HasFDerivAt ψ ψ' x) :
    HasFDerivAt (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y))
      ((pairedWedgeCLM (μ x) (φ x)).comp ψ' +
        ((pairedWedgeCLM (μ x)).comp φ' +
          ((pairedWedgeCLM (E := E) (k := k) (l := l)).comp μ').flip
            (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) (E' := X) (F' := E [⋀^Fin k]→L[ℝ] F₁)
            (G' := (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] E [⋀^Fin (k + l)]→L[ℝ] F₃)
            (φ x)).flip (ψ x)) x := by
  -- Cache canonical operator-space instances for the nested continuous-linear-map calculus.
  let : NormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  rw [← hasFDerivWithinAt_univ] at hμ hφ hψ ⊢
  exact hμ.pairedWedge hφ hψ

/-- Differentiating a paired wedge within a unique-differentiability set gives one term for
each of the pairing and the two forms. -/
theorem fderivWithin_pairedWedge_apply (hs : UniqueDiffWithinAt ℝ s x)
    (hμ : DifferentiableWithinAt ℝ μ s x) (hφ : DifferentiableWithinAt ℝ φ s x)
    (hψ : DifferentiableWithinAt ℝ ψ s x) (v : X) :
    fderivWithin ℝ (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) s x v =
      pairedWedge (fderivWithin ℝ μ s x v) (fderivWithin ℝ μ s x v).continuous₂ (φ x) (ψ x) +
        pairedWedge (μ x) (μ x).continuous₂ (fderivWithin ℝ φ s x v) (ψ x) +
        pairedWedge (μ x) (μ x).continuous₂ (φ x) (fderivWithin ℝ ψ s x v) := by
  -- Cache canonical operator-space instances for the nested continuous-linear-map calculus.
  let : NormedAddCommGroup
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] F₃)) := inferInstance
  let : NormedAddCommGroup
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ
      ((E [⋀^Fin k]→L[ℝ] F₁) →L[ℝ] (E [⋀^Fin l]→L[ℝ] F₂) →L[ℝ]
        E [⋀^Fin (k + l)]→L[ℝ] F₃) := inferInstance
  let : NormedAddCommGroup (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  let : NormedSpace ℝ (F₁ →L[ℝ] F₂ →L[ℝ] F₃) := inferInstance
  rw [(hμ.hasFDerivWithinAt.pairedWedge hφ.hasFDerivWithinAt hψ.hasFDerivWithinAt).fderivWithin hs]
  simp [ContinuousLinearMap.flip_apply, add_comm, add_left_comm, add_assoc]

/-- Differentiating a paired wedge gives one term for each of its three inputs. -/
theorem fderiv_pairedWedge_apply (hμ : DifferentiableAt ℝ μ x)
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) (v : X) :
    fderiv ℝ (fun y ↦ pairedWedge (μ y) (μ y).continuous₂ (φ y) (ψ y)) x v =
      pairedWedge (fderiv ℝ μ x v) (fderiv ℝ μ x v).continuous₂ (φ x) (ψ x) +
        pairedWedge (μ x) (μ x).continuous₂ (fderiv ℝ φ x v) (ψ x) +
        pairedWedge (μ x) (μ x).continuous₂ (φ x) (fderiv ℝ ψ x v) := by
  simpa only [fderivWithin_univ] using
    fderivWithin_pairedWedge_apply uniqueDiffWithinAt_univ hμ.differentiableWithinAt
      hφ.differentiableWithinAt hψ.differentiableWithinAt v

end TauCeti
