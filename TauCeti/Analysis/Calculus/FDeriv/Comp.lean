/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

import Mathlib.Tactic.Abel

/-!
# Derivatives under composition and changes of coordinates

By the chain rule, the differential of `f ∘ φ` at `b` is the differential of `f` at `φ b`
precomposed with that of `φ` at `b`. When the latter is invertible, one vanishes exactly when the
other does, so criticality does not depend on the coordinates.

At a fixed point of a map preserving the germ of `f`, the derivative of `f` is unchanged by
precomposition with the derivative of that map.

## Main results

* `HasFDerivAt.comp_eq_of_eventuallyEq`: invariance of a germ at a fixed point implies invariance
  of its derivative.
* `HasFDerivAt.injective_of_eventuallyEq_id`: a map with a differentiable local left inverse has
  injective derivative.
* `TauCeti.fderiv_comp_eq_zero_iff_of_isInvertible`: `b` is a critical point of `f ∘ φ` exactly
  when `φ b` is a critical point of `f`, if the differential of `φ` at `b` is invertible.
* `ContinuousLinearMap.fderiv_comp_right_of_rightInverse`,
  `ContinuousLinearMap.fderiv_comp_left_of_leftInverse`: the chain rule for precomposition with a
  split surjection and postcomposition with a split injection, with no differentiability
  assumption.
* `TauCeti.fderiv_comp_add_smul`: the derivative of `w ↦ f (c + a • w)` is `a` times that of `f`
  at `c + a • w`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- If a map fixes `x` and preserves the germ of `f` there, its derivative preserves the
derivative of `f` by precomposition. -/
theorem _root_.HasFDerivAt.comp_eq_of_eventuallyEq {f : E → F} {f' : E →L[𝕜] F}
    {φ : E → E} {φ' : E →L[𝕜] E} {x : E} (hf : HasFDerivAt f f' x)
    (hφ : HasFDerivAt φ φ' x) (hfix : φ x = x)
    (hinv : f ∘ φ =ᶠ[nhds x] f) : f'.comp φ' = f' := by
  have hfφ : HasFDerivAt f f' (φ x) := by simpa only [hfix] using hf
  exact (hfφ.comp x hφ).unique (hf.congr_of_eventuallyEq hinv)

/-- If `g ∘ f` is the identity near `x` and `g` is differentiable at `f x`, the derivative of `f`
at `x` is injective. -/
theorem _root_.HasFDerivAt.injective_of_eventuallyEq_id {f : E → F} {g : F → E}
    {f' : E →L[𝕜] F} {g' : F →L[𝕜] E} {x : E} (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' (f x)) (hgf : g ∘ f =ᶠ[nhds x] id) : Function.Injective f' := by
  have hcomp := ((hg.comp x hf).congr_of_eventuallyEq hgf.symm).unique (hasFDerivAt_id x)
  exact Function.LeftInverse.injective fun a => by
    simpa using congrArg (fun L : E →L[𝕜] E => L a) hcomp

/-- **Criticality does not depend on the coordinates.** If `f` is differentiable at `φ b` and
the differential of `φ` at `b` is invertible, then `b` is a critical
point of `f ∘ φ` exactly when `φ b` is a critical point of `f`. -/
theorem fderiv_comp_eq_zero_iff_of_isInvertible {f : E → G} {φ : F → E} {b : F}
    (hf : DifferentiableAt 𝕜 f (φ b)) (hinv : (fderiv 𝕜 φ b).IsInvertible) :
    fderiv 𝕜 (f ∘ φ) b = 0 ↔ fderiv 𝕜 f (φ b) = 0 := by
  have hφ := differentiableAt_of_isInvertible_fderiv hinv
  obtain ⟨e, he⟩ := hinv
  -- The differential of `f ∘ φ` at `b` is that of `f` at `φ b` precomposed with the equivalence
  -- `e`, so one vanishes exactly when the other does.
  rw [fderiv_comp (x := b) hf hφ, ← he]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; ext u; simp⟩
  ext u
  simpa using congrArg (fun L : F →L[𝕜] G ↦ L (e.symm u)) h

/-- Precomposing a real-valued function with scalar multiplication scales the norm of its
Fréchet derivative by the absolute value of the scalar. -/
theorem norm_fderiv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (a : ℝ) (x : E) :
    ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ = |a| * ‖fderiv ℝ f (a • x)‖ := by
  rw [_root_.fderiv_comp_smul a, norm_smul, Real.norm_eq_abs]

/-- **The chain rule for an affine change of variables.** The derivative of `w ↦ f (c + a • w)`
at `w` is `a` times the derivative of `f` at `c + a • w`. Like `fderiv_comp_smul`, this needs no
differentiability of `f`. -/
theorem fderiv_comp_add_smul (f : E → F) (c : E) (a : 𝕜) (w : E) :
    fderiv 𝕜 (fun w ↦ f (c + a • w)) w = a • fderiv 𝕜 f (c + a • w) := by
  rw [_root_.fderiv_comp_smul (f := fun y ↦ f (c + y)), fderiv_comp_add_left]

/-- For a continuous linear map `g` with a continuous linear right inverse `s`, the derivative of
`h ∘ g` at `x` is the derivative of `h` at `g x` composed with `g`, for every `h` (no
differentiability assumption). -/
theorem _root_.ContinuousLinearMap.fderiv_comp_right_of_rightInverse (g : G →L[𝕜] E) (s : E →L[𝕜] G)
    (hgs : Function.RightInverse s g) (h : E → F) (x : G) :
    fderiv 𝕜 (h ∘ g) x = (fderiv 𝕜 h (g x)).comp g := by
  by_cases hd : DifferentiableAt 𝕜 h (g x)
  · rw [fderiv_comp x hd g.differentiableAt, g.fderiv]
  · have hnd : ¬ DifferentiableAt 𝕜 (h ∘ g) x := fun hd' ↦ hd (by
      have hx : (fun u ↦ s u + (x - s (g x))) (g x) = x := by simp
      have hcomp : h = (h ∘ g) ∘ fun u ↦ s u + (x - s (g x)) := by
        funext u
        simp [hgs _]
      have := (hx ▸ hd').comp (g x)
        (by fun_prop : DifferentiableAt 𝕜 (fun u ↦ s u + (x - s (g x))) (g x))
      rwa [← hcomp] at this)
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- For a continuous linear map `Φ` with a continuous linear left inverse `Ψ`, the derivative of
`Φ ∘ k` at `y` is `Φ` composed with the derivative of `k` at `y`, for every `k` (no
differentiability assumption). -/
theorem _root_.ContinuousLinearMap.fderiv_comp_left_of_leftInverse {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Φ : E →L[𝕜] F) (Ψ : F →L[𝕜] E) (hΨΦ : Function.LeftInverse Ψ Φ) (k : X → E) (y : X) :
    fderiv 𝕜 (Φ ∘ k) y = Φ.comp (fderiv 𝕜 k y) := by
  by_cases hd : DifferentiableAt 𝕜 k y
  · rw [fderiv_comp y Φ.differentiableAt hd, Φ.fderiv]
  · have hnd : ¬ DifferentiableAt 𝕜 (Φ ∘ k) y := fun hd' ↦ hd (by
      have : k = Ψ ∘ (Φ ∘ k) := by
        funext u
        simp [hΨΦ _]
      rw [this]
      exact Ψ.differentiableAt.comp y hd')
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

end TauCeti

namespace ContinuousLinearMap

open Function
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂]

/-- A critical point of a map yields a critical point of its slice along a level set of a
functional `φ`. Precisely, let `(φ, ρ)` be jointly injective on `F`, let `γ` parametrize a family of
points along which `φ ∘ f` is locally constant, and let `φ ∘ Df` be nonzero at `γ z`. If
`ρ ∘ f ∘ γ` has surjective derivative at `z`, then `Df` is surjective at `γ z`; equivalently, if
`γ z` is critical for `f`, then `z` is critical for the slice `ρ ∘ f ∘ γ`. -/
theorem surjective_fderiv_of_surjective_fderiv_comp {f : E → F} {γ : G₁ → E} {z : G₁} {c : 𝕜}
    (φ : F →L[𝕜] 𝕜) (ρ : F →L[𝕜] G₂) (hφρ : Injective fun w ↦ (φ w, ρ w))
    (hγ : DifferentiableAt 𝕜 γ z) (hf : DifferentiableAt 𝕜 f (γ z))
    (hconst : (fun w ↦ φ (f (γ w))) =ᶠ[𝓝 z] fun _ ↦ c)
    (hne : ∃ v, φ (fderiv 𝕜 f (γ z) v) ≠ 0)
    (hs : Surjective (fderiv 𝕜 (fun w ↦ ρ (f (γ w))) z)) : Surjective (fderiv 𝕜 f (γ z)) := by
  set T : G₁ →L[𝕜] E := fderiv 𝕜 γ z
  set A : E →L[𝕜] F := fderiv 𝕜 f (γ z)
  have hT : HasFDerivAt γ T z := hγ.hasFDerivAt
  have hA : HasFDerivAt f A (γ z) := hf.hasFDerivAt
  have hGd : HasFDerivAt (fun w ↦ ρ (f (γ w))) (ρ.comp (A.comp T)) z :=
    ρ.hasFDerivAt.comp z (hA.comp z hT)
  have hzero : ∀ w : G₁, φ (A (T w)) = 0 := by
    have hd : HasFDerivAt (fun w ↦ φ (f (γ w))) (φ.comp (A.comp T)) z :=
      φ.hasFDerivAt.comp z (hA.comp z hT)
    have hzero' : φ.comp (A.comp T) = 0 :=
      (hd.congr_of_eventuallyEq hconst.symm).unique (hasFDerivAt_const c z)
    intro w
    simpa using congrArg (fun B : G₁ →L[𝕜] 𝕜 ↦ B w) hzero'
  have hker : ∀ y, φ y = 0 → ∃ u, A u = y := by
    intro y hy
    obtain ⟨w, hw⟩ := hs (ρ y)
    rw [hGd.fderiv] at hw
    refine ⟨T w, hφρ ?_⟩
    exact Prod.ext (by simp only [hzero w, hy]) hw
  obtain ⟨v, hv⟩ := hne
  intro w
  obtain ⟨u, hu⟩ := hker (w - (φ w / φ (A v)) • A v) (by simp [div_mul_cancel₀ _ hv])
  refine ⟨u + (φ w / φ (A v)) • v, ?_⟩
  rw [map_add, map_smul, hu]
  abel

end ContinuousLinearMap
