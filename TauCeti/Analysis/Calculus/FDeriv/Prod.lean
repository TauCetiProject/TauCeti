/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives of separated sums on a product

A function on a product `E × F` of the form `φ ∘ Prod.fst + ψ ∘ Prod.snd`, with `φ : E → G` and
`ψ : F → G`, is a *separated sum*: it depends on the two coordinates through two independent
functions. Its derivative at `(a, b)` is the coproduct `φ'.coprod ψ'` of the derivatives of the
two summands, so it vanishes exactly when both summands have vanishing derivative. This is the
first-order input for the study of critical points of separated sums, for instance of Morse
functions on a product manifold.

## Main declarations

* `HasFDerivAt.comp_fst_add_comp_snd`: the derivative of a separated sum is the coproduct of the
  derivatives of its summands.
* `TauCeti.fderiv_comp_fst_add_comp_snd`: the same for the totalized derivative.
* `TauCeti.fderiv_comp_fst_add_comp_snd_eq_zero_iff`: a separated sum of differentiable functions
  is critical at `(a, b)` exactly when both summands are critical at `a` and `b`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {φ : E → G} {ψ : F → G} {φ' : E →L[𝕜] G} {ψ' : F →L[𝕜] G} {a : E} {b : F}

/-- The derivative of a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` at `(a, b)` is the coproduct
of the derivatives of `φ` at `a` and of `ψ` at `b`. -/
theorem _root_.HasFDerivAt.comp_fst_add_comp_snd (hφ : HasFDerivAt φ φ' a)
    (hψ : HasFDerivAt ψ ψ' b) :
    HasFDerivAt (φ ∘ Prod.fst + ψ ∘ Prod.snd) (φ'.coprod ψ') (a, b) := by
  have h := (hφ.comp (a, b) (hasFDerivAt_fst (𝕜 := 𝕜) (p := (a, b)))).add
    (hψ.comp (a, b) (hasFDerivAt_snd (𝕜 := 𝕜) (p := (a, b))))
  rwa [ContinuousLinearMap.comp_fst_add_comp_snd] at h

/-- The totalized derivative of a separated sum of differentiable functions is the coproduct of
the derivatives of its summands. -/
@[simp]
theorem fderiv_comp_fst_add_comp_snd (hφ : DifferentiableAt 𝕜 φ a) (hψ : DifferentiableAt 𝕜 ψ b) :
    fderiv 𝕜 (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) = (fderiv 𝕜 φ a).coprod (fderiv 𝕜 ψ b) :=
  (hφ.hasFDerivAt.comp_fst_add_comp_snd hψ.hasFDerivAt).fderiv

/-- A separated sum of differentiable functions is critical at `(a, b)` exactly when both
summands are critical at `a` and at `b`. This is not a `simp` lemma: the `@[simp]` lemma
`TauCeti.fderiv_comp_fst_add_comp_snd` already rewrites its left-hand side to
`(fderiv 𝕜 φ a).coprod (fderiv 𝕜 ψ b) = 0`. -/
theorem fderiv_comp_fst_add_comp_snd_eq_zero_iff (hφ : DifferentiableAt 𝕜 φ a)
    (hψ : DifferentiableAt 𝕜 ψ b) :
    fderiv 𝕜 (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) = 0 ↔
      fderiv 𝕜 φ a = 0 ∧ fderiv 𝕜 ψ b = 0 := by
  rw [fderiv_comp_fst_add_comp_snd hφ hψ]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext v
      simpa using congrArg (fun L : E × F →L[𝕜] G ↦ L (v, 0)) h
    · ext w
      simpa using congrArg (fun L : E × F →L[𝕜] G ↦ L (0, w)) h
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    ext <;> simp

end TauCeti

end
