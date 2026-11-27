/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Laplacian.Basic
public import TauCeti.NumberTheory.MaassForms.Automorphic

/-!
# The hyperbolic Laplacian on automorphic functions

The hyperbolic Laplacian `Δ = -y² (∂ₓ² + ∂ᵧ²)` (`TauCeti.UpperHalfPlane.hyperbolicLaplacian`)
commutes with composition by every isometry `τ ↦ g • τ` of `ℍ`, `g ∈ GL(2, ℝ)`. Two consequences
for weight-zero automorphic functions of level `N` with nebentypus `χ` are recorded here.

* **The reflection.** `Δ` commutes with the reflection `(ι f)(z) = f (-conj z)`, with no
  hypothesis on `f`, so that `ι` acts on the solutions of `Δ f = λ f` for each `λ`.
* **Automorphy.** For `γ ∈ Γ₀(N)` the relation `f ∘ γ = χ(d_γ) f` is preserved by `Δ`, which
  commutes with `γ` and with scalars, so the Laplacian of a `C²` automorphic function is
  automorphic with the same nebentypus. This is what makes the Laplace eigenvalue equation
  `Δ f = λ f` meaningful on the space of automorphic functions.

## Main results

* `TauCeti.MaassForms.hyperbolicLaplacian_reflection`: `Δ (ι f) = ι (Δ f)`.
* `TauCeti.MaassForms.IsAutomorphic.hyperbolicLaplacian`: the Laplacian of a `C²` automorphic
  function is automorphic.

## References

* H. Iwaniec, *Spectral Methods of Automorphic Forms*, second edition, Section 1.2 (the
  invariance of the Laplacian).
-/

public section

open UpperHalfPlane CongruenceSubgroup ModularGroup

open scoped MatrixGroups

namespace TauCeti.MaassForms

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}

/-- **The reflection commutes with the hyperbolic Laplacian**: `Δ (ι f) = ι (Δ f)` for every
`f : ℍ → ℂ`, where `(ι f)(z) = f (-conj z)`. -/
@[simp]
theorem hyperbolicLaplacian_reflection (f : ℍ → ℂ) :
    TauCeti.UpperHalfPlane.hyperbolicLaplacian (reflection f) =
      reflection (TauCeti.UpperHalfPlane.hyperbolicLaplacian f) := by
  have h : reflection f = fun τ ↦ f (J • τ) := funext (reflection_apply f)
  funext z
  rw [reflection_apply, ← TauCeti.UpperHalfPlane.hyperbolicLaplacian_comp_J_smul, h]

/-- **The Laplacian preserves automorphy**: if `f` is automorphic for `Γ₀(N)` with nebentypus `χ`
and `C²` on `ℍ`, then so is `Δ f`, with the same nebentypus. -/
theorem IsAutomorphic.hyperbolicLaplacian (hf : IsAutomorphic N χ f)
    (hf₂ : ∀ z : ℍ, ContDiffAt ℝ 2 (f ∘ ofComplex) z) :
    IsAutomorphic N χ (TauCeti.UpperHalfPlane.hyperbolicLaplacian f) := by
  refine isAutomorphic_iff.mpr fun γ hγ z ↦ ?_
  have h : (fun τ ↦ f ((γ : GL (Fin 2) ℝ) • τ)) = χ (γ 1 1) • f :=
    funext fun τ ↦ hf.apply_smul hγ τ
  rw [sl_moeb, ← TauCeti.UpperHalfPlane.hyperbolicLaplacian_comp_smul (hf₂ _), h,
    TauCeti.UpperHalfPlane.hyperbolicLaplacian_const_smul _ (hf₂ z)]

end TauCeti.MaassForms
