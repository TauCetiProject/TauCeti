/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Analysis.Calculus.Deriv.Matrix
import Mathlib.Tactic.NoncommRing

/-!
# Differentiating paths of symplectic matrices

Differentiating `gᵀ J g = J` along a differentiable path `g` of symplectic matrices gives the
linearized symplectic condition `g'ᵀ J g + gᵀ J g' = 0`
(`HasDerivAt.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero`).

The Conley–Zehnder index of an asymptotic operator `-J ∂ₜ - S(t)` is that of the path solving
`Ψ' = J S Ψ`. A change of frame by a path `g` of symplectic matrices transforms this equation: if
`Ψ' = J S Ψ`, then `Ψ′ = g⁻¹ Ψ P` satisfies `Ψ′' = J S′ Ψ′` with `S′ = gᵀ S g + gᵀ J g'`, for
every constant matrix `P` (`Matrix.hasDerivAt_inv_mul_mul_of_mem_symplecticGroup`).

The matrix `J` is Mathlib's `Matrix.J`, and the symplectic group is defined by `A J Aᵀ = J`.
Matrices carry the operator norm.

## Main results

* `HasDerivAt.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero`: a path of symplectic matrices
  satisfies `g'ᵀ J g + gᵀ J g' = 0`.
* `Matrix.hasDerivAt_inv_mul_mul_of_mem_symplecticGroup`: the frame change transforms `Ψ' = J S Ψ`
  into `Ψ′' = J (gᵀ S g + gᵀ J g') Ψ′`.
-/

public section

open Matrix
open scoped Topology Matrix.Norms.Operator

variable {𝕜 n : Type*} [NontriviallyNormedField 𝕜] [Fintype n] [DecidableEq n]

/-- **The linearized symplectic condition.** The derivative `g'` of a path `g` of symplectic
matrices satisfies `g'ᵀ J g + gᵀ J g' = 0`, the derivative of `gᵀ J g = J`. -/
theorem HasDerivAt.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero
    {g : 𝕜 → Matrix (n ⊕ n) (n ⊕ n) 𝕜} {g' : Matrix (n ⊕ n) (n ⊕ n) 𝕜} {t : 𝕜}
    (hg' : HasDerivAt g g' t) (hg : ∀ᶠ s in 𝓝 t, g s ∈ symplecticGroup n 𝕜) :
    g'ᵀ * J n 𝕜 * g t + (g t)ᵀ * J n 𝕜 * g' = 0 := by
  have h₁ : HasDerivAt (fun s ↦ (g s)ᵀ * J n 𝕜 * g s)
      (g'ᵀ * J n 𝕜 * g t + (g t)ᵀ * J n 𝕜 * g') t :=
    (hg'.matrix_transpose.mul_const (J n 𝕜)).mul hg'
  have h₂ : HasDerivAt (fun s ↦ (g s)ᵀ * J n 𝕜 * g s) 0 t :=
    (hasDerivAt_const t (J n 𝕜)).congr_of_eventuallyEq
      (hg.mono fun s hs ↦ SymplecticGroup.mem_iff'.mp hs)
  exact h₁.unique h₂

namespace Matrix

/-- **Change of frame in the equation of a Hamiltonian path.** Let `g` be a path of symplectic
matrices with derivative `g'` at `t`, and let `Ψ` satisfy `Ψ' = J S Ψ` at `t`. Then for every
constant matrix `P` the path `g⁻¹ Ψ P` satisfies `(g⁻¹ Ψ P)' = J S′ (g⁻¹ Ψ P)` at `t`, with
`S′ = gᵀ S g + gᵀ J g'`. For `P = g(0)` this is the frame-changed path. -/
theorem hasDerivAt_inv_mul_mul_of_mem_symplecticGroup {g Ψ : 𝕜 → Matrix (n ⊕ n) (n ⊕ n) 𝕜}
    {g' S : Matrix (n ⊕ n) (n ⊕ n) 𝕜} {t : 𝕜} (hg : ∀ᶠ s in 𝓝 t, g s ∈ symplecticGroup n 𝕜)
    (hg' : HasDerivAt g g' t) (hΨ : HasDerivAt Ψ (J n 𝕜 * S * Ψ t) t)
    (P : Matrix (n ⊕ n) (n ⊕ n) 𝕜) :
    HasDerivAt (fun s ↦ (g s)⁻¹ * Ψ s * P)
      (J n 𝕜 * ((g t)ᵀ * S * g t + (g t)ᵀ * J n 𝕜 * g') * ((g t)⁻¹ * Ψ t * P)) t := by
  have hT := hg'.transpose_mul_J_mul_add_transpose_mul_J_mul_eq_zero hg
  have hgt : g t ∈ symplecticGroup n 𝕜 := hg.self_of_nhds
  have hinv : g t * (g t)⁻¹ = 1 := mul_nonsing_inv _ (SymplecticGroup.symplectic_det hgt)
  -- Near `t` the inverse of `g` is `-J gᵀ J`, which is differentiated by the product rule.
  have h₁ : HasDerivAt (fun s ↦ -J n 𝕜 * (g s)ᵀ * J n 𝕜 * Ψ s * P)
      ((-J n 𝕜 * g'ᵀ * J n 𝕜 * Ψ t + -J n 𝕜 * (g t)ᵀ * J n 𝕜 * (J n 𝕜 * S * Ψ t)) * P) t :=
    (((hg'.matrix_transpose.const_mul (-J n 𝕜)).mul_const (J n 𝕜)).mul hΨ).mul_const P
  refine (h₁.congr_deriv ?_).congr_of_eventuallyEq
    (hg.mono fun s hs ↦ by dsimp only; rw [SymplecticGroup.inv_eq_symplectic_inv _ hs])
  rw [SymplecticGroup.inv_eq_symplectic_inv _ hgt] at hinv ⊢
  set G := g t
  set K := -J n 𝕜 * Gᵀ * J n 𝕜
  have hT' : Gᵀ * J n 𝕜 * g' = -(g'ᵀ * J n 𝕜 * G) := eq_neg_of_add_eq_zero_right hT
  have e₁ : J n 𝕜 * (Gᵀ * S * G + Gᵀ * J n 𝕜 * g') * (K * Ψ t * P) =
      J n 𝕜 * Gᵀ * S * (G * K) * Ψ t * P + J n 𝕜 * (Gᵀ * J n 𝕜 * g') * K * Ψ t * P := by
    noncomm_ring
  have e₂ : (-J n 𝕜 * g'ᵀ * J n 𝕜 * Ψ t + K * (J n 𝕜 * S * Ψ t)) * P =
      -(J n 𝕜 * g'ᵀ * J n 𝕜 * Ψ t * P) - J n 𝕜 * Gᵀ * (J n 𝕜 * J n 𝕜) * S * Ψ t * P := by
    simp only [K]
    noncomm_ring
  have e₃ : J n 𝕜 * -(g'ᵀ * J n 𝕜 * G) * K * Ψ t * P =
      -(J n 𝕜 * g'ᵀ * J n 𝕜 * (G * K) * Ψ t * P) := by
    noncomm_ring
  rw [e₁, e₂, hinv, hT', e₃, hinv, J_squared]
  noncomm_ring

end Matrix
