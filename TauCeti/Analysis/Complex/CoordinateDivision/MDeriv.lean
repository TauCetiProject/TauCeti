/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.MDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.MDeriv.Roots

/-!
# Mixed-derivative remainder vanishing for multivariate coordinate division

This file connects mixed partial derivatives `TauCeti.mDeriv` to multivariate coordinate
polynomial division (`TauCeti.Analysis.Complex.CoordinateDivision.Basic`): if a multivariate
division remainder `f₀` satisfies `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` with
`deg_{z_j} f₀ < deg (P j)` while `D^κ f(ζ) = 0` at every root tuple `ζ ∈ ∏ᵢ Pᵢ⁻¹(0)` for all
multi-orders `κ` with `κᵢ < (P i).rootMultiplicity (ζ i)`, then `f₀ = 0`
(Waldschmidt 2000, §4.3, Lemma 4.8).

## Main results

* `TauCeti.eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero`: vanishing of the multivariate division
  remainder when `D^κ f` vanishes on `∏ᵢ Pᵢ⁻¹(0)` up to the root multiplicities.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Finset Function Polynomial

namespace TauCeti

variable {n : ℕ}

/-- **Vanishing of the multivariate remainder (Waldschmidt, Lemma 4.8).**
Let `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` where `f₀` and each `g_i` are entire and `f₀` is
a polynomial of degree `< deg (P j)` in every coordinate `z_j`. If `D^κ f(ζ) = 0` at every root
tuple `ζ ∈ ∏ᵢ Pᵢ⁻¹(0)` and for every multi-order `κ` satisfying
`∀ i, κ i < (P i).rootMultiplicity (ζ i)`, then `f₀ = 0`. -/
theorem eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero
    {f f₀ : (Fin n → ℂ) → ℂ} {g : Fin n → (Fin n → ℂ) → ℂ} {P : Fin n → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀) (hg : ∀ i, Differentiable ℂ (g i))
    (hdiv : ∀ z, f z = f₀ z + ∑ i, g i z * (P i).eval (z i))
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hzero : ∀ ζ : Fin n → ℂ, (∀ i, (P i).IsRoot (ζ i)) →
      ∀ κ : Fin n → ℕ, (∀ i, κ i < (P i).rootMultiplicity (ζ i)) → mDeriv κ f ζ = 0) :
    f₀ = 0 := by
  have hterm (i : Fin n) : Differentiable ℂ (fun y : Fin n → ℂ ↦ g i y * (P i).eval (y i)) :=
    (hg i).mul ((P i).differentiable.comp (differentiable_apply i))
  have hf_eq : f = f₀ + ∑ i : Fin n, fun y ↦ g i y * (P i).eval (y i) := by
    ext y
    simp [hdiv y, Finset.sum_apply]
  refine eq_zero_of_degree_lt_of_mDeriv_eq_zero hf₀ hdeg₀ fun ζ hζ κ hκ ↦ ?_
  have h0 : mDeriv κ f ζ = 0 := hzero ζ hζ κ hκ
  rw [hf_eq, mDeriv_add hf₀ (Differentiable.sum fun i _ ↦ hterm i),
    mDeriv_sum univ (fun i _ ↦ hterm i), Pi.add_apply, Finset.sum_apply] at h0
  have hsum0 : ∑ i : Fin n, mDeriv κ (fun y ↦ g i y * (P i).eval (y i)) ζ = 0 :=
    sum_eq_zero fun i _ ↦ mDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity (hg i) (hκ i)
  rwa [hsum0, add_zero] at h0

end TauCeti
