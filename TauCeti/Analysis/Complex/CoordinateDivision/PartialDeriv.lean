/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.PartialDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.PartialDeriv.Roots

/-!
# Partial-derivative remainder vanishing for univariate coordinate division

This file connects coordinate partial derivatives `TauCeti.partialDeriv` to univariate coordinate
polynomial division (`TauCeti.Analysis.Complex.CoordinateDivision.Basic`): if a univariate
division remainder `f₀` satisfies `f(y) = f₀(y) + fk(y) P(y k)` with `deg_{z_k} f₀ < deg P`
while `∂_k^m f(update z k ζ) = 0` for every root `ζ` of `P` and every `m < P.rootMultiplicity ζ`,
then `f₀ z = 0` (Waldschmidt 2000, §4.3, Lemma 4.8).

## Main results

* `TauCeti.eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero`: vanishing of the
  univariate division remainder when `∂_k^m f` vanishes along the root hyperplanes up to the root
  multiplicities.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Function Polynomial

namespace TauCeti

variable {ι : Type*} [DecidableEq ι]

/-- If `f(y) = f₀(y) + fk(y) P(y k)` with `f₀, fk` entire and `deg_{z_k} f₀ < deg P` along the
line through `z` in coordinate `k`, and if `∂_k^m f` vanishes at `update z k ζ` for every root `ζ`
of `P` and every `m < P.rootMultiplicity ζ`, then `f₀ z = 0`. -/
theorem eq_zero_of_eq_add_mul_eval_of_iterate_partialDeriv_eq_zero [Finite ι]
    {f f₀ fk : (ι → ℂ) → ℂ} (hf₀ : Differentiable ℂ f₀) (hfk : Differentiable ℂ fk) {k : ι}
    {P : ℂ[X]} (hdiv : ∀ y, f y = f₀ y + fk y * P.eval (y k)) {z : ι → ℂ}
    (hdeg : ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hzero : ∀ ζ, P.IsRoot ζ → ∀ m < P.rootMultiplicity ζ,
      (partialDeriv k)^[m] f (update z k ζ) = 0) :
    f₀ z = 0 := by
  have := Fintype.ofFinite ι
  have hf_eq : f = f₀ + fun y ↦ fk y * P.eval (y k) := funext hdiv
  have hterm : Differentiable ℂ (fun y ↦ fk y * P.eval (y k)) :=
    hfk.mul (P.differentiable.comp (differentiable_apply k))
  refine eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero hf₀ hdeg fun ζ hζ m hm ↦ ?_
  have hfz : (partialDeriv k)^[m] f (update z k ζ) = 0 := hzero ζ hζ m hm
  rw [hf_eq, iterate_partialDeriv_add hf₀ hterm k m, Pi.add_apply,
    iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity hfk (by simpa using hm),
    add_zero] at hfz
  exact hfz

end TauCeti
