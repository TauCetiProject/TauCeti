/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.PartialDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Calculus.Deriv.Polynomial

/-!
# Root-multiplicity vanishing and Hermite uniqueness for partial derivatives

If an entire function `g : (ι → ℂ) → ℂ` is multiplied by `P.eval (y k)`, then every iterated
partial derivative `∂_k^m` of order `m < P.rootMultiplicity (z k)` vanishes at `z`
(`TauCeti.iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity`). Conversely, an entire
function `f₀` that agrees along the `k`-th coordinate line through `z` with a polynomial of degree
`< deg P` and satisfies `∂_k^m f₀ (update z k ζ) = 0` for every root `ζ` of `P` and every
`m < P.rootMultiplicity ζ` vanishes at `z`
(`TauCeti.eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero`).

## Main results

* `TauCeti.iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity`: derivatives of order
  below `P.rootMultiplicity (z k)` annihilate `y ↦ g y * P.eval (y k)`.
* `TauCeti.eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero`: Hermite-type uniqueness on a
  coordinate line for entire functions with a coordinate polynomial degree bound.
-/

public section

open Finset Function Polynomial

namespace TauCeti

variable {ι : Type*} [DecidableEq ι]

/-- If `g : (ι → ℂ) → ℂ` is entire and `m < P.rootMultiplicity (z k)`, then the `m`-th partial
derivative along coordinate `k` annihilates `y ↦ g y * P.eval (y k)` at `z`. -/
theorem iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity [Finite ι]
    {g : (ι → ℂ) → ℂ} (hg : Differentiable ℂ g) {k : ι} {P : ℂ[X]} {z : ι → ℂ} {m : ℕ}
    (hm : m < P.rootMultiplicity (z k)) :
    (partialDeriv k)^[m] (fun y ↦ g y * P.eval (y k)) z = 0 := by
  have := Fintype.ofFinite ι
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hm
  have hgP : Differentiable ℂ (fun y ↦ g y * P.eval (y k)) :=
    hg.mul (P.differentiable.comp (differentiable_apply k))
  rw [iterate_partialDeriv_eq_iteratedDeriv_update hgP k m z]
  have hline : (fun w ↦ g (update z k w) * P.eval (update z k w k)) =
      (fun w ↦ g (update z k w)) * fun w ↦ P.eval w := by
    ext w
    simp
  have hg_line : Differentiable ℂ (fun w ↦ g (update z k w)) := fun w ↦
    (hg (update z k w)).comp w (hasFDerivAt_update z w).differentiableAt
  rw [hline, iteratedDeriv_mul hg_line.contDiff.contDiffAt P.differentiable.contDiff.contDiffAt]
  refine sum_eq_zero fun i _ ↦ ?_
  have hPi : (hasseDeriv (m - i) P).eval (z k) = 0 :=
    (le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hP0).mp le_rfl (m - i) (by omega)
  rw [Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv, hPi, mul_zero, mul_zero]

/-- If `f₀ : (ι → ℂ) → ℂ` is entire, agrees with a polynomial of degree `< deg P` along the line
through `z` in coordinate `k`, and satisfies `∂_k^m f₀ (update z k ζ) = 0` for every root `ζ` of
`P` and every `m < P.rootMultiplicity ζ`, then `f₀ z = 0`. -/
theorem eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero [Finite ι]
    {f₀ : (ι → ℂ) → ℂ} (hf₀ : Differentiable ℂ f₀) {k : ι} {P : ℂ[X]} {z : ι → ℂ}
    (hdeg : ∃ Q : ℂ[X], Q.degree < P.degree ∧ ∀ w, f₀ (update z k w) = Q.eval w)
    (hzero : ∀ ζ, P.IsRoot ζ → ∀ m < P.rootMultiplicity ζ,
      (partialDeriv k)^[m] f₀ (update z k ζ) = 0) :
    f₀ z = 0 := by
  have := Fintype.ofFinite ι
  obtain ⟨Q, hQdeg, hQ⟩ := hdeg
  have hP0 : P ≠ 0 := ne_zero_of_degree_gt hQdeg
  suffices hQ0 : Q = 0 by simpa [hQ0] using hQ (z k)
  by_contra hQ0
  have hmult (ζ : ℂ) : P.rootMultiplicity ζ ≤ Q.rootMultiplicity ζ := by
    rcases Nat.eq_zero_or_pos (P.rootMultiplicity ζ) with hm0 | hmpos
    · simp [hm0]
    · have hζroot : P.IsRoot ζ := (rootMultiplicity_pos hP0).mp hmpos
      rw [le_rootMultiplicity_iff_forall_eval_hasseDeriv_eq_zero hQ0]
      intro m hm
      have hfz : (partialDeriv k)^[m] f₀ (update z k ζ) = 0 := hzero ζ hζroot m hm
      rw [iterate_partialDeriv_eq_iteratedDeriv_update hf₀ k m (update z k ζ), update_self] at hfz
      have hline : (fun w ↦ f₀ (update (update z k ζ) k w)) = fun w ↦ Q.eval w :=
        funext fun w ↦ by simp [hQ]
      rw [hline, Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hfz
      exact (mul_eq_zero.mp hfz).resolve_left (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
  have hdvd : P ∣ Q := (IsAlgClosed.dvd_iff_roots_le_roots hP0 hQ0).mpr
    (Multiset.le_iff_count.mpr fun ζ ↦ by simpa [count_roots] using hmult ζ)
  exact hQ0 (eq_zero_of_dvd_of_degree_lt hdvd hQdeg)

end TauCeti
