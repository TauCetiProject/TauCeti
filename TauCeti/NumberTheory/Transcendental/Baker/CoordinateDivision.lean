/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.NumberTheory.Transcendental.Baker.MDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.CoordinateDivision
import TauCeti.Analysis.Complex.DividedDifference

/-!
# Mixed-derivative remainder vanishing for multivariate coordinate division

This file connects mixed partial derivatives `TauCeti.Baker.mDeriv` to multivariate coordinate
polynomial division (`TauCeti.Analysis.Complex.CoordinateDivision`). Every mixed partial
derivative preserves strict coordinate polynomial degree bounds, and if a multivariate division
remainder `f₀` satisfies `f(z) = f₀(z) + ∑ i, g_i(z) (P i).eval (z i)` with
`deg_{z_j} f₀ < deg (P j)` while `D^κ f(ζ) = 0` at every root tuple `ζ ∈ ∏ᵢ Pᵢ⁻¹(0)` for all
multi-orders `κ` with `κᵢ < (P i).rootMultiplicity (ζ i)`, then `f₀ = 0`
(Waldschmidt 2000, §4.3, Lemma 4.8).

## Main results

* `TauCeti.Baker.exists_degree_lt_and_mDeriv_eq_eval`: `mDeriv σ f` preserves any strict
  coordinate polynomial degree bound `< d`.
* `TauCeti.Baker.eq_zero_of_degree_lt_of_mDeriv_eq_zero`: an entire function with
  `deg_{z_j} f₀ < deg (P j)` in every coordinate whose mixed partial derivatives vanish on
  `∏ᵢ Pᵢ⁻¹(0)` up to the root multiplicities is identically zero.
* `TauCeti.Baker.eq_zero_of_eq_add_sum_mul_eval_of_mDeriv_eq_zero`: vanishing of the multivariate
  division remainder when `D^κ f` vanishes on `∏ᵢ Pᵢ⁻¹(0)` up to the root multiplicities.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, Lemma 4.8, pp. 123–128.
-/

public section

open Finset Function Polynomial

namespace TauCeti.Baker

variable {n : ℕ}

/-- Every mixed partial derivative `mDeriv σ f` of an entire function `f` preserves a strict
polynomial degree bound `< d` in any coordinate `j`. -/
theorem exists_degree_lt_and_mDeriv_eq_eval {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (j : Fin n) (σ : Fin n → ℕ) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) :
    ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, mDeriv σ f (update z j w) = Q.eval w := by
  suffices ∀ (s : Finset (Fin n)) (τ : Fin n → ℕ), (∀ i ∉ s, τ i = 0) →
      ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, mDeriv τ f (update z j w) = Q.eval w by
    exact this univ σ (fun i hi ↦ (hi (mem_univ i)).elim)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro τ hτ
    have hτ0 : τ = 0 := by ext i; exact hτ i (notMem_empty i)
    rw [hτ0, mDeriv_zero]
    exact hdeg
  | insert i s _ ih =>
    intro τ hτ
    have hupd : ∀ m ∉ s, update τ i 0 m = 0 := by
      intro m hms
      by_cases hmi : m = i
      · subst hmi; simp
      · simp [hmi, hτ m (fun hm ↦ hms ((mem_insert.mp hm).resolve_left hmi))]
    rw [mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero hf τ i]
    exact exists_degree_lt_and_iterate_partialDeriv_eq_eval
      (differentiable_mDeriv hf (update τ i 0)) i j (ih (update τ i 0) hupd) (τ i)

/-- If `g : (Fin n → ℂ) → ℂ` is entire and `κ i < P.rootMultiplicity (z i)`, then `mDeriv κ`
annihilates `y ↦ g y * P.eval (y i)` at `z`. -/
private theorem mDeriv_mul_eval_eq_zero {g : (Fin n → ℂ) → ℂ} (hg : Differentiable ℂ g)
    {i : Fin n} {P : ℂ[X]} {z : Fin n → ℂ} {κ : Fin n → ℕ}
    (hκ : κ i < P.rootMultiplicity (z i)) :
    mDeriv κ (fun y ↦ g y * P.eval (y i)) z = 0 := by
  have hPi : Differentiable ℂ (fun y : Fin n → ℂ ↦ P.eval (y i)) :=
    P.differentiable.comp (differentiable_apply i)
  have hcomm : (fun y : Fin n → ℂ ↦ g y * P.eval (y i)) = fun y ↦ P.eval (y i) * g y :=
    funext fun _ ↦ mul_comm _ _
  rw [hcomm, mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero (hPi.fun_mul hg) κ i,
    mDeriv_mul_of_update_eq hPi hg (fun j hj y s ↦ by
      have hji : i ≠ j := fun h ↦ hj (by subst h; simp)
      simp [update_of_ne hji])]
  have hcomm' : (fun y : Fin n → ℂ ↦ P.eval (y i) * mDeriv (update κ i 0) g y) =
      fun y ↦ mDeriv (update κ i 0) g y * P.eval (y i) :=
    funext fun _ ↦ mul_comm _ _
  rw [hcomm']
  exact iterate_partialDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity (differentiable_mDeriv hg _)
    hκ

/-- If an entire function `f₀ : (Fin n → ℂ) → ℂ` has polynomial degree strictly less than
`deg (P j)` in every coordinate `z_j` and satisfies `mDeriv κ f₀ ζ = 0` at every root tuple
`ζ ∈ ∏ᵢ Pᵢ⁻¹(0)` for every multi-order `κ` with `∀ i, κ i < (P i).rootMultiplicity (ζ i)`, then
`f₀ = 0`. -/
theorem eq_zero_of_degree_lt_of_mDeriv_eq_zero {f₀ : (Fin n → ℂ) → ℂ} {P : Fin n → ℂ[X]}
    (hf₀ : Differentiable ℂ f₀)
    (hdeg₀ : ∀ j z, ∃ Q : ℂ[X], Q.degree < (P j).degree ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hzero : ∀ ζ : Fin n → ℂ, (∀ i, (P i).IsRoot (ζ i)) →
      ∀ κ : Fin n → ℕ, (∀ i, κ i < (P i).rootMultiplicity (ζ i)) → mDeriv κ f₀ ζ = 0) :
    f₀ = 0 := by
  have claim (m : ℕ) (hm : m ≤ n) :
      ∀ (z : Fin n → ℂ), (∀ i : Fin n, m ≤ i.val → (P i).IsRoot (z i)) →
      ∀ (κ : Fin n → ℕ), (∀ i : Fin n, i.val < m → κ i = 0) →
        (∀ i : Fin n, m ≤ i.val → κ i < (P i).rootMultiplicity (z i)) →
        mDeriv κ f₀ z = 0 := by
    induction m with
    | zero =>
      intro z hz κ _ hκ
      exact hzero z (fun i ↦ hz i (Nat.zero_le _)) κ (fun i ↦ hκ i (Nat.zero_le _))
    | succ m ih =>
      intro z hz κ hκ0 hκ
      let j : Fin n := ⟨m, hm⟩
      have hκj : κ j = 0 := hκ0 j (Nat.lt_succ_self m)
      refine eq_zero_of_degree_lt_of_iterate_partialDeriv_eq_zero (differentiable_mDeriv hf₀ κ)
        (exists_degree_lt_and_mDeriv_eq_eval hf₀ j κ (hdeg₀ j) z) fun ζ hζ r hr ↦ ?_
      rw [← mDeriv_single, mDeriv_mDeriv hf₀, add_comm]
      refine ih (Nat.le_of_succ_le hm) (update z j ζ) ?_ (κ + Pi.single j r) ?_ ?_
      · intro i hi
        by_cases hij : i = j
        · subst hij; simpa using hζ
        · rw [update_of_ne hij]
          exact hz i (by have : i.val ≠ m := fun h ↦ hij (Fin.ext h); omega)
      · intro i hi
        have hij : i ≠ j := Fin.ne_of_val_ne hi.ne
        simp [hij, hκ0 i (Nat.lt_succ_of_lt hi)]
      · intro i hi
        by_cases hij : i = j
        · subst hij; simpa [hκj] using hr
        · rw [update_of_ne hij, Pi.add_apply, Pi.single_eq_of_ne hij, add_zero]
          exact hκ i (by have : i.val ≠ m := fun h ↦ hij (Fin.ext h); omega)
  ext z
  simpa using claim n le_rfl z (fun i hi ↦ (i.isLt.not_ge hi).elim) 0 (fun _ _ ↦ rfl)
    (fun i hi ↦ (i.isLt.not_ge hi).elim)

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
    sum_eq_zero fun i _ ↦ mDeriv_mul_eval_eq_zero (hg i) (hκ i)
  rwa [hsum0, add_zero] at h0

end TauCeti.Baker
