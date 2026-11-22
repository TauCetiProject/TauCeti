/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.MDeriv.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.MDeriv.Degree
import TauCeti.Analysis.Complex.PartialDeriv.Roots

/-!
# Root-multiplicity vanishing and Hermite uniqueness for mixed partial derivatives

Every mixed partial derivative `TauCeti.mDeriv κ` annihilates `y ↦ g y * P.eval (y i)` at `z`
whenever `κ i < P.rootMultiplicity (z i)`
(`TauCeti.mDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity`).
Conversely, an entire function `f₀ : (Fin n → ℂ) → ℂ` with coordinate polynomial degree strictly
less than `deg (P j)` in every coordinate `z_j` whose mixed partial derivatives vanish on the
Cartesian root set `∏ᵢ Pᵢ⁻¹(0)` up to the root multiplicities is identically zero
(`TauCeti.eq_zero_of_degree_lt_of_mDeriv_eq_zero`).

## Main results

* `TauCeti.mDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity`: `mDeriv κ` annihilates
  `y ↦ g y * P.eval (y i)` at `z` whenever `κ i < P.rootMultiplicity (z i)`.
* `TauCeti.eq_zero_of_degree_lt_of_mDeriv_eq_zero`: Hermite-type uniqueness on `∏ᵢ Pᵢ⁻¹(0)` for
  entire functions with coordinate polynomial degree bounds.
-/

public section

open Finset Function Polynomial

namespace TauCeti

variable {n : ℕ}

/-- If `g : (Fin n → ℂ) → ℂ` is entire and `κ i < P.rootMultiplicity (z i)`, then `mDeriv κ`
annihilates `y ↦ g y * P.eval (y i)` at `z`. -/
theorem mDeriv_mul_eval_eq_zero_of_lt_rootMultiplicity {g : (Fin n → ℂ) → ℂ}
    (hg : Differentiable ℂ g) {i : Fin n} {P : ℂ[X]} {z : Fin n → ℂ} {κ : Fin n → ℕ}
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

end TauCeti
