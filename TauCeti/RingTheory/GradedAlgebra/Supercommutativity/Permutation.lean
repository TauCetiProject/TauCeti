/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import TauCeti.GroupTheory.Perm.KoszulSign
import TauCeti.Algebra.BigOperators.Fin

/-!
# Permuting the factors of a product of homogeneous elements

Let `A` be a ring with homogeneous pieces `ℬ : ι → S` over a Koszul-signed degree semiring `ι`,
in which homogeneous elements supercommute: `a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a)` for
`a ∈ ℬ p` and `b ∈ ℬ q`. This file computes the effect of reordering a product of homogeneous
elements: listing the factors `a 0, …, a (n - 1)` in the order of a permutation `σ` multiplies the
product by the Koszul sign `σ.koszulSign d` (`Equiv.Perm.koszulSign`) of their degrees `d`. Only
the commutation rule is used: no decomposition of `A` into its pieces is required.

## Main results

* `TauCeti.mul_list_prod_ofFn_succAbove_of_mul_eq_uzpow_smul_mul`: inserting the factor `a k` at
  its position `k` from the front of a word costs the sign `∏ i ∈ Iio k, (-1) ^ (d k * d i)`.
* `TauCeti.list_prod_ofFn_comp_perm_of_mul_eq_uzpow_smul_mul`: the product of the factors listed
  in the order of `σ` is `σ.koszulSign d` times their product in the natural order.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the Koszul
  commutation rule in free supercommutative algebras.
-/

public section

open Finset

namespace TauCeti

variable {A ι S : Type*} [Ring A] [CommSemiring ι] [Module ι (Additive ℤˣ)] [SetLike S A]
  {ℬ : ι → S}

/-- Under Koszul graded commutativity, inserting the factor `a k` of a word of homogeneous elements
at its position `k` from the front costs the signs `(-1) ^ (d k * d i)` of moving it past the
factors `a i` with `i < k`. -/
theorem mul_list_prod_ofFn_succAbove_of_mul_eq_uzpow_smul_mul
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {n : ℕ} {d : Fin (n + 1) → ι} {a : Fin (n + 1) → A} (ha : ∀ i, a i ∈ ℬ (d i))
    (k : Fin (n + 1)) :
    a k * (List.ofFn (a ∘ k.succAbove)).prod =
      (∏ i ∈ Iio k, (-1 : ℤˣ) ^ (d k * d i)) • (List.ofFn a).prod := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := Fin.fin_one_eq_zero k
    simp [← filter_gt_eq_Iio]
  | succ n ih =>
    induction k using Fin.cases with
    | zero => simp [List.ofFn_succ, ← filter_gt_eq_Iio]
    | succ k =>
      have h := ih (d := d ∘ Fin.succ) (a := a ∘ Fin.succ) (fun i => ha i.succ) k
      simp only [Function.comp_apply] at h
      have e : List.ofFn (a ∘ k.succ.succAbove) =
          a 0 :: List.ofFn ((a ∘ Fin.succ) ∘ k.succAbove) := by
        simp [List.ofFn_succ, Function.comp_def, Fin.succ_succAbove_succ]
      -- Move `a k.succ` past `a 0`, then apply the induction hypothesis to the remaining word.
      calc a k.succ * (List.ofFn (a ∘ k.succ.succAbove)).prod
          = a k.succ * a 0 * (List.ofFn ((a ∘ Fin.succ) ∘ k.succAbove)).prod := by
            rw [e, List.prod_cons, mul_assoc]
        _ = ((-1 : ℤˣ) ^ (d k.succ * d 0)) •
              (a 0 * (a k.succ * (List.ofFn ((a ∘ Fin.succ) ∘ k.succAbove)).prod)) := by
            rw [hcomm (ha k.succ) (ha 0), smul_mul_assoc, mul_assoc]
        _ = ((-1 : ℤˣ) ^ (d k.succ * d 0)) • (a 0 *
              (∏ i ∈ Iio k, (-1 : ℤˣ) ^ (d k.succ * d i.succ)) •
                (List.ofFn (a ∘ Fin.succ)).prod) := by
            rw [h]
        _ = (((-1 : ℤˣ) ^ (d k.succ * d 0)) * ∏ i ∈ Iio k, (-1 : ℤˣ) ^ (d k.succ * d i.succ)) •
              (a 0 * (List.ofFn (a ∘ Fin.succ)).prod) := by
            rw [mul_smul_comm, smul_smul]
        _ = (∏ i ∈ Iio k.succ, (-1 : ℤˣ) ^ (d k.succ * d i)) • (List.ofFn a).prod := by
            rw [Fin.prod_Iio_succ, List.ofFn_succ (f := a), List.prod_cons, Function.comp_def]

/-- **Permuting the factors of a product.** Under Koszul graded commutativity, listing homogeneous
factors `a i` of degrees `d i` in the order of a permutation `σ` multiplies their product by the
Koszul sign `σ.koszulSign d`. -/
theorem list_prod_ofFn_comp_perm_of_mul_eq_uzpow_smul_mul
    (hcomm : ∀ {p q : ι} {a b : A},
      a ∈ ℬ p → b ∈ ℬ q → a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a))
    {n : ℕ} {d : Fin n → ι} {a : Fin n → A} (ha : ∀ i, a i ∈ ℬ (d i)) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn (a ∘ σ)).prod = σ.koszulSign d • (List.ofFn a).prod := by
  induction n with
  | zero => simp [Subsingleton.elim σ 1]
  | succ n ih =>
    obtain ⟨⟨j, π⟩, rfl⟩ := (Equiv.Perm.consFinEquiv n).surjective σ
    have e : List.ofFn (a ∘ Equiv.Perm.consFin j π) =
        a j :: List.ofFn ((a ∘ j.succAbove) ∘ π) := by
      simp [List.ofFn_succ, Function.comp_def]
    -- List `a j` first, reorder the remaining word by induction, then insert `a j` at `j`.
    calc (List.ofFn (a ∘ Equiv.Perm.consFinEquiv n (j, π))).prod
        = a j * (List.ofFn ((a ∘ j.succAbove) ∘ π)).prod := by
          rw [Equiv.Perm.consFinEquiv_apply, e, List.prod_cons]
      _ = π.koszulSign (d ∘ j.succAbove) • (a j * (List.ofFn (a ∘ j.succAbove)).prod) := by
          rw [ih (d := d ∘ j.succAbove) (a := a ∘ j.succAbove) (fun i => ha _), mul_smul_comm]
      _ = (π.koszulSign (d ∘ j.succAbove) * ∏ i ∈ Iio j, (-1 : ℤˣ) ^ (d j * d i)) •
            (List.ofFn a).prod := by
          rw [mul_list_prod_ofFn_succAbove_of_mul_eq_uzpow_smul_mul hcomm ha, smul_smul]
      _ = (Equiv.Perm.consFinEquiv n (j, π)).koszulSign d • (List.ofFn a).prod := by
          rw [Equiv.Perm.consFinEquiv_apply, Equiv.Perm.koszulSign_consFin,
            mul_comm (π.koszulSign _)]

end TauCeti
