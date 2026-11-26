/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.GroupTheory.Perm.Fin
public import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# The Koszul sign of a permutation of graded letters

Let `d : Fin n → ι` assign a degree to each of `n` letters, where the degrees live in a
Koszul-signed degree semiring `ι` (`[CommSemiring ι] [Module ι (Additive ℤˣ)]`, for instance `ℤ`,
`ℕ` or `ZMod 2`). Listing the letters in the order `σ 0, σ 1, …` of a permutation `σ`, every pair
of positions `i < j` whose letters appear in the opposite order, `σ j < σ i`, has to be exchanged
once to restore the natural order. Under the Koszul rule `x y = (-1) ^ (|x| |y|) y x` each such
exchange costs the sign `(-1) ^ (d (σ i) * d (σ j))`. The **Koszul sign** `σ.koszulSign d` is the
product of these signs over the inversions of `σ`. It is the sign by which a product of
homogeneous elements of a supercommutative algebra changes when its factors are permuted; see
`TauCeti.list_prod_ofFn_comp_perm_of_mul_eq_uzpow_smul_mul`.

## Main definitions

* `Equiv.Perm.koszulSign σ d`: the product of the signs `(-1) ^ (d (σ i) * d (σ j))` over the
  inversions `(i, j)` of `σ`.

## Main results

* `Equiv.Perm.koszulSign_eq_prod_prod_Ioi`: the Koszul sign as a product over the increasing pairs
  of positions, in the form of `Equiv.Perm.sign_eq_prod_prod_Ioi`.
* `Equiv.Perm.koszulSign_consFin`: listing the letter `j` in front of the other letters, which are
  listed in the order of `π`, multiplies the Koszul sign of `π` by the signs of moving `j` past
  the letters `i < j`.
* `Equiv.Perm.koszulSign_swap_castSucc_succ`: exchanging two adjacent letters costs the sign of
  exchanging them once.
* `Equiv.Perm.koszulSign_mul`: the cocycle law
  `(σ * τ).koszulSign d = σ.koszulSign d * τ.koszulSign (d ∘ σ)`, which makes the signed
  permutation action on words of graded letters an action; `Equiv.Perm.koszulSign_inv` follows.
* `Equiv.Perm.koszulSign_eq_sign`: when every letter is odd, the Koszul sign is the sign of the
  permutation.
* `Equiv.Perm.koszulSign_eq_one`: when every letter is even, the Koszul sign is trivial.
* `Equiv.Perm.koszulSign_intCast`: the Koszul sign of integer degrees is the Koszul sign of their
  images in any Koszul-signed degree ring, such as their parities in `ZMod 2`.
* `Equiv.Perm.koszulSign_eq_sign_blockPerm`: for degrees in `ℕ`, the Koszul sign is the sign of
  the permutation `Equiv.Perm.blockPerm σ d` reordering consecutive blocks of sizes `d i`, so a
  letter of degree `k` behaves like a block of `k` odd letters.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the Koszul
  commutation rule in free supercommutative algebras.
-/

public section

open Finset

namespace Equiv.Perm

variable {ι : Type*} [CommSemiring ι] [Module ι (Additive ℤˣ)] {n : ℕ}

/-- The Koszul sign of listing letters of degrees `d` in the order of `σ`: the product, over the
inversions `(i, j)` of `σ` (positions `i < j` with `σ j < σ i`), of the signs
`(-1) ^ (d (σ i) * d (σ j))` of exchanging the two letters. -/
def koszulSign (σ : Perm (Fin n)) (d : Fin n → ι) : ℤˣ :=
  ∏ p ∈ univ.inversions σ, (-1) ^ (d (σ p.1) * d (σ p.2))

theorem koszulSign_def (σ : Perm (Fin n)) (d : Fin n → ι) :
    σ.koszulSign d = ∏ p ∈ univ.inversions σ, (-1) ^ (d (σ p.1) * d (σ p.2)) := (rfl)

@[simp]
theorem koszulSign_one (d : Fin n → ι) : koszulSign 1 d = 1 := by
  simp [koszulSign_def]

/-- **Insertion of a first letter.** Listing the letter `j` first and the remaining letters in the
order of `π` costs the Koszul sign of `π` on the remaining letters, times the signs of moving the
letter `j` past each letter `i < j`. -/
@[simp]
theorem koszulSign_consFin (j : Fin (n + 1)) (π : Perm (Fin n)) (d : Fin (n + 1) → ι) :
    (consFin j π).koszulSign d =
      (∏ i ∈ Iio j, (-1) ^ (d j * d i)) * π.koszulSign (d ∘ j.succAbove) :=
  prod_univ_inversions_consFin j π fun a b ↦ (-1) ^ (d a * d b)

/-- The Koszul sign as a product over the increasing pairs of positions, in the form of
`Equiv.Perm.sign_eq_prod_prod_Ioi`. -/
theorem koszulSign_eq_prod_prod_Ioi (σ : Perm (Fin n)) (d : Fin n → ι) :
    σ.koszulSign d =
      ∏ i, ∏ j ∈ Ioi i, if σ i < σ j then 1 else (-1) ^ (d (σ i) * d (σ j)) := by
  rw [koszulSign_def, prod_univ_inversions (w := fun a b => (-1) ^ (d (σ a) * d (σ b)))]
  refine prod_congr rfl fun i _ => ?_
  rw [← filter_lt_eq_Ioi, prod_filter]
  refine prod_congr rfl fun j _ => ?_
  have := σ.injective.ne (a₁ := i) (a₂ := j)
  grind

/-- Exchanging two adjacent letters costs the sign `(-1) ^ (d i.castSucc * d i.succ)`: the only
inversion of the adjacent transposition is the exchanged pair. -/
@[simp]
theorem koszulSign_swap_castSucc_succ (i : Fin n) (d : Fin (n + 1) → ι) :
    (swap i.castSucc i.succ).koszulSign d = (-1) ^ (d i.castSucc * d i.succ) := by
  rw [koszulSign_def, inversions_univ_swap_castSucc_succ, prod_singleton, swap_apply_left,
    swap_apply_right, mul_comm]

/-- **The Koszul sign is a cocycle.** Listing letters in the order of `σ * τ` costs the Koszul
sign of `σ`, times the Koszul sign of `τ` acting on the letters already listed in the order of
`σ`. This is the consistency of the signed permutation action on words of graded letters. -/
theorem koszulSign_mul (σ τ : Perm (Fin n)) (d : Fin n → ι) :
    (σ * τ).koszulSign d = σ.koszulSign d * τ.koszulSign (d ∘ σ) := by
  -- Symmetrize the factors of the Koszul sign of `σ`, so that they can be reindexed along `τ`.
  set g : Fin n → Fin n → ℤˣ := fun a b =>
    if (a < b ↔ σ a < σ b) then 1 else (-1) ^ (d (σ a) * d (σ b)) with hg
  have hgsymm (a b : Fin n) : g a b = g b a := by
    have := σ.injective.ne (a₁ := a) (a₂ := b)
    simp only [hg, mul_comm (d (σ a))]
    grind
  have hσ : σ.koszulSign d = ∏ i, ∏ j ∈ Ioi i, g (τ i) (τ j) := by
    rw [TauCeti.prod_prod_Ioi_comp_perm g τ hgsymm, koszulSign_eq_prod_prod_Ioi]
    exact prod_congr rfl fun i _ => prod_congr rfl fun j hj => by simp [hg, (mem_Ioi.mp hj)]
  rw [hσ, koszulSign_eq_prod_prod_Ioi, koszulSign_eq_prod_prod_Ioi, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  simp only [hg, Perm.coe_mul, Function.comp_apply]
  by_cases h₁ : τ i < τ j <;> by_cases h₂ : σ (τ i) < σ (τ j) <;>
    simp [h₁, h₂]

/-- The Koszul sign of the inverse permutation, acting on the letters listed in the order of
`σ`, is the Koszul sign of `σ`. -/
@[simp]
theorem koszulSign_inv (σ : Perm (Fin n)) (d : Fin n → ι) :
    σ⁻¹.koszulSign (d ∘ σ) = σ.koszulSign d := by
  have h := koszulSign_mul σ σ⁻¹ d
  rw [mul_inv_cancel, koszulSign_one] at h
  rw [eq_inv_of_mul_eq_one_right h.symm, Int.units_inv_eq_self]

/-- When every letter is odd, the Koszul sign of `σ` is its sign. -/
theorem koszulSign_eq_sign (σ : Perm (Fin n)) {d : Fin n → ι}
    (hd : ∀ i, (-1 : ℤˣ) ^ d i = -1) : σ.koszulSign d = sign σ := by
  rw [koszulSign_def, TauCeti.sign_eq_neg_one_pow_card_inversion, ← prod_const]
  exact prod_congr rfl fun p _ => by rw [uzpow_mul, hd, hd]

/-- When every letter is even, the Koszul sign is trivial. -/
theorem koszulSign_eq_one (σ : Perm (Fin n)) {d : Fin n → ι}
    (hd : ∀ i, (-1 : ℤˣ) ^ d i = 1) : σ.koszulSign d = 1 := by
  rw [koszulSign_def]
  exact prod_eq_one fun p _ => by rw [uzpow_mul, hd, one_uzpow]

/-- For degrees in `ℕ`, the Koszul sign of `σ` is the sign of the permutation reordering
consecutive blocks of sizes `d i` in the order of `σ`: a letter of degree `k` exchanges like a
block of `k` odd letters. -/
theorem koszulSign_eq_sign_blockPerm (σ : Perm (Fin n)) (d : Fin n → ℕ) :
    σ.koszulSign d = sign (blockPerm σ d) := by
  rw [sign_blockPerm, koszulSign_def, ← prod_pow_eq_pow_sum]

/-- The Koszul sign of integer degrees `d` only depends on their images in a Koszul-signed degree
ring `R`; for `R = ZMod 2`, it is the Koszul sign of their parities. -/
theorem koszulSign_intCast {R : Type*} [CommRing R] [Module R (Additive ℤˣ)]
    (σ : Perm (Fin n)) (d : Fin n → ℤ) :
    σ.koszulSign (fun i ↦ (d i : R)) = σ.koszulSign d := by
  simp only [koszulSign_def, ← Int.cast_mul, uzpow_intCast]

end Equiv.Perm
