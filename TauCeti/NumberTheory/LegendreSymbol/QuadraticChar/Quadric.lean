/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Points on nondegenerate quadrics over a finite field

Let `F` be a finite field of odd characteristic with `q` elements and quadratic character `χ`. For
a nondegenerate quadratic form `Q` in `n` variables over `F` with discriminant `Δ`, the number
`N(c)` of solutions of `Q(x) = c` depends only on `n`, on `χ` of the signed discriminant, and on
`c` only through `χ(c)` in odd rank and through whether `c` vanishes in even rank:

```text
n = 2m + 1:  N(c) = q^{2m} + χ((-1)^m Δ c) q^m,
n = 2m + 2:  N(c) = q^{2m+1} + χ((-1)^{m+1} Δ) q^m ν(c),  where ν(0) = q - 1, ν(c) = -1 for c ≠ 0.
```

For `n = 1` this is the count `1 + χ(c / a)` of the square roots of `c / a`, which is Mathlib's
`quadraticChar_card_sqrts`. In general the formulas are proved for diagonal forms
`∑ wᵢ xᵢ²` with all `wᵢ ≠ 0`, with `Δ = ∏ wᵢ`, by adding one variable at a time: adding the term
`a t²` turns the count `N` into `c ↦ qⁿ + ∑ᵤ χ(a u) N(c - u)`, and the two parities alternate,
the odd-to-even step evaluating the Jacobi sum `∑ᵤ χ(u (c - u))` with
`TauCeti.sum_quadraticChar_mul_sub`. Since every symmetric matrix is
congruent to a diagonal one when `2` is invertible, the same formulas count the solutions of
`xᵀ A x = c` for a symmetric matrix `A` with `det A ≠ 0`, with `Δ = det A`.

These are the point counts from which the orders of the finite orthogonal groups, and with them
the local densities of an integral lattice at the primes not dividing twice its determinant, are
computed.

## Main results

* `TauCeti.card_sum_mul_sq_eq_of_card_eq_two_mul_add_one`,
  `TauCeti.card_sum_mul_sq_eq_of_card_eq_two_mul_add_two`: the number of solutions of
  `∑ wᵢ xᵢ² = c` in odd and in even rank.
* `Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_one`,
  `Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two`: the number of solutions of
  `xᵀ A x = c` for a nondegenerate symmetric matrix `A`, in odd and in even rank.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, Encyclopedia of Mathematics and its Applications
  20, Cambridge University Press (1997), Theorems 6.26 and 6.27.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Graduate Texts in
  Mathematics 84, Springer (1990), Chapter 8, §6.
-/

public section

open Finset Matrix

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Diagonal

/-- The counts of all the values of a function on `ι → F` add up to `qⁿ`. -/
private theorem sum_card_sum_mul_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → F) :
    ∑ c : F, (#{x : ι → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ Fintype.card ι := by
  have h := card_eq_sum_card_fiberwise (f := fun x : ι → F ↦ ∑ i, w i * x i ^ 2)
    (s := univ) (t := univ) fun _ _ ↦ mem_univ _
  rw [card_univ, Fintype.card_fun] at h
  exact_mod_cast h.symm

/-- In zero variables the only value is `0`. -/
private theorem card_sum_mul_sq_fin_zero (w : Fin 0 → F) (c : F) :
    (#{x : Fin 0 → F | ∑ i, w i * x i ^ 2 = c} : ℤ) = if c = 0 then 1 else 0 := by
  split_ifs with hc
  · subst hc
    simp
  · simp [eq_comm, hc]

/-- Splitting off the first variable: the count in `n + 1` variables is the sum over the value
`t` of the first variable of the count in the remaining `n` variables. -/
private theorem card_sum_mul_sq_fin_succ {n : ℕ} (w : Fin (n + 1) → F) (c : F) :
    (#{x : Fin (n + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      ∑ t : F, (#{y : Fin n → F | ∑ i, Fin.tail w i * y i ^ 2 = c - w 0 * t ^ 2} : ℤ) := by
  simp only [natCast_card_filter]
  rw [← (Fin.consEquiv fun _ ↦ F).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun t _ ↦ sum_congr rfl fun y _ ↦ ?_
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail,
    eq_sub_iff_add_eq, add_comm (w 0 * t ^ 2)]

/-- Adding the variable `t` with coefficient `a = w 0 ≠ 0` changes the count `N` into
`c ↦ qⁿ + ∑ᵤ χ(a u) N(c - u)`. -/
private theorem card_sum_mul_sq_fin_succ_eq (hF : ringChar F ≠ 2) {n : ℕ} (w : Fin (n + 1) → F)
    (hw : w 0 ≠ 0) (c : F) :
    (#{x : Fin (n + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ n + ∑ u : F, quadraticChar F (w 0 * u) *
        #{y : Fin n → F | ∑ i, Fin.tail w i * y i ^ 2 = c - u} := by
  rw [card_sum_mul_sq_fin_succ, sum_comp_mul_sq hF hw
    (fun u ↦ (#{y : Fin n → F | ∑ i, Fin.tail w i * y i ^ 2 = c - u} : ℤ))]
  simp only [smul_eq_mul, add_mul, one_mul, sum_add_distrib]
  congr 1
  have hsub := Equiv.sum_comp (Equiv.subLeft c)
    (fun v ↦ (#{y : Fin n → F | ∑ i, Fin.tail w i * y i ^ 2 = v} : ℤ))
  simp only [Equiv.subLeft_apply] at hsub
  rw [hsub, sum_card_sum_mul_sq_eq, Fintype.card_fin]

/-- In one variable, `a x² = c` has `1 + χ(a c)` solutions. -/
private theorem card_sum_mul_sq_fin_one (hF : ringChar F ≠ 2) (w : Fin (2 * 0 + 1) → F)
    (hw : ∀ i, w i ≠ 0) (c : F) :
    (#{x : Fin (2 * 0 + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * 0) +
        quadraticChar F ((-1) ^ 0 * (∏ i, w i) * c) * (Fintype.card F : ℤ) ^ 0 := by
  have h0 (v : F) : (#{y : Fin (2 * 0) → F | ∑ i, Fin.tail w i * y i ^ 2 = v} : ℤ) =
      if v = 0 then 1 else 0 :=
    card_sum_mul_sq_fin_zero (Fin.tail w) v
  rw [card_sum_mul_sq_fin_succ_eq hF w (hw 0)]
  simp only [h0, sub_eq_zero, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
  simp

/-- The odd-rank count in `2m + 1` variables gives the even-rank count in `2m + 2` variables. The
new term is the Jacobi sum `∑ᵤ χ(u (c - u)) = χ(-1) ν(c)`. -/
private theorem card_sum_mul_sq_fin_even_of_odd (hF : ringChar F ≠ 2) {m : ℕ}
    (hodd : ∀ w : Fin (2 * m + 1) → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (#{x : Fin (2 * m + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
        (Fintype.card F : ℤ) ^ (2 * m) +
          quadraticChar F ((-1) ^ m * (∏ i, w i) * c) * (Fintype.card F : ℤ) ^ m)
    (w : Fin (2 * m + 1 + 1) → F) (hw : ∀ i, w i ≠ 0) (c : F) :
    (#{x : Fin (2 * m + 1 + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * m + 1) +
        quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) * (Fintype.card F : ℤ) ^ m *
          if c = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  rw [card_sum_mul_sq_fin_succ_eq hF w (hw 0)]
  simp only [hodd (Fin.tail w) (fun i ↦ hw _), mul_add, sum_add_distrib, ← sum_mul,
    sum_quadraticChar_mul hF (hw 0), zero_mul, zero_add]
  have hu (u : F) : quadraticChar F (w 0 * u) *
      (quadraticChar F ((-1) ^ m * (∏ i, Fin.tail w i) * (c - u)) * (Fintype.card F : ℤ) ^ m) =
      quadraticChar F ((-1) ^ m * w 0 * ∏ i, Fin.tail w i) * (Fintype.card F : ℤ) ^ m *
        quadraticChar F (u * (c - u)) := by
    simp only [map_mul]
    ring
  rw [sum_congr rfl fun u _ ↦ hu u, ← mul_sum, sum_quadraticChar_mul_sub hF, Fin.prod_univ_succ w]
  simp only [Fin.tail, map_mul, map_pow]
  ring

/-- The even-rank count in `2m + 2` variables gives the odd-rank count in `2m + 3` variables. Since
`ν(c - u) = q [u = c] - 1`, only the term `u = c` survives. -/
private theorem card_sum_mul_sq_fin_odd_of_even (hF : ringChar F ≠ 2) {m : ℕ}
    (heven : ∀ w : Fin (2 * m + 1 + 1) → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (#{x : Fin (2 * m + 1 + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
        (Fintype.card F : ℤ) ^ (2 * m + 1) +
          quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) * (Fintype.card F : ℤ) ^ m *
            if c = 0 then (Fintype.card F : ℤ) - 1 else -1)
    (w : Fin (2 * (m + 1) + 1) → F) (hw : ∀ i, w i ≠ 0) (c : F) :
    (#{x : Fin (2 * (m + 1) + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * (m + 1)) +
        quadraticChar F ((-1) ^ (m + 1) * (∏ i, w i) * c) * (Fintype.card F : ℤ) ^ (m + 1) := by
  -- Restate the hypothesis for an index type `Fin n` with `n` only propositionally `2m + 2`.
  have heven' : ∀ n, n = 2 * m + 1 + 1 → ∀ v : Fin n → F, (∀ i, v i ≠ 0) → ∀ c : F,
      (#{x : Fin n → F | ∑ i, v i * x i ^ 2 = c} : ℤ) =
        (Fintype.card F : ℤ) ^ (2 * m + 1) +
          quadraticChar F ((-1) ^ (m + 1) * ∏ i, v i) * (Fintype.card F : ℤ) ^ m *
            if c = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
    intro n hn
    subst hn
    exact heven
  rw [card_sum_mul_sq_fin_succ_eq hF w (hw 0)]
  simp only [heven' _ (by ring) (Fin.tail w) (fun i ↦ hw _), mul_add, sum_add_distrib,
    ← sum_mul, sum_quadraticChar_mul hF (hw 0), zero_mul, zero_add]
  have hu (u : F) : quadraticChar F (w 0 * u) *
      (quadraticChar F ((-1) ^ (m + 1) * ∏ i, Fin.tail w i) * (Fintype.card F : ℤ) ^ m *
        if c - u = 0 then (Fintype.card F : ℤ) - 1 else -1) =
      quadraticChar F ((-1) ^ (m + 1) * ∏ i, Fin.tail w i) * (Fintype.card F : ℤ) ^ m *
        ((Fintype.card F : ℤ) * (if u = c then quadraticChar F (w 0 * u) else 0) -
          quadraticChar F (w 0 * u)) := by
    by_cases h : u = c
    · simp only [h, sub_self, ite_true]
      ring
    · simp only [sub_eq_zero, Ne.symm h, h, ite_false]
      ring
  rw [sum_congr rfl fun u _ ↦ hu u, ← mul_sum, sum_sub_distrib, ← mul_sum,
    Fintype.sum_ite_eq', sum_quadraticChar_mul hF (hw 0), Fin.prod_univ_succ w]
  simp only [Fin.tail, map_mul, map_pow]
  ring

/-- The diagonal count in odd rank `2m + 1` and in even rank `2m + 2`, over `Fin n`, proved
together by induction on `m`. -/
private theorem card_sum_mul_sq_fin (hF : ringChar F ≠ 2) (m : ℕ) :
    (∀ w : Fin (2 * m + 1) → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (#{x : Fin (2 * m + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
        (Fintype.card F : ℤ) ^ (2 * m) +
          quadraticChar F ((-1) ^ m * (∏ i, w i) * c) * (Fintype.card F : ℤ) ^ m) ∧
    (∀ w : Fin (2 * m + 1 + 1) → F, (∀ i, w i ≠ 0) → ∀ c : F,
      (#{x : Fin (2 * m + 1 + 1) → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
        (Fintype.card F : ℤ) ^ (2 * m + 1) +
          quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) * (Fintype.card F : ℤ) ^ m *
            if c = 0 then (Fintype.card F : ℤ) - 1 else -1) := by
  induction m with
  | zero =>
    exact ⟨card_sum_mul_sq_fin_one hF,
      card_sum_mul_sq_fin_even_of_odd hF (card_sum_mul_sq_fin_one hF)⟩
  | succ m ih =>
    have hodd := card_sum_mul_sq_fin_odd_of_even hF ih.2
    exact ⟨hodd, card_sum_mul_sq_fin_even_of_odd hF hodd⟩

/-- Reindexing the variables of a diagonal form along an equivalence `ι ≃ Fin n`. -/
private theorem card_sum_mul_sq_eq_fin {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n)
    (w : ι → F) (c : F) :
    #{x : ι → F | ∑ i, w i * x i ^ 2 = c} =
      #{y : Fin n → F | ∑ j, w (e.symm j) * y j ^ 2 = c} := by
  refine card_equiv (e.arrowCongr (Equiv.refl F)) fun x ↦ ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq]
  rw [e.symm.sum_comp (fun i ↦ w i * x i ^ 2)]

variable (hF : ringChar F ≠ 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
include hF

/-- **Points on a diagonal quadric in odd rank.** Over a finite field of odd characteristic with
`q` elements, if `w : ι → F` has nonzero entries and `ι` has `2m + 1` elements, then
`∑ wᵢ xᵢ² = c` has `q^{2m} + χ((-1)^m (∏ wᵢ) c) q^m` solutions. -/
theorem card_sum_mul_sq_eq_of_card_eq_two_mul_add_one {m : ℕ}
    (hι : Fintype.card ι = 2 * m + 1) {w : ι → F} (hw : ∀ i, w i ≠ 0) (c : F) :
    (#{x : ι → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * m) +
        quadraticChar F ((-1) ^ m * (∏ i, w i) * c) * (Fintype.card F : ℤ) ^ m := by
  let e := Fintype.equivFinOfCardEq hι
  rw [card_sum_mul_sq_eq_fin e, (card_sum_mul_sq_fin hF m).1 _ (fun _ ↦ hw _),
    e.symm.prod_comp w]

/-- **Points on a diagonal quadric in even rank.** Over a finite field of odd characteristic with
`q` elements, if `w : ι → F` has nonzero entries and `ι` has `2m + 2` elements, then
`∑ wᵢ xᵢ² = c` has `q^{2m+1} + χ((-1)^{m+1} ∏ wᵢ) q^m ν(c)` solutions, where `ν(0) = q - 1` and
`ν(c) = -1` for `c ≠ 0`. -/
theorem card_sum_mul_sq_eq_of_card_eq_two_mul_add_two {m : ℕ}
    (hι : Fintype.card ι = 2 * m + 2) {w : ι → F} (hw : ∀ i, w i ≠ 0) (c : F) :
    (#{x : ι → F | ∑ i, w i * x i ^ 2 = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * m + 1) +
        quadraticChar F ((-1) ^ (m + 1) * ∏ i, w i) * (Fintype.card F : ℤ) ^ m *
          if c = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  let e := Fintype.equivFinOfCardEq (hι.trans (by omega) : Fintype.card ι = 2 * m + 1 + 1)
  rw [card_sum_mul_sq_eq_fin e, (card_sum_mul_sq_fin hF m).2 _ (fun _ ↦ hw _),
    e.symm.prod_comp w]

end Diagonal

end TauCeti

namespace Matrix.IsSymm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Matrix ι ι F}

/-- A nondegenerate symmetric matrix is congruent to a diagonal matrix `diagonal d`; the solutions
of `xᵀ A x = c` correspond to those of `∑ dᵢ yᵢ² = c`, all `dᵢ` are nonzero, and `∏ dᵢ` lies in
the square class of `det A`. -/
private theorem exists_card_dotProduct_mulVec_eq (hA : A.IsSymm) (hF : ringChar F ≠ 2)
    (hdet : A.det ≠ 0) :
    ∃ d : ι → F, (∀ i, d i ≠ 0) ∧
      (∀ a : F, quadraticChar F (a * ∏ i, d i) = quadraticChar F (a * A.det)) ∧
      ∀ c : F, #{x : ι → F | x ⬝ᵥ A *ᵥ x = c} = #{y : ι → F | ∑ i, d i * y i ^ 2 = c} := by
  have : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hF)
  obtain ⟨P, d, hP, hPAP⟩ := hA.exists_isUnit_transpose_mul_mul_eq_diagonal
  have hPdet : P.det ≠ 0 := ((isUnit_iff_isUnit_det P).mp hP).ne_zero
  have hprod : ∏ i, d i = P.det ^ 2 * A.det := by
    rw [← det_diagonal, ← hPAP, det_mul, det_mul, det_transpose]
    ring
  have hd (i : ι) : d i ≠ 0 :=
    prod_ne_zero_iff.mp (hprod ▸ mul_ne_zero (pow_ne_zero 2 hPdet) hdet) i (mem_univ i)
  refine ⟨d, hd, fun a ↦ ?_, fun c ↦ ?_⟩
  · rw [hprod, mul_left_comm, map_mul, quadraticChar_sq_one' hPdet, one_mul]
  · -- The substitution `x = P y` carries `xᵀ A x` to `yᵀ (Pᵀ A P) y = ∑ dᵢ yᵢ²`.
    have hform (y : ι → F) : (P *ᵥ y) ⬝ᵥ A *ᵥ (P *ᵥ y) = ∑ i, d i * y i ^ 2 := by
      have hcongr : y ⬝ᵥ (Pᵀ * A * P) *ᵥ y = (P *ᵥ y) ⬝ᵥ A *ᵥ (P *ᵥ y) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      rw [← hcongr, hPAP]
      simp only [dotProduct, mulVec_diagonal]
      exact sum_congr rfl fun i _ ↦ by ring
    have hinv : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hP)
    have hinv' : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hP)
    refine (card_nbij' (fun y ↦ P *ᵥ y) (fun x ↦ P⁻¹ *ᵥ x) ?_ ?_ ?_ ?_).symm
    · intro y hy
      simpa only [mem_coe, mem_filter, mem_univ, true_and, hform] using hy
    · intro x hx
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      rw [← hform, mulVec_mulVec, hinv', one_mulVec, hx]
    · intro y _
      simp only [mulVec_mulVec, hinv, one_mulVec]
    · intro x _
      simp only [mulVec_mulVec, hinv', one_mulVec]

/-- **Points on a nondegenerate quadric in odd rank.** Over a finite field of odd characteristic
with `q` elements, if `A` is a symmetric matrix with `det A ≠ 0` indexed by a type with `2m + 1`
elements, then `xᵀ A x = c` has `q^{2m} + χ((-1)^m det A · c) q^m` solutions. -/
theorem card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_one (hA : A.IsSymm)
    (hF : ringChar F ≠ 2) (hdet : A.det ≠ 0) {m : ℕ} (hι : Fintype.card ι = 2 * m + 1) (c : F) :
    (#{x : ι → F | x ⬝ᵥ A *ᵥ x = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * m) +
        quadraticChar F ((-1) ^ m * A.det * c) * (Fintype.card F : ℤ) ^ m := by
  obtain ⟨d, hd, hχ, hcard⟩ := hA.exists_card_dotProduct_mulVec_eq hF hdet
  rw [hcard, TauCeti.card_sum_mul_sq_eq_of_card_eq_two_mul_add_one hF hι hd,
    show (-1) ^ m * (∏ i, d i) * c = ((-1) ^ m * c) * ∏ i, d i by ring, hχ,
    show (-1) ^ m * c * A.det = (-1) ^ m * A.det * c by ring]

/-- **Points on a nondegenerate quadric in even rank.** Over a finite field of odd characteristic
with `q` elements, if `A` is a symmetric matrix with `det A ≠ 0` indexed by a type with `2m + 2`
elements, then `xᵀ A x = c` has `q^{2m+1} + χ((-1)^{m+1} det A) q^m ν(c)` solutions, where
`ν(0) = q - 1` and `ν(c) = -1` for `c ≠ 0`. -/
theorem card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two (hA : A.IsSymm)
    (hF : ringChar F ≠ 2) (hdet : A.det ≠ 0) {m : ℕ} (hι : Fintype.card ι = 2 * m + 2) (c : F) :
    (#{x : ι → F | x ⬝ᵥ A *ᵥ x = c} : ℤ) =
      (Fintype.card F : ℤ) ^ (2 * m + 1) +
        quadraticChar F ((-1) ^ (m + 1) * A.det) * (Fintype.card F : ℤ) ^ m *
          if c = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  obtain ⟨d, hd, hχ, hcard⟩ := hA.exists_card_dotProduct_mulVec_eq hF hdet
  rw [hcard, TauCeti.card_sum_mul_sq_eq_of_card_eq_two_mul_add_two hF hι hd, hχ]

end Matrix.IsSymm
