/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.Polynomial.Colex.Basic

/-!
# Polynomials of bounded degree as lexicographic tuples

For a ring `R` with a partial order, the polynomials of degree `< n` form an additive subgroup of
`R[X]` with its colexicographic order, and listing their coefficients from degree `n - 1` down to
degree `0` identifies this ordered group with `Rⁿ` ordered lexicographically. For `R = ℤ`, the
polynomials of degree at most `d` in `ℤ[t]`, ordered with `t` infinitely large, form the ordered
group `ℤ^{d+1}` with the lexicographic order.

## Main declarations

* `Polynomial.Colex.degreeLT R n`: the polynomials of degree `< n`, as an additive subgroup of
  `Colex R[X]`.
* `Polynomial.Colex.degreeLTEquiv R n`: its isomorphism of ordered additive groups with
  `Lex (Fin n → R)`, sending `p` to `(p_{n-1}, …, p_1, p_0)`; its inverse is described by
  `Polynomial.Colex.degreeLTEquiv_symm_apply_coeff`.

## Main results

* `Polynomial.Colex.ordConnected_degreeLT`: the polynomials of degree `< n` form an order-convex
  subset of `Colex R[X]`, so `degreeLT R n` is a convex subgroup.
* `Polynomial.Colex.degreeLT_mono`: these subgroups increase with `n`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §2.3.
-/

public section

namespace Polynomial

namespace Colex

variable (R : Type*) [Ring R]

/-- The polynomials of degree `< n`, as an additive subgroup of `Colex R[X]`. -/
def degreeLT (n : ℕ) : AddSubgroup (Colex R[X]) where
  carrier := {p | ofColex p ∈ Polynomial.degreeLT R n}
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    rw [ofColex_add]
    exact add_mem hx hy
  zero_mem' := by
    rw [Set.mem_ofPred_eq, ofColex_zero]
    exact zero_mem _
  neg_mem' {x} hx := by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [ofColex_neg]
    exact neg_mem hx

variable {R}

/-- An element of `Colex R[X]` lies in `degreeLT R n` exactly when its degree is `< n`. -/
@[simp, grind =]
theorem mem_degreeLT {n : ℕ} {x : Colex R[X]} : x ∈ degreeLT R n ↔ (ofColex x).degree < n :=
  Polynomial.mem_degreeLT

variable (R) in
/-- Only `0` has degree `< 0`. -/
@[simp]
theorem degreeLT_zero : degreeLT R 0 = ⊥ := by
  ext x
  simp

/-- The polynomials of degree `< m` have degree `< n` for `m ≤ n`. -/
@[gcongr, mono]
theorem degreeLT_mono {m n : ℕ} (h : m ≤ n) : degreeLT R m ≤ degreeLT R n :=
  fun _ hx ↦ mem_degreeLT.2 ((mem_degreeLT.1 hx).trans_le (by exact_mod_cast h))

-- The coefficients from degree `n - 1` down to degree `0`, as a bijection.
private noncomputable def degreeLTEquivAux (n : ℕ) : degreeLT R n ≃ Lex (Fin n → R) :=
  (Equiv.subtypeEquiv ofColex fun _ ↦ Iff.rfl).trans <|
    (Polynomial.degreeLTEquiv R n).toEquiv.trans <|
      (Equiv.arrowCongr Fin.revPerm (Equiv.refl R)).trans toLex

private theorem degreeLTEquivAux_apply {n : ℕ} (p : degreeLT R n) (i : Fin n) :
    degreeLTEquivAux n p i = (ofColex (p : Colex R[X])).coeff i.rev :=
  rfl

variable [PartialOrder R]

/-- The polynomials of degree `< n` form an order-convex subset of `Colex R[X]`: a polynomial lying
between two of them has degree `< n` as well. -/
instance ordConnected_degreeLT (n : ℕ) : (degreeLT R n : Set (Colex R[X])).OrdConnected := by
  refine ⟨fun a ha b hb x hx ↦ ?_⟩
  simp only [SetLike.mem_coe, mem_degreeLT] at ha hb ⊢
  by_contra! hxn
  -- `x` has larger degree than `a` and `b`, so its leading coefficient decides both comparisons.
  have hax : a < x := hx.1.lt_of_ne (by rintro rfl; exact (ha.trans_le hxn).false)
  have hxb : x < b := hx.2.lt_of_ne (by rintro rfl; exact (hb.trans_le hxn).false)
  exact ((lt_iff_of_degree_lt (ha.trans_le hxn)).1 hax).not_gt
    ((lt_iff_of_degree_gt (hb.trans_le hxn)).1 hxb)

/-- Reversing the coefficients turns the colexicographic order into the lexicographic one. -/
private theorem degreeLTEquivAux_lt_iff {n : ℕ} {p q : degreeLT R n} :
    degreeLTEquivAux n p < degreeLTEquivAux n q ↔ p < q := by
  obtain ⟨x, hx⟩ := p
  obtain ⟨y, hy⟩ := q
  rw [mem_degreeLT] at hx hy
  have hx0 (j : ℕ) (hj : n ≤ j) : (ofColex x).coeff j = 0 :=
    coeff_eq_zero_of_degree_lt (hx.trans_le (by exact_mod_cast hj))
  have hy0 (j : ℕ) (hj : n ≤ j) : (ofColex y).coeff j = 0 :=
    coeff_eq_zero_of_degree_lt (hy.trans_le (by exact_mod_cast hj))
  rw [Subtype.mk_lt_mk, lt_iff]
  -- The order on `Lex (Fin n → R)` is by definition `Pi.Lex (· < ·) (· < ·)`.
  constructor
  · rintro ⟨i, hi, hlt⟩
    refine ⟨i.rev, fun j hj ↦ ?_, by simpa [degreeLTEquivAux_apply] using hlt⟩
    rcases lt_or_ge j n with hjn | hjn
    · simpa [degreeLTEquivAux_apply] using
        hi (Fin.rev ⟨j, hjn⟩) (Fin.rev_lt_iff.1 (by simpa [Fin.lt_def] using hj))
    · rw [hx0 j hjn, hy0 j hjn]
  · rintro ⟨i, hi, hlt⟩
    have hin : i < n := by
      by_contra! hni
      rw [hx0 i hni, hy0 i hni] at hlt
      exact hlt.false
    refine ⟨Fin.rev ⟨i, hin⟩, fun j hj ↦ ?_, by simpa [degreeLTEquivAux_apply] using hlt⟩
    rw [degreeLTEquivAux_apply, degreeLTEquivAux_apply]
    exact hi _ (by simpa [Fin.lt_def] using Fin.lt_rev_iff.1 hj)

variable (R) in
/-- Listing the coefficients from degree `n - 1` down to degree `0` identifies the polynomials of
degree `< n`, ordered colexicographically, with `Rⁿ` ordered lexicographically. -/
noncomputable def degreeLTEquiv (n : ℕ) : degreeLT R n ≃+o Lex (Fin n → R) where
  toEquiv := degreeLTEquivAux n
  map_add' p q := ofLex.injective <| funext fun i ↦ by
    rw [ofLex_add]
    simp [degreeLTEquivAux_apply]
  map_le_map_iff' {p q} := by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
    exact or_congr degreeLTEquivAux_lt_iff (degreeLTEquivAux n).injective.eq_iff

@[simp, grind =]
theorem degreeLTEquiv_apply {n : ℕ} (p : degreeLT R n) (i : Fin n) :
    degreeLTEquiv R n p i = (ofColex (p : Colex R[X])).coeff i.rev :=
  degreeLTEquivAux_apply p i

/-- The polynomial corresponding to `v : Lex (Fin n → R)` has coefficient `v (n - 1 - i)` in each
degree `i < n` and coefficient `0` in each degree `≥ n`. -/
@[simp, grind =]
theorem degreeLTEquiv_symm_apply_coeff {n : ℕ} (v : Lex (Fin n → R)) (i : ℕ) :
    (ofColex ((degreeLTEquiv R n).symm v : Colex R[X])).coeff i =
      if h : i < n then v (Fin.rev ⟨i, h⟩) else 0 := by
  split_ifs with h
  · simpa only [Pi.ofLex_apply, degreeLTEquiv_apply, Fin.rev_rev, Fin.val_mk] using
      congrFun (congrArg ofLex ((degreeLTEquiv R n).apply_symm_apply v)) (Fin.rev ⟨i, h⟩)
  · exact coeff_eq_zero_of_degree_lt <| (mem_degreeLT.1 ((degreeLTEquiv R n).symm v).2).trans_le
      (by exact_mod_cast not_lt.1 h)

end Colex

end Polynomial
