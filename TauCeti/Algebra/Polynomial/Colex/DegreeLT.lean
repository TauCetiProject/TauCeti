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

For a linearly ordered ring `R`, the polynomials of degree `< n` form an additive subgroup of
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
  add_mem' := (Polynomial.degreeLT R n).add_mem
  zero_mem' := (Polynomial.degreeLT R n).zero_mem
  neg_mem' := (Polynomial.degreeLT R n).neg_mem

variable {R}

/-- An element of `Colex R[X]` lies in `degreeLT R n` exactly when its degree is `< n`. -/
@[simp]
theorem mem_degreeLT {n : ℕ} {x : Colex R[X]} : x ∈ degreeLT R n ↔ (ofColex x).degree < n :=
  Polynomial.mem_degreeLT

variable [LinearOrder R]

/-- The polynomials of degree `< n` form an order-convex subset of `Colex R[X]`: a polynomial lying
between two of them has degree `< n` as well. -/
theorem ordConnected_degreeLT (n : ℕ) : (degreeLT R n : Set (Colex R[X])).OrdConnected := by
  refine ⟨fun a ha b hb x hx ↦ ?_⟩
  obtain ⟨p, rfl⟩ := toColex.surjective a
  obtain ⟨q, rfl⟩ := toColex.surjective b
  obtain ⟨r, rfl⟩ := toColex.surjective x
  simp only [SetLike.mem_coe, mem_degreeLT, ofColex_toColex] at ha hb ⊢
  by_contra! hr
  -- `r` has larger degree than `p` and `q`, so its sign decides both comparisons.
  have hrp : toColex r ≤ toColex p := not_lt.1 fun h ↦ hx.2.not_gt <|
    (toColex_lt_toColex_iff_of_degree_lt (hb.trans_le hr)).2 <|
      (toColex_lt_toColex_iff_of_degree_lt (ha.trans_le hr)).1 h
  exact (ha.trans_le hr).ne (congrArg degree (toColex.injective (hx.1.antisymm hrp)))

-- The coefficients from degree `n - 1` down to degree `0`, as a bijection.
private noncomputable def degreeLTEquivAux (n : ℕ) : degreeLT R n ≃ Lex (Fin n → R) :=
  (Equiv.subtypeEquiv ofColex fun _ ↦ Iff.rfl).trans <|
    (Polynomial.degreeLTEquiv R n).toEquiv.trans <|
      (Equiv.arrowCongr Fin.revPerm (Equiv.refl R)).trans toLex

omit [LinearOrder R] in
private theorem degreeLTEquivAux_apply {n : ℕ} (p : degreeLT R n) (i : Fin n) :
    degreeLTEquivAux n p i = (ofColex (p : Colex R[X])).coeff i.rev :=
  rfl

private theorem strictMono_degreeLTEquivAux (n : ℕ) :
    StrictMono (degreeLTEquivAux (R := R) n) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  obtain ⟨p, rfl⟩ := toColex.surjective p
  obtain ⟨q, rfl⟩ := toColex.surjective q
  rw [mem_degreeLT, ofColex_toColex] at hp hq
  obtain ⟨i, hi, hlt⟩ := toColex_lt_toColex.1 (Subtype.mk_lt_mk.1 h)
  have hin : i < n := by
    by_contra! hni
    rw [coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast hni)),
      coeff_eq_zero_of_degree_lt (hq.trans_le (by exact_mod_cast hni))] at hlt
    exact hlt.false
  refine ⟨Fin.rev ⟨i, hin⟩, fun j hj ↦ ?_, ?_⟩
  · rw [degreeLTEquivAux_apply, degreeLTEquivAux_apply]
    exact hi _ (by simpa [Fin.lt_def] using Fin.lt_rev_iff.1 hj)
  · simpa [degreeLTEquivAux_apply] using hlt

variable (R) in
/-- Listing the coefficients from degree `n - 1` down to degree `0` identifies the polynomials of
degree `< n`, ordered colexicographically, with `Rⁿ` ordered lexicographically. -/
noncomputable def degreeLTEquiv (n : ℕ) : degreeLT R n ≃+o Lex (Fin n → R) where
  toEquiv := degreeLTEquivAux n
  map_add' p q := ofLex.injective <| funext fun i ↦ by
    rw [ofLex_add]
    simp [degreeLTEquivAux_apply]
  map_le_map_iff' := (strictMono_degreeLTEquivAux n).le_iff_le

@[simp]
theorem degreeLTEquiv_apply {n : ℕ} (p : degreeLT R n) (i : Fin n) :
    degreeLTEquiv R n p i = (ofColex (p : Colex R[X])).coeff i.rev :=
  degreeLTEquivAux_apply p i

/-- The polynomial corresponding to `v : Lex (Fin n → R)` has coefficient `v (n - 1 - i)` in each
degree `i < n` and coefficient `0` in each degree `≥ n`. -/
@[simp]
theorem degreeLTEquiv_symm_apply_coeff {n : ℕ} (v : Lex (Fin n → R)) (i : ℕ) :
    (ofColex ((degreeLTEquiv R n).symm v : Colex R[X])).coeff i =
      if h : i < n then v (Fin.rev ⟨i, h⟩) else 0 := by
  split_ifs with h
  · simpa using congrFun ((degreeLTEquiv R n).apply_symm_apply v) (Fin.rev ⟨i, h⟩)
  · exact coeff_eq_zero_of_degree_lt <| (mem_degreeLT.1 ((degreeLTEquiv R n).symm v).2).trans_le
      (by exact_mod_cast not_lt.1 h)

end Colex

end Polynomial
