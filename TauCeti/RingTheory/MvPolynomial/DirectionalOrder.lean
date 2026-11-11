/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import TauCeti.RingTheory.MvPolynomial.LineRestriction
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Detecting ambient order along affine lines

For a polynomial of finite ambient order at a point over an infinite domain, there is a
direction along which its restriction has exactly that order. The coefficient of degree `m`
on a line is the value of the degree-`m` homogeneous Taylor component at the direction.
Thus the good directions are detected by a nonzero polynomial, rather than assumed to exist.
For finitely many polynomial–point pairs, one direction detects all their orders:
the product of their first nonzero homogeneous Taylor components remains nonzero.

These coefficient formulas supply the algebraic input for choosing uniform directions in
families of constant ambient order, and hence for analytic preparation of discriminants.
Restricting to lines through the origin also detects homogeneity over an infinite domain:
`MvPolynomial.isHomogeneous_iff_forall_eval_smul` says that `p` is homogeneous of degree `n`
exactly when `eval (a • x) p = a ^ n • eval x p` for all `a` and `x`.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  Sections 2–3.
-/

public section

namespace MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Translating the polynomial first gives the restriction to an affine line. -/
theorem aeval_C_add_C_mul_X_eq (p : MvPolynomial σ R) (a v : σ → R) :
    aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p =
      aeval (fun i ↦ Polynomial.C (v i) * Polynomial.X) (taylor a p) := by
  rw [taylor_apply, ← AlgHom.comp_apply]
  congr 1
  ext i
  simp [add_comm]

/-- The coefficients of an affine-line restriction are the homogeneous Taylor components
evaluated at the direction. -/
@[simp]
theorem coeff_aeval_C_add_C_mul_X (p : MvPolynomial σ R) (a v : σ → R) (m : ℕ) :
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff m =
      eval v (homogeneousComponent m (taylor a p)) := by
  rw [aeval_C_add_C_mul_X_eq, coeff_aeval_C_mul_X]

/-- Terms below the ambient order vanish in every affine-line restriction. -/
theorem coeff_aeval_C_add_C_mul_X_eq_zero (p : MvPolynomial σ R) (a v : σ → R)
    {m : ℕ} (hm : (m : ℕ∞) < p.orderAt a) :
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff m = 0 := by
  rw [coeff_aeval_C_add_C_mul_X]
  have hzero : homogeneousComponent m (taylor a p) = 0 := by
    ext d
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · exact le_orderAt_iff.1 le_rfl d (hd ▸ hm)
    · rfl
  simp [hzero]

/-- The first nonzero homogeneous Taylor component is nonzero. -/
theorem homogeneousComponent_ne_zero_of_orderAt_eq (p : MvPolynomial σ R)
    (a : σ → R) {m : ℕ} (hm : p.orderAt a = m) :
    homogeneousComponent m (taylor a p) ≠ 0 := by
  obtain ⟨⟨d, hd, hdm⟩, _⟩ := orderAt_eq_coe_iff.1 hm
  intro hzero
  have := congrArg (fun q : MvPolynomial σ R ↦ q.coeff d) hzero
  simp [coeff_homogeneousComponent, hdm, hd] at this

/-- Restriction to an affine line cannot decrease the ambient order, including the zero
polynomial and lines on which the restriction vanishes identically. -/
theorem orderAt_le_trailingDegree_aeval_C_add_C_mul_X (p : MvPolynomial σ R)
    (a v : σ → R) :
    p.orderAt a ≤
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)
        p).trailingDegree := by
  rw [Polynomial.trailingDegree]
  apply Finset.le_min
  intro k hk
  by_contra h
  exact (Polynomial.mem_support_iff.1 hk)
    (p.coeff_aeval_C_add_C_mul_X_eq_zero a v (lt_of_not_ge h))

/-- A line detects finite ambient order exactly when the first homogeneous Taylor
component does not vanish at its direction. -/
theorem trailingDegree_aeval_C_add_C_mul_X_eq_iff (p : MvPolynomial σ R)
    (a v : σ → R) {m : ℕ} (hm : p.orderAt a = m) :
    (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).trailingDegree =
      (m : ℕ∞) ↔
      eval v (homogeneousComponent m (taylor a p)) ≠ 0 := by
  rw [← coeff_aeval_C_add_C_mul_X]
  constructor
  · intro h
    have hq : aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p ≠ 0 :=
      Polynomial.trailingDegree_eq_top.not.1 (by simp [h])
    have hn := Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some h
    simpa only [hn] using Polynomial.coeff_natTrailingDegree_ne_zero.2 hq
  · intro h
    exact le_antisymm (Polynomial.trailingDegree_le_of_ne_zero h)
      (hm ▸ p.orderAt_le_trailingDegree_aeval_C_add_C_mul_X a v)

end CommSemiring

section InfiniteDomain

variable [CommRing R] [IsDomain R] [Infinite R]

/-- One direction simultaneously detects the ambient orders of finitely many polynomials
at specified, possibly different, points. Zero polynomials are allowed and retain infinite
order. The empty family imposes no restriction on the direction. -/
theorem exists_forall_trailingDegree_aeval_C_add_C_mul_X_eq {ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial σ R) (a : ι → σ → R) :
    ∃ v : σ → R, ∀ i ∈ s,
      (aeval (fun j ↦ Polynomial.C (a i j) + Polynomial.C (v j) * Polynomial.X)
        (p i)).trailingDegree = (p i).orderAt (a i) := by
  classical
  let m (i : ι) := ((p i).orderAt (a i)).toNat
  let H (i : ι) := if p i = 0 then 1 else homogeneousComponent (m i) (taylor (a i) (p i))
  have hm (i : ι) (hi : p i ≠ 0) : (p i).orderAt (a i) = m i :=
    (ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hi)).symm
  have hH (i : ι) : H i ≠ 0 := by
    by_cases hi : p i = 0
    · simp [H, hi]
    · simpa only [H, ite_eq_right hi] using
        (p i).homogeneousComponent_ne_zero_of_orderAt_eq (a i) (hm i hi)
  have hprod : ∏ i ∈ s, H i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hH i
  obtain ⟨v, hv⟩ : ∃ v, eval v (∏ i ∈ s, H i) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext h)
  have hv' : ∀ i ∈ s, eval v (H i) ≠ 0 := by
    simpa only [map_prod, Finset.prod_ne_zero_iff] using hv
  refine ⟨v, fun i hi ↦ ?_⟩
  by_cases hpi : p i = 0
  · simp [hpi]
  rw [hm i hpi]
  exact ((p i).trailingDegree_aeval_C_add_C_mul_X_eq_iff (a i) v (hm i hpi)).2
    (by simpa only [H, ite_eq_right hpi] using hv' i hi)

/-- A polynomial of ambient order `m` admits a line restriction that is nonzero and has
order exactly `m` at the line parameter zero. -/
theorem exists_natTrailingDegree_aeval_C_add_C_mul_X_eq (p : MvPolynomial σ R)
    (a : σ → R) {m : ℕ} (hm : p.orderAt a = m) :
    ∃ v : σ → R,
      aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p ≠ 0 ∧
      Polynomial.natTrailingDegree
        (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p) = m := by
  classical
  obtain ⟨v, hv⟩ := exists_forall_trailingDegree_aeval_C_add_C_mul_X_eq
    {()} (fun _ ↦ p) (fun _ ↦ a)
  have hdegree :
      (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X)
        p).trailingDegree = (m : ℕ∞) := by
    simpa only [hm] using hv () (Finset.mem_singleton_self ())
  refine ⟨v, Polynomial.trailingDegree_eq_top.not.1 (by simp [hdegree]), ?_⟩
  exact Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some hdegree

/-- Over an infinite domain, a polynomial is homogeneous of degree `n` exactly when scaling the
point by `a` scales its value by `a ^ n`. The reverse implication needs infinitely many scalars:
over a finite field with `q` elements, `X ^ q - X` vanishes everywhere without being
homogeneous. -/
theorem isHomogeneous_iff_forall_eval_smul {p : MvPolynomial σ R} {n : ℕ} :
    p.IsHomogeneous n ↔ ∀ (a : R) (x : σ → R), eval (a • x) p = a ^ n • eval x p := by
  refine ⟨fun hp a x => hp.eval_smul x a, fun h => ?_⟩
  -- The restriction of `p` to the line through `x` is the monomial `eval x p • t ^ n`, so its
  -- coefficient of degree `m ≠ n`, the degree-`m` component evaluated at `x`, vanishes.
  have hcomp : ∀ m ≠ n, homogeneousComponent m p = 0 := by
    intro m hm
    refine MvPolynomial.funext fun x => ?_
    have hQ : aeval (fun i ↦ Polynomial.C (x i) * Polynomial.X) p =
        Polynomial.monomial n (eval x p) := Polynomial.funext fun a => by
      have hline := eval_aeval_C_add_C_mul_X p 0 x a
      simp only [Pi.zero_apply, map_zero, zero_add] at hline
      rw [hline, h, Polynomial.eval_monomial, smul_eq_mul, mul_comm]
    rw [map_zero, ← coeff_aeval_C_mul_X, hQ, Polynomial.coeff_monomial_of_ne _ hm]
  have hp : p = homogeneousComponent n p := by
    conv_lhs => rw [← sum_homogeneousComponent p]
    refine Finset.sum_eq_single n (fun m _ hm => hcomp m hm) fun hn => ?_
    exact homogeneousComponent_eq_zero n p (by simpa [Nat.lt_succ_iff] using hn)
  rw [hp]
  exact homogeneousComponent_isHomogeneous n p

end InfiniteDomain


end MvPolynomial
