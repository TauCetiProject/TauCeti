/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Associated
public import TauCeti.RingTheory.MvPolynomial.Prime
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant

/-!
# The squared Vandermonde product is prime among symmetric polynomials

Let `δ = ∏_{i < j} (X j - X i)` be the Vandermonde product of the variables of
`MvPolynomial (Fin n) R`. Permuting the variables multiplies `δ` by the sign of the permutation
(`MvPolynomial.rename_vandermonde`), so `δ ^ 2`, the discriminant of `∏ i, (X - X i)`, is
symmetric.

Over a domain `R` in which `2 ≠ 0`:

* a polynomial that changes sign under every transposition of two variables vanishes on each
  diagonal `X i = X j`, so it is divisible by each prime `X j - X i`, and hence by `δ`
  (`MvPolynomial.vandermonde_dvd_of_rename_swap`);
* a symmetric polynomial divisible by one difference `X a - X b` is divisible by all of them, so
  by `δ`; the quotient is antisymmetric, so it is divisible by `δ` again, and the polynomial is
  divisible by `δ ^ 2` (`MvPolynomial.vandermonde_sq_dvd_of_isSymmetric`);
* consequently, for `n ≥ 2`, `δ ^ 2` is a prime element of the symmetric subalgebra
  (`MvPolynomial.prime_vandermonde_sq`). Through the fundamental theorem of symmetric polynomials
  this says that the discriminant of the generic monic polynomial of degree `n` is prime.

The hypothesis `2 ≠ 0` cannot be dropped: in characteristic `2` the Vandermonde product `δ` is
itself symmetric, and `δ ^ 2` is not prime among symmetric polynomials.

## Main results

* `MvPolynomial.rename_vandermonde`: `rename e δ = sign e • δ`.
* `MvPolynomial.isSymmetric_vandermonde_sq`: `δ ^ 2` is symmetric.
* `MvPolynomial.vandermonde_dvd_of_forall_dvd`: `δ` divides every polynomial divisible by each
  difference `X j - X i`.
* `MvPolynomial.vandermonde_dvd_of_rename_swap`: `δ` divides every antisymmetric polynomial.
* `MvPolynomial.vandermonde_sq_dvd_of_isSymmetric`: `δ ^ 2` divides every symmetric polynomial
  divisible by some difference `X a - X b`.
* `MvPolynomial.prime_vandermonde_sq`: `δ ^ 2` is prime in `symmetricSubalgebra (Fin n) R`.
-/

public section

open Finset Equiv

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The Vandermonde product is antisymmetric**: renaming the variables along a permutation `e`
multiplies `∏_{i < j} (X j - X i)` by the sign of `e`. -/
theorem rename_vandermonde (e : Perm (Fin n)) :
    rename e (∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin n) R)) =
      Perm.sign e • ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i) := by
  rw [← TauCeti.alternant_fin_val_eq_vandermonde, TauCeti.rename_alternant]

/-- The square of the Vandermonde product is a symmetric polynomial. -/
theorem isSymmetric_vandermonde_sq :
    ((∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i)) ^ 2 : MvPolynomial (Fin n) R).IsSymmetric := by
  intro e
  rw [map_pow, rename_vandermonde, smul_pow, Int.units_sq, one_smul]

variable [IsDomain R]

private theorem vandermonde_ne_zero :
    ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin n) R) ≠ 0 := by
  rw [← Matrix.det_vandermonde]
  exact Matrix.det_vandermonde_ne_zero_iff.2 X_injective

/-- Over a domain, a polynomial divisible by each difference `X j - X i` of two variables is
divisible by their product, the Vandermonde product. -/
theorem vandermonde_dvd_of_forall_dvd {p : MvPolynomial (Fin n) R}
    (h : ∀ i j : Fin n, i < j → X j - X i ∣ p) :
    ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin n) R) ∣ p := by
  classical
  rw [← prod_finset_product' {q : Fin n × Fin n | q.1 < q.2} univ Ioi (by simp)]
  refine prod_primes_dvd_of_pairwise_not_dvd
    (fun q hq ↦ prime_X_sub_X (mem_filter.1 hq).2.ne') ?_ fun q hq ↦ h _ _ (mem_filter.1 hq).2
  rintro ⟨c, d⟩ hcd ⟨a, b⟩ hab hne hdvd
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hab hcd
  -- Renaming `d` to `c` kills `X d - X c`, so it kills its multiple `X b - X a`.
  have h0 := X_sub_X_dvd_iff.1 hdvd
  simp only [map_sub, rename_X, sub_eq_zero, X_inj, Function.update_apply, id] at h0
  refine hne (Eq.symm ?_)
  split_ifs at h0 with h1 h2 h2 <;> simp only [Prod.mk.injEq] <;> grind

/-- Over a domain in which `2 ≠ 0`, a polynomial that changes sign under every transposition of
two variables is divisible by the Vandermonde product. -/
theorem vandermonde_dvd_of_rename_swap (h2 : (2 : R) ≠ 0) {p : MvPolynomial (Fin n) R}
    (hp : ∀ i j : Fin n, i ≠ j → rename (swap i j) p = -p) :
    ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin n) R) ∣ p := by
  classical
  refine vandermonde_dvd_of_forall_dvd fun i j hij ↦ X_sub_X_dvd_iff.2 ?_
  -- On the diagonal `X j = X i` the transposition of `i` and `j` acts trivially, so the value
  -- of `p` there equals its own negative.
  have hcomp : Function.update id j i ∘ swap i j = Function.update id j i := by
    ext k
    simp only [Function.comp_apply, Function.update_apply, id, swap_apply_def]
    split_ifs <;> grind
  have hneg : rename (Function.update id j i) p = -rename (Function.update id j i) p := by
    conv_lhs => rw [← neg_neg p, ← hp i j hij.ne, map_neg, rename_rename, hcomp]
  have h2' : (2 : MvPolynomial (Fin n) R) ≠ 0 := by
    rw [← map_ofNat C 2, Ne, C_eq_zero]
    exact h2
  refine (mul_eq_zero.1 ?_).resolve_left h2'
  rw [two_mul]
  exact add_eq_zero_iff_eq_neg.2 hneg

/-- Over a domain in which `2 ≠ 0`, a symmetric polynomial divisible by one difference `X a - X b`
of two distinct variables is divisible by the square of the Vandermonde product. -/
theorem vandermonde_sq_dvd_of_isSymmetric (h2 : (2 : R) ≠ 0) {p : MvPolynomial (Fin n) R}
    (hp : p.IsSymmetric) {a b : Fin n} (hab : a ≠ b) (h : X a - X b ∣ p) :
    (∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin n) R)) ^ 2 ∣ p := by
  -- Moving `a` to `j` and `b` to `i`, the symmetric `p` is divisible by every `X j - X i`.
  have hall : ∀ i j : Fin n, i < j → X j - X i ∣ p := by
    intro i j hij
    have hc : swap a j b ≠ j := by simpa using (swap a j).injective.ne hab.symm
    have he₁ : (swap (swap a j b) i * swap a j) a = j := by
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hc.symm hij.ne']
    have he₂ : (swap (swap a j b) i * swap a j) b = i := by
      rw [Perm.mul_apply, swap_apply_left]
    have := map_dvd (rename (swap (swap a j b) i * swap a j)) h
    rwa [hp, map_sub, rename_X, rename_X, he₁, he₂] at this
  obtain ⟨q, rfl⟩ := vandermonde_dvd_of_forall_dvd hall
  -- The quotient by the antisymmetric Vandermonde product is antisymmetric.
  have hq : ∀ i j : Fin n, i ≠ j → rename (swap i j) q = -q := by
    intro i j hij
    have := hp (swap i j)
    rw [map_mul, rename_vandermonde, Perm.sign_swap hij, Units.neg_smul, one_smul, neg_mul,
      ← mul_neg] at this
    exact neg_eq_iff_eq_neg.1 (mul_left_cancel₀ vandermonde_ne_zero this)
  rw [sq]
  exact mul_dvd_mul_left _ (vandermonde_dvd_of_rename_swap h2 hq)

/-- **The discriminant in the roots is prime among symmetric polynomials.** Over a domain in which
`2 ≠ 0`, for `n ≥ 2`, the square of the Vandermonde product of `n` variables is a prime element of
the subalgebra of symmetric polynomials. -/
theorem prime_vandermonde_sq (h2 : (2 : R) ≠ 0) (hn : 2 ≤ n) :
    Prime (⟨_, isSymmetric_vandermonde_sq⟩ : symmetricSubalgebra (Fin n) R) := by
  set δ : MvPolynomial (Fin n) R := ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i)
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin n, a < b :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.mk_lt_mk.2 one_pos⟩
  have hπ : Prime (X b - X a : MvPolynomial (Fin n) R) := prime_X_sub_X hab.ne'
  have hπδ : X b - X a ∣ δ ^ 2 :=
    (dvd_prod_of_mem (fun j ↦ X j - X a) (mem_Ioi.2 hab)).trans
      ((dvd_prod_of_mem (fun i ↦ ∏ j ∈ Ioi i, (X j - X i)) (mem_univ a)).trans
        (dvd_pow_self δ two_ne_zero))
  -- A symmetric polynomial divisible by `X b - X a` is a multiple of `δ ^ 2` in the subalgebra.
  have hdvd (x : symmetricSubalgebra (Fin n) R) (hx : X b - X a ∣ (x : MvPolynomial (Fin n) R)) :
      (⟨_, isSymmetric_vandermonde_sq⟩ : symmetricSubalgebra (Fin n) R) ∣ x := by
    obtain ⟨t, ht⟩ := vandermonde_sq_dvd_of_isSymmetric h2 x.property hab.ne' hx
    have hδ : δ ^ 2 ≠ 0 := pow_ne_zero 2 vandermonde_ne_zero
    have hts : t.IsSymmetric := fun e ↦ mul_left_cancel₀ hδ <|
      calc δ ^ 2 * rename e t = rename e (δ ^ 2 * t) := by
            rw [map_mul, isSymmetric_vandermonde_sq e]
        _ = δ ^ 2 * t := by rw [← ht, x.property e]
    exact ⟨⟨t, hts⟩, Subtype.ext ht⟩
  refine ⟨fun h0 ↦ pow_ne_zero 2 vandermonde_ne_zero congr(Subtype.val $h0), fun hu ↦
    hπ.not_isUnit (isUnit_of_dvd_unit hπδ (hu.map (symmetricSubalgebra (Fin n) R).val)),
    fun x y hxy ↦ ?_⟩
  have := hπδ.trans (map_dvd (symmetricSubalgebra (Fin n) R).val hxy)
  rw [map_mul] at this
  exact (hπ.dvd_or_dvd this).imp (hdvd x) (hdvd y)

end MvPolynomial
