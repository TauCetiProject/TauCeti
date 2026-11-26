/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Algebra.Squarefree
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Counting squarefree monic polynomials over a finite field

Over a finite field `𝔽_q` the number `s_n` of monic squarefree polynomials of degree `n` is
`s₀ = 1`, `s₁ = q` and `s_n = q ^ n - q ^ (n - 1)` for `n ≥ 2`. This is the count behind the
proportion `1 - 1/q` of squarefree polynomials among monic ones, and it is what turns
squarefreeness conditions on binary forms over finite fields (nonvanishing discriminants) into
explicit counts.

The count is classical (M. Rosen, *Number Theory in Function Fields*, Chapter 2; it is
also recalled in Ellenberg, Venkatesh and Westerland, *Homological stability for Hurwitz spaces
and the Cohen–Lenstra conjecture over function fields*, §8.7). The argument here avoids
generating functions: every monic `g` factors uniquely as `g = e ^ 2 * d` with `e` monic and `d`
monic squarefree. Sorting the `q ^ n` monic polynomials of degree `n`
(`Polynomial.ncard_setOf_monic_natDegree_eq`) by the degree `j` of `e`
gives `q ^ n = ∑_{0 ≤ j ≤ n/2} q ^ j * s_{n - 2j}`. Subtracting `q` times the same identity in
degree `n - 2` isolates `s_n` without solving the recursion. The existence of the factorization is
Mathlib's `exists_sq_mul_squarefree`, normalized to monic factors; its uniqueness is
`Squarefree.associated_of_sq_mul_eq_sq_mul`.

## Main definitions

* `Polynomial.monicSquarefreePolysOfDegree R n`: the monic squarefree polynomials of degree `n`.

## Main results

* `Polynomial.Monic.exists_sq_mul_squarefree`, `Polynomial.Monic.eq_of_sq_mul_eq_sq_mul`: over a
  domain whose polynomial ring has unique factorization, a monic polynomial is `e ^ 2 * d` with
  `e` monic and `d` monic squarefree, and `e`, `d` are unique.
* `Polynomial.monicSquarefreePolysOfDegree_zero`, `Polynomial.monicSquarefreePolysOfDegree_one`:
  in degree zero only `1` is monic squarefree, and over a domain every monic linear polynomial is
  squarefree.
* `Polynomial.sum_pow_mul_ncard_monicSquarefreePolysOfDegree`: over a finite field,
  `∑_{j ≤ n/2} q ^ j * s_{n - 2j} = q ^ n`.
* `Polynomial.ncard_monicSquarefreePolysOfDegree`: over a finite field,
  `s_n = q ^ n - q ^ (n - 1)` for `n ≥ 2`; `Polynomial.ncard_monicSquarefreePolysOfDegree_one`
  gives `s₁ = q`, and more generally `#R` over any domain `R`.
-/

public section

namespace Polynomial

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The monic squarefree polynomials of degree `n` over `R`. Over a finite field this is the
finite set counted by `Polynomial.ncard_monicSquarefreePolysOfDegree`. -/
def monicSquarefreePolysOfDegree (n : ℕ) : Set R[X] :=
  {g | g.Monic ∧ Squarefree g ∧ g.natDegree = n}

variable {R} in
/-- Membership in `monicSquarefreePolysOfDegree` is the conjunction defining it. -/
@[simp]
theorem mem_monicSquarefreePolysOfDegree_iff {n : ℕ} {g : R[X]} :
    g ∈ monicSquarefreePolysOfDegree R n ↔ g.Monic ∧ Squarefree g ∧ g.natDegree = n :=
  Iff.rfl

/-- Over a finite semiring there are finitely many monic squarefree polynomials of each degree. -/
theorem finite_monicSquarefreePolysOfDegree [Finite R] (n : ℕ) :
    (monicSquarefreePolysOfDegree R n).Finite :=
  (finite_setOf_monic_natDegree_eq R n).subset fun _ hg => ⟨hg.1, hg.2.2⟩

/-- The only monic squarefree polynomial of degree zero is `1`. -/
@[simp]
theorem monicSquarefreePolysOfDegree_zero : monicSquarefreePolysOfDegree R 0 = {1} := by
  ext g
  rw [mem_monicSquarefreePolysOfDegree_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨hg, _, hdeg⟩ => eq_one_of_monic_natDegree_zero hg hdeg, ?_⟩
  rintro rfl
  exact ⟨monic_one, squarefree_one, natDegree_one⟩

end CommSemiring

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

variable (R) in
/-- Over a domain every monic linear polynomial is irreducible, hence squarefree. -/
theorem monicSquarefreePolysOfDegree_one :
    monicSquarefreePolysOfDegree R 1 = {g : R[X] | g.Monic ∧ g.natDegree = 1} := by
  ext g
  simp only [mem_monicSquarefreePolysOfDegree_iff, Set.mem_ofPred_eq]
  refine ⟨fun ⟨hg, _, hdeg⟩ => ⟨hg, hdeg⟩, fun ⟨hg, hdeg⟩ => ⟨hg, ?_, hdeg⟩⟩
  exact (hg.irreducible_of_degree_eq_one (degree_eq_iff_natDegree_eq_of_pos one_pos |>.2 hdeg)
    ).squarefree

variable (R) in
/-- **Count of squarefree monic polynomials of degree one.** Over a domain `R` there are `#R`
monic squarefree linear polynomials; for a finite field with `q` elements this is `q`. -/
theorem ncard_monicSquarefreePolysOfDegree_one :
    (monicSquarefreePolysOfDegree R 1).ncard = Nat.card R := by
  rw [monicSquarefreePolysOfDegree_one, ncard_setOf_monic_natDegree_eq, pow_one]

variable [UniqueFactorizationMonoid R[X]]

/-- **Square times squarefree factorization of a monic polynomial.** Over a domain whose
polynomial ring has unique factorization, every monic polynomial is `e ^ 2 * d` with `e` monic and
`d` monic squarefree. -/
theorem Monic.exists_sq_mul_squarefree {g : R[X]} (hg : g.Monic) :
    ∃ e d : R[X], e.Monic ∧ d.Monic ∧ Squarefree d ∧ e ^ 2 * d = g := by
  obtain ⟨e, d, rfl, hd⟩ := _root_.exists_sq_mul_squarefree g
  -- The leading coefficients satisfy `lc(e) ^ 2 * lc(d) = 1`, so `lc(e)` is a unit by which `e`
  -- can be normalized, the square of that unit moving into `d`.
  have hlc : e.leadingCoeff * (e.leadingCoeff * d.leadingCoeff) = 1 := by
    rw [← mul_assoc, ← sq, ← leadingCoeff_pow, ← leadingCoeff_mul]
    exact hg
  obtain ⟨c, hc⟩ : ∃ c : R, c * e.leadingCoeff = 1 := ⟨_, (IsUnit.of_mul_eq_one _ hlc).val_inv_mul⟩
  have he : (C c * e).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hprod : (C c * e) ^ 2 * (C (e.leadingCoeff ^ 2) * d) = e ^ 2 * d := by
    calc (C c * e) ^ 2 * (C (e.leadingCoeff ^ 2) * d)
        = C ((c * e.leadingCoeff) ^ 2) * (e ^ 2 * d) := by
          simp only [map_pow, map_mul]
          ring
      _ = e ^ 2 * d := by rw [hc, one_pow, C_1, one_mul]
  refine ⟨_, _, he, (he.pow 2).of_mul_monic_left (hprod ▸ hg), ?_, hprod⟩
  have hu : IsUnit (C (e.leadingCoeff ^ 2)) :=
    isUnit_C.2 ((IsUnit.of_mul_eq_one _ hlc).pow 2)
  exact (associated_unit_mul_left d _ hu).squarefree_iff.2 hd

/-- **Uniqueness of the square times squarefree factorization of a monic polynomial.** If
`e₁ ^ 2 * d₁ = e₂ ^ 2 * d₂` with `e₁`, `e₂` monic and `d₁`, `d₂` squarefree, then `e₁ = e₂` and
`d₁ = d₂`. -/
theorem Monic.eq_of_sq_mul_eq_sq_mul {e₁ e₂ d₁ d₂ : R[X]} (he₁ : e₁.Monic) (he₂ : e₂.Monic)
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂) (h : e₁ ^ 2 * d₁ = e₂ ^ 2 * d₂) :
    e₁ = e₂ ∧ d₁ = d₂ := by
  have he : e₁ = e₂ :=
    eq_of_monic_of_associated he₁ he₂ (hd₁.associated_of_sq_mul_eq_sq_mul hd₂ he₁.ne_zero h).1
  subst he
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero 2 he₁.ne_zero) h⟩

/-- Sorting the monic polynomials of degree `n` by their square times squarefree factorization
`g = e ^ 2 * d`: the index `j` is the degree of `e`. -/
private noncomputable def sqMulSquarefreeEquiv (n : ℕ) :
    (Σ j : Fin (n / 2 + 1), {e : R[X] // e.Monic ∧ e.natDegree = j} ×
      monicSquarefreePolysOfDegree R (n - 2 * j)) ≃ {g : R[X] // g.Monic ∧ g.natDegree = n} :=
  Equiv.ofBijective
    (fun ⟨⟨j, hj⟩, ⟨e, he, hej⟩, ⟨d, hd, _, hdj⟩⟩ => ⟨e ^ 2 * d, (he.pow 2).mul hd, by
      rw [(he.pow 2).natDegree_mul hd, he.natDegree_pow, hej, hdj]
      omega⟩)
    (by
      constructor
      · rintro ⟨j, ⟨e, he, hej⟩, ⟨d, hd, hds, hdj⟩⟩ ⟨j', ⟨e', he', hej'⟩, ⟨d', hd', hds', hdj'⟩⟩ h
        obtain ⟨rfl, rfl⟩ := he.eq_of_sq_mul_eq_sq_mul he' hds hds' (congrArg Subtype.val h)
        obtain rfl : j = j' := Fin.ext (hej.symm.trans hej')
        rfl
      · rintro ⟨g, hg, hgn⟩
        obtain ⟨e, d, he, hd, hds, rfl⟩ := hg.exists_sq_mul_squarefree
        have hdeg : 2 * e.natDegree + d.natDegree = n := by
          rw [← hgn, (he.pow 2).natDegree_mul hd, he.natDegree_pow, mul_comm]
        exact ⟨⟨⟨e.natDegree, by omega⟩, ⟨e, he, rfl⟩, ⟨d, hd, hds, by simp only; omega⟩⟩, rfl⟩)

end Domain

section FiniteField

variable (K : Type*) [Field K] [Finite K]

/-- **The square times squarefree count.** Over a finite field `K` with `q` elements, with `s_m`
the number of monic squarefree polynomials of degree `m`,
`∑_{0 ≤ j ≤ n/2} q ^ j * s_{n - 2j} = q ^ n`: each monic polynomial of degree `n` is uniquely
`e ^ 2 * d` with `e` monic of some degree `j` and `d` monic squarefree of degree `n - 2j`. -/
theorem sum_pow_mul_ncard_monicSquarefreePolysOfDegree (n : ℕ) :
    ∑ j ∈ Finset.range (n / 2 + 1),
        Nat.card K ^ j * (monicSquarefreePolysOfDegree K (n - 2 * j)).ncard = Nat.card K ^ n := by
  have : ∀ m, Finite {e : K[X] // e.Monic ∧ e.natDegree = m} := fun m =>
    (finite_setOf_monic_natDegree_eq K m).to_subtype
  have : ∀ m, Finite (monicSquarefreePolysOfDegree K m) := fun m =>
    (finite_monicSquarefreePolysOfDegree K m).to_subtype
  have := Nat.card_congr (sqMulSquarefreeEquiv (R := K) n)
  rw [Nat.card_sigma, ← Set.coe_ofPred, Nat.card_coe_set_eq,
    ncard_setOf_monic_natDegree_eq] at this
  rw [← this, ← Fin.sum_univ_eq_sum_range
    (fun j => Nat.card K ^ j * (monicSquarefreePolysOfDegree K (n - 2 * j)).ncard)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.card_prod, ← Set.coe_ofPred, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    ncard_setOf_monic_natDegree_eq]

/-- **Count of squarefree monic polynomials over a finite field.** Over a finite field with `q`
elements there are `q ^ n - q ^ (n - 1)` monic squarefree polynomials of each degree `n ≥ 2`. -/
theorem ncard_monicSquarefreePolysOfDegree {n : ℕ} (hn : 2 ≤ n) :
    (monicSquarefreePolysOfDegree K n).ncard = Nat.card K ^ n - Nat.card K ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := sum_pow_mul_ncard_monicSquarefreePolysOfDegree K (m + 2)
  rw [show (m + 2) / 2 + 1 = m / 2 + 1 + 1 by omega, Finset.sum_range_succ'] at h
  -- The terms with `j ≥ 1` are `q` times the identity in degree `m`.
  have htail : ∑ j ∈ Finset.range (m / 2 + 1),
      Nat.card K ^ (j + 1) * (monicSquarefreePolysOfDegree K (m + 2 - 2 * (j + 1))).ncard =
        Nat.card K ^ (m + 1) := by
    rw [pow_succ', ← sum_pow_mul_ncard_monicSquarefreePolysOfDegree K m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show m + 2 - 2 * (j + 1) = m - 2 * j by omega, pow_succ']
    ring
  rw [htail, pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero] at h
  rw [show m + 2 - 1 = m + 1 by omega]
  omega

end FiniteField

end Polynomial
