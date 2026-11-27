/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Algebra.Polynomial.BigOperators
import TauCeti.RingTheory.UniqueFactorizationDomain.SubsetProduct

/-!
# Squarefree monic polynomials are products of distinct monic irreducibles

Over a domain `R` with a normalization monoid, such as `ℤ`, whose polynomial ring has unique
factorization, a squarefree monic polynomial is the product of a finite set of monic irreducible
polynomials. The set is that of its normalized irreducible factors: a normalized divisor of a
monic polynomial is monic, because its leading coefficient is a normalized unit.

A nonzero discriminant gives squarefreeness (`Polynomial.Monic.squarefree_of_discr_ne_zero`).
For monic `f : ℤ[X]` with `disc f ≠ 0` this is the first step in reducing statements about a
reducible `f` to its irreducible factors. The factors are irreducible in `ℤ[X]`, and so, being
monic, also over `ℚ` by Gauss's lemma.

## Main results

* `Polynomial.Monic.monic_of_mem_normalizedFactors`: a normalized irreducible factor of a monic
  polynomial is monic.
* `Polynomial.Monic.prod_toFinset_normalizedFactors_of_squarefree`: a squarefree monic
  polynomial is the product of its distinct normalized irreducible factors.
* `Polynomial.Monic.exists_finset_prod_eq_of_squarefree`: a squarefree monic polynomial is the
  product of a finite set of monic irreducible polynomials.
* `Polynomial.Monic.exists_finset_prod_eq_of_discr_ne_zero`: the same conclusion for a monic
  polynomial with nonzero discriminant.
* `Polynomial.natDegree_eq_sum_mul_count_normalizedFactors`: the degree of a polynomial is
  the sum of the degrees of its normalized factors, counted with multiplicity.
* `TauCeti.Polynomial.sum_finsuppAntidiag_eq_sum_monicsOfDegree`: over a finite field, the monic
  polynomials of degree `n` whose normalized factors lie in a finite set `S` of monic irreducibles
  are the products `∏_{P ∈ S} P ^ (l P / deg P)` for the exponent vectors `l` on `S` with
  `∑ l = n` and `deg P ∣ l P`, so a sum over these polynomials is a sum over such `l`.
-/

public section

open UniqueFactorizationMonoid

namespace Polynomial.Monic

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R[X]] {f : R[X]}

/-- A normalized irreducible factor of a monic polynomial is monic: its leading coefficient is
a normalized unit. -/
theorem monic_of_mem_normalizedFactors (hf : f.Monic) {g : R[X]}
    (hg : g ∈ normalizedFactors f) : g.Monic := by
  have hu : IsUnit g.leadingCoeff := by
    obtain ⟨h, hh⟩ := dvd_of_mem_normalizedFactors hg
    exact IsUnit.of_mul_eq_one h.leadingCoeff
      (by rw [← leadingCoeff_mul, ← hh, hf.leadingCoeff])
  rw [Monic, ← normalize_normalized_factor g hg, leadingCoeff_normalize,
    normalize_eq_one.mpr hu]

/-- A squarefree monic polynomial is the product of its distinct normalized irreducible
factors. -/
theorem prod_toFinset_normalizedFactors_of_squarefree [DecidableEq R[X]] (hf : f.Monic)
    (hsq : Squarefree f) : ∏ g ∈ (normalizedFactors f).toFinset, g = f := by
  have hf0 : f ≠ 0 := hf.ne_zero
  -- Squarefreeness makes the factor multiset duplicate-free, so it is its own `toFinset`.
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    ((squarefree_iff_nodup_normalizedFactors hf0).mp hsq).dedup, Multiset.map_id']
  have hprod := monic_multiset_prod_of_monic (normalizedFactors f) id
    fun _ hg ↦ monic_of_mem_normalizedFactors hf hg
  rw [Multiset.map_id] at hprod
  exact eq_of_monic_of_associated hprod hf (prod_normalizedFactors hf0)

/-- A squarefree monic polynomial is the product of a finite set of monic irreducible
polynomials, namely its normalized irreducible factors. -/
theorem exists_finset_prod_eq_of_squarefree (hf : f.Monic) (hsq : Squarefree f) :
    ∃ s : Finset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f := by
  classical
  refine ⟨(normalizedFactors f).toFinset, fun g hg ↦ ?_,
    hf.prod_toFinset_normalizedFactors_of_squarefree hsq⟩
  rw [Multiset.mem_toFinset] at hg
  exact ⟨monic_of_mem_normalizedFactors hf hg, irreducible_of_normalized_factor g hg⟩

/-- A monic polynomial with nonzero discriminant is the product of a finite set of monic
irreducible polynomials. Over `ℤ` this is the factorization of a monic `f` with `disc f ≠ 0`
into distinct monic irreducible factors. -/
theorem exists_finset_prod_eq_of_discr_ne_zero (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_squarefree (hf.squarefree_of_discr_ne_zero hd)

/-- A polynomial `f` whose normalized factors lie in a finite set `S` has degree
`∑ g ∈ S, deg g · m g`, where `m g` is the number of times that `g` occurs as a normalized
factor. -/
theorem _root_.Polynomial.natDegree_eq_sum_mul_count_normalizedFactors [DecidableEq R[X]]
    (f : R[X]) {S : Finset R[X]} (hS : (normalizedFactors f).toFinset ⊆ S) :
    f.natDegree = ∑ g ∈ S, g.natDegree * (normalizedFactors f).count g := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  conv_lhs => rw [← natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (prod_normalizedFactors hf0)),
    natDegree_multiset_prod _ (zero_notMem_normalizedFactors f), Finset.sum_multiset_map_count]
  refine (Finset.sum_subset hS fun g _ hg ↦ ?_).trans (Finset.sum_congr rfl fun g _ ↦ ?_)
  · rw [Multiset.count_eq_zero.2 fun h ↦ hg (Multiset.mem_toFinset.2 h), zero_smul]
  · rw [smul_eq_mul, mul_comm]

/-- The integral case: a monic integral polynomial with nonzero discriminant is the product of
distinct monic irreducible integral polynomials. -/
example {f : ℤ[X]} (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset ℤ[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_discr_ne_zero hd

end Polynomial.Monic

namespace TauCeti.Polynomial

open _root_.Polynomial Finset

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]

/-- **Factorization over a finite set of monic irreducibles.** Let `S` be a finite set of monic
irreducible polynomials over a finite field. Then `l ↦ ∏_{P ∈ S} P ^ (l P / deg P)` is a bijection
from the `l : F[X] →₀ ℕ` on `S` with `∑_{P ∈ S} l P = n` and `deg P ∣ l P` to the monic
polynomials of degree `n` whose normalized factors lie in `S`. So a sum of `w` over these
polynomials is a sum over such `l`. -/
theorem sum_finsuppAntidiag_eq_sum_monicsOfDegree {M : Type*} [AddCommMonoid M]
    {S : Finset F[X]} (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) (n : ℕ) (w : F[X] → M) :
    ∑ l ∈ (S.finsuppAntidiag n).filter (fun l ↦ ∀ P ∈ S, P.natDegree ∣ l P),
        w (∏ P ∈ S, P ^ (l P / P.natDegree)) =
      ∑ g ∈ (monicsOfDegree F n).filter (fun g ↦ (normalizedFactors g).toFinset ⊆ S), w g := by
  have hdeg : ∀ P ∈ S, 0 < P.natDegree := fun P hP ↦ (hS P hP).2.natDegree_pos
  have hnS : ∀ P ∈ S, normalize P = P ∧ Irreducible P := fun P hP ↦
    ⟨(hS P hP).1.normalize_eq_self, (hS P hP).2⟩
  -- The inverse sends `g` to the vector of `deg P` times the multiplicity of `P` in `g`.
  refine sum_nbij' (fun l ↦ ∏ P ∈ S, P ^ (l P / P.natDegree))
    (fun g ↦ Finsupp.onFinset S
      (fun P ↦ if P ∈ S then P.natDegree * (normalizedFactors g).count P else 0)
      (fun P hP ↦ by by_contra h; simp [h] at hP)) ?_ ?_ ?_ ?_ fun _ _ ↦ rfl
  · intro l hl
    simp only [mem_filter, mem_finsuppAntidiag] at hl
    simp only [mem_filter, mem_monicsOfDegree]
    refine ⟨⟨monic_prod_of_monic _ _ fun P hP ↦ (hS P hP).1.pow _, ?_⟩, ?_⟩
    · rw [natDegree_prod_of_monic _ _ fun P hP ↦ (hS P hP).1.pow _, ← hl.1.1]
      refine sum_congr rfl fun P hP ↦ ?_
      rw [(hS P hP).1.natDegree_pow, Nat.div_mul_cancel (hl.2 P hP)]
    · rw [TauCeti.normalizedFactors_finset_prod_pow hnS]
      intro Q hQ
      obtain ⟨R, hR, hQR⟩ := Multiset.mem_sum.1 (Multiset.mem_toFinset.1 hQ)
      rw [Multiset.mem_nsmul] at hQR
      rwa [Multiset.mem_singleton.1 hQR.2]
  · intro g hg
    simp only [mem_filter, mem_monicsOfDegree] at hg
    obtain ⟨⟨-, hgn⟩, hgS⟩ := hg
    simp only [mem_filter, mem_finsuppAntidiag, Finsupp.onFinset_apply]
    refine ⟨⟨?_, Finsupp.support_onFinset_subset⟩, fun P hP ↦ by simp [hP]⟩
    rw [← hgn, g.natDegree_eq_sum_mul_count_normalizedFactors hgS]
    exact sum_congr rfl fun P hP ↦ by simp [hP]
  · intro l hl
    simp only [mem_filter, mem_finsuppAntidiag] at hl
    ext P
    simp only [Finsupp.onFinset_apply]
    split_ifs with hP
    · rw [TauCeti.count_normalizedFactors_finset_prod_pow hnS _ hP,
        Nat.mul_div_cancel' (hl.2 P hP)]
    · exact (Finsupp.notMem_support_iff.1 fun h ↦ hP (hl.1.2 h)).symm
  · intro g hg
    simp only [mem_filter, mem_monicsOfDegree] at hg
    obtain ⟨⟨hgm, -⟩, hgS⟩ := hg
    simp only [Finsupp.onFinset_apply]
    refine (prod_congr rfl fun P hP ↦ ?_).trans
      (TauCeti.finset_prod_pow_count_normalizedFactors hgm.ne_zero hgm.normalize_eq_self hgS)
    simp only [hP, ↓reduceIte, Nat.mul_div_cancel_left _ (hdeg P hP)]

end TauCeti.Polynomial
