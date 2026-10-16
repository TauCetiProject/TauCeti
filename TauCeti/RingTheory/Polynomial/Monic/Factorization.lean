/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Algebra.Polynomial.BigOperators

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

* `Polynomial.Monic.exists_finset_prod_eq_of_squarefree`: a squarefree monic polynomial is the
  product of a finite set of monic irreducible polynomials.
* `Polynomial.Monic.exists_finset_prod_eq_of_discr_ne_zero`: the same conclusion for a monic
  polynomial with nonzero discriminant.
-/

public section

open UniqueFactorizationMonoid

namespace Polynomial.Monic

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R[X]] {f : R[X]}

/-- A squarefree monic polynomial is the product of a finite set of monic irreducible
polynomials, namely its normalized irreducible factors. -/
theorem exists_finset_prod_eq_of_squarefree (hf : f.Monic) (hsq : Squarefree f) :
    ∃ s : Finset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  -- A normalized factor divides `f`, so its leading coefficient is a normalized unit, hence `1`.
  have hmon : ∀ g ∈ normalizedFactors f, g.Monic := by
    intro g hg
    have hu : IsUnit g.leadingCoeff := by
      obtain ⟨h, hh⟩ := dvd_of_mem_normalizedFactors hg
      exact IsUnit.of_mul_eq_one h.leadingCoeff
        (by rw [← leadingCoeff_mul, ← hh, hf.leadingCoeff])
    rw [Monic, ← normalize_normalized_factor g hg, leadingCoeff_normalize,
      normalize_eq_one.mpr hu]
  refine ⟨(normalizedFactors f).toFinset, fun g hg ↦ ?_, ?_⟩
  · rw [Multiset.mem_toFinset] at hg
    exact ⟨hmon g hg, irreducible_of_normalized_factor g hg⟩
  · -- Squarefreeness makes the factor multiset duplicate-free, so it is its own `toFinset`.
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      ((squarefree_iff_nodup_normalizedFactors hf0).mp hsq).dedup, Multiset.map_id']
    have hprod := monic_multiset_prod_of_monic (normalizedFactors f) id hmon
    rw [Multiset.map_id] at hprod
    exact eq_of_monic_of_associated hprod hf (prod_normalizedFactors hf0)

/-- A monic polynomial with nonzero discriminant is the product of a finite set of monic
irreducible polynomials. Over `ℤ` this is the factorization of a monic `f` with `disc f ≠ 0`
into distinct monic irreducible factors. -/
theorem exists_finset_prod_eq_of_discr_ne_zero (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_squarefree (hf.squarefree_of_discr_ne_zero hd)

/-- The integral case: a monic integral polynomial with nonzero discriminant is the product of
distinct monic irreducible integral polynomials. -/
example {f : ℤ[X]} (hf : f.Monic) (hd : f.discr ≠ 0) :
    ∃ s : Finset ℤ[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ ∏ g ∈ s, g = f :=
  hf.exists_finset_prod_eq_of_discr_ne_zero hd

end Polynomial.Monic
