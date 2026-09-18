/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Monic irreducible polynomials of a fixed degree

The monic irreducible polynomials of a given degree over a semiring `R` form a set depending
only on `R` and the degree. When `R` is finite that set is finite, because a monic polynomial of
degree `d` is determined by its lower coefficients: `Polynomial.monicEquivDegreeLT` matches such
polynomials with `Polynomial.degreeLT`, which `Polynomial.degreeLTEquiv` identifies with the
finite function space `Fin d → R`.

## Main definitions

* `Polynomial.monicIrreduciblesOfDegree`: the monic irreducible polynomials of degree `d`.

## Main results

* `Polynomial.mem_monicIrreduciblesOfDegree_iff`: the defining membership condition.
* `Polynomial.finite_monicIrreduciblesOfDegree`: over a finite coefficient ring there are
  finitely many.
-/

public section

namespace Polynomial

variable (R : Type*) [Semiring R]

/-- The monic irreducible polynomials of degree `d` over `R`.

The set depends only on `R` and `d`, which is what lets a counting argument compare it with an
unrelated family without assuming a bound on either. -/
def monicIrreduciblesOfDegree (d : ℕ) : Set R[X] :=
  {g | g.Monic ∧ Irreducible g ∧ g.natDegree = d}

/-- Membership in `monicIrreduciblesOfDegree` is the conjunction defining it. -/
@[simp]
theorem mem_monicIrreduciblesOfDegree_iff {d : ℕ} {g : R[X]} :
    g ∈ monicIrreduciblesOfDegree R d ↔ g.Monic ∧ Irreducible g ∧ g.natDegree = d :=
  Iff.rfl

/-- **Over a finite coefficient ring there are finitely many monic irreducibles of each
degree.** They sit inside the monic polynomials of that degree, which are parametrised by their
lower coefficients. -/
theorem finite_monicIrreduciblesOfDegree [Nontrivial R] [Finite R] (d : ℕ) :
    (monicIrreduciblesOfDegree R d).Finite := by
  have hdeg : Finite (Polynomial.degreeLT R d) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv R d).toEquiv.symm
  have hmon : {g : R[X] | g.Monic ∧ g.natDegree = d}.Finite := by
    rw [← Set.finite_coe_iff]
    exact Finite.of_equiv _ (Polynomial.monicEquivDegreeLT (R := R) d).symm
  exact hmon.subset fun g hg => ⟨hg.1, hg.2.2⟩

end Polynomial

end
