/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.RingTheory.Polynomial.RationalRoot

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
* `TauCeti.irreducible_map_rat_of_natDegree_eq_three`: a monic integral cubic with no integral
  root is irreducible over `ℚ`.
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

namespace TauCeti

open Polynomial

/-- A monic integral cubic without an integral root is irreducible over `ℚ`: a rational root of
a monic integral polynomial is integral. -/
theorem irreducible_map_rat_of_natDegree_eq_three {g : ℤ[X]} (hg : g.Monic)
    (hdeg : g.natDegree = 3) (h : ∀ m : ℤ, g.eval m ≠ 0) :
    Irreducible (g.map (Int.castRingHom ℚ)) := by
  refine irreducible_of_degree_le_three_of_not_isRoot
    (by rw [natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]; decide)
    fun x hx => ?_
  have hx' : aeval x g = 0 := by
    rwa [aeval_def, algebraMap_int_eq, ← eval_map]
  obtain ⟨m, rfl⟩ := isInteger_of_is_root_of_monic hg hx'
  rw [aeval_algebraMap_apply, coe_aeval_eq_eval,
    map_eq_zero_iff _ (algebraMap ℤ ℚ).injective_int] at hx'
  exact h m hx'

end TauCeti

end
