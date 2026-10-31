/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.GelfandInvariant.HighestWeight
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
import TauCeti.Algebra.Lie.GeneralLinear.GelfandInvariant.Separation

/-!
# Gelfand-Tsetlin patterns are separated by their Gelfand-invariant eigenvalues

Along the chain of upper-left corners `gl 1 ⊆ gl 2 ⊆ ⋯ ⊆ gl n`, the Gelfand-Tsetlin vector of a
pattern `P` lies, for each `j ≤ n`, in an irreducible `gl j`-submodule whose highest weight is the
row `(P 0 j, …, P (j - 1) j)` of `P`. The Gelfand invariants of `gl j` are central in `U(gl j)`, so
they act on that vector by their highest-weight eigenvalues `TauCeti.gelfandEigenvalue` at this row.
This file proves that the resulting family of scalars determines the pattern: two patterns whose
rows have the same Gelfand-invariant eigenvalues in degrees `1, …, j` at every level `j` are equal.
This is the combinatorial content of the statement that the joint eigencharacter of the
Gelfand-Tsetlin generators separates the Gelfand-Tsetlin basis. Each row is a weakly decreasing
integer sequence, so the statement follows from the separation of dominant weights
`TauCeti.eq_of_forall_gelfandEigenvalue_eq`, applied level by level.

## Main results

* `TauCeti.GTPattern.eq_of_forall_gelfandEigenvalue_eq`: the Gelfand-invariant eigenvalues of the
  rows of a Gelfand-Tsetlin pattern determine the pattern.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Yangians and Classical Lie Algebras* (2007), Chapter 7.
-/

public section

namespace TauCeti.GTPattern

variable {n : ℕ}

/-- **The Gelfand-Tsetlin eigencharacter separates patterns.** Over a commutative ring of
characteristic zero, two Gelfand-Tsetlin patterns are equal as soon as, at every level `j ≤ n`,
their rows of length `j` have the same highest-weight eigenvalues of the Gelfand invariants of
`gl j` in degrees `1, …, j`. -/
theorem eq_of_forall_gelfandEigenvalue_eq {K : Type*} [CommRing K] [CharZero K]
    {P Q : GTPattern n}
    (h : ∀ j ≤ n, ∀ r ∈ Finset.Icc 1 j,
      gelfandEigenvalue (fun i : Fin j => (P i j : K)) r =
        gelfandEigenvalue (fun i : Fin j => (Q i j : K)) r) :
    P = Q := by
  refine ext fun i j => ?_
  by_cases hij : i < j ∧ j ≤ n
  · have hrow := TauCeti.eq_of_forall_gelfandEigenvalue_eq (K := K)
      (μ := fun i : Fin j => P i j) (μ' := fun i : Fin j => Q i j)
      (fun a b hab => P.entry_anti hij.2 hab b.2) (fun a b hab => Q.entry_anti hij.2 hab b.2)
      (by simpa using h j hij.2)
    exact congrFun hrow ⟨i, hij.1⟩
  · rw [P.entry_eq_zero (by omega), Q.entry_eq_zero (by omega)]

end TauCeti.GTPattern
