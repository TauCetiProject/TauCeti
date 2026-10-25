/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.Algebra.Polynomial.OddDegreeFactor

/-!
# Roots of odd-degree polynomials below an algebraically closed extension

If a field `R` has an algebraically closed extension `K` of degree a power of two, then every
polynomial of odd degree over `R` has a root in `R`: it has an irreducible factor of odd degree,
and that degree divides `[K : R]`, so it is one.

## Main results

* `Polynomial.exists_isRoot_of_odd_natDegree_of_finrank_eq_two_pow`: an odd-degree polynomial
  over `R` has a root in `R` when `R` has an algebraically closed extension of degree `2 ^ k`.

## References

* The degree bound on irreducible factors is adapted from the proof of
  `isRealClosed_of_isAlgClosed_adjoin` by Kiran S. Kedlaya in Mathlib pull request 41911
  (the Artin–Schreier theorem).
-/

public section

namespace Polynomial

open Module

variable {R K : Type*} [Field R] [Field K] [Algebra R K] [IsAlgClosed K]

/-- Over a field with an algebraically closed extension of degree `2 ^ k`, every polynomial of
odd degree has a root. -/
theorem exists_isRoot_of_odd_natDegree_of_finrank_eq_two_pow (p : R[X]) (hp : Odd p.natDegree)
    {k : ℕ} (hK : finrank R K = 2 ^ k) : ∃ x, p.IsRoot x := by
  obtain ⟨q, hq, hqodd, hqp⟩ := exists_irreducible_factor_of_odd_natDegree p hp
  have hdvd : q.natDegree ∣ 2 ^ k :=
    hK ▸ Irreducible.natDegree_dvd_finrank hq (IsAlgClosed.splits _)
  have hq1 : q.natDegree = 1 :=
    ((Nat.coprime_two_right.mpr hqodd).pow_right k).eq_one_of_dvd hdvd
  obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one
    ((degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hq1)
  exact ⟨x, hx.dvd hqp⟩

end Polynomial
