/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card

/-!
# Counting polynomials of bounded degree and bounded coefficients

For a (semi)ring `R` and a finite set `U` of allowed coefficient values, the polynomials of
degree at most `d` all of whose coefficients lie in `U` form a set of cardinality at most
`#U ^ (d + 1)`: a polynomial of degree `≤ d` is determined by its `d + 1` coefficients
`coeff 0, …, coeff d`, each of which ranges over `U`.

Mathlib already records the *finiteness* of this set, as the engine of its `bUnion_roots_finite`
(the set of roots of all polynomials of bounded degree with coefficients in a finite set is
finite), where the same injection `f ↦ (f.coeff i)ᵢ` appears; the contribution here is the
explicit cardinality bound rather than mere finiteness.

The integer specialisation counts the polynomials of degree `≤ d` whose coefficients are bounded
in absolute value by `B`: there are at most `(2 * B + 1) ^ (d + 1)` of them. This is the
elementary counting input named by the Layer-2 ("effective Hermite–Minkowski") target of the
effective-bounds roadmap: Mathlib's `NumberField.finite_of_discr_bdd` already bounds the degree
and coefficient height of a generating polynomial of a number field of bounded discriminant
(`natDegree_le_rankOfDiscrBdd`, `boundOfDiscBdd`), so an explicit *count* of number fields of
bounded discriminant needs an explicit count of the polynomials of bounded degree and height.

## Main results

* `TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`: at most `#U ^ (d + 1)` polynomials of
  degree `≤ d` with every coefficient in a finite set `U`.
* `TauCeti.Polynomial.ncard_natDegree_le_abs_intCoeff_le`: at most `(2 * B + 1) ^ (d + 1)`
  integer polynomials of degree `≤ d` with every coefficient bounded by `B` in absolute value.
-/

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [Semiring R]

/-- The polynomials of degree at most `d` whose coefficients all lie in a finite set `U` number
at most `#U ^ (d + 1)`: such a polynomial is determined by the `d + 1` coefficients
`coeff 0, …, coeff d`, each ranging over `U`, so the coefficient map injects the set into the
`(d + 1)`-fold product `Fin (d + 1) → U`. -/
theorem ncard_natDegree_le_coeff_mem_le (d : ℕ) (U : Finset R) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U}.ncard ≤ U.card ^ (d + 1) := by
  classical
  set S : Set R[X] := {f | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U} with hS
  -- The coefficient map sends `S` into the finite product `Fin (d + 1) → U`.
  set T : Finset (Fin (d + 1) → R) := Fintype.piFinset (fun _ => U) with hT
  have hcard : (T : Set (Fin (d + 1) → R)).ncard = U.card ^ (d + 1) := by
    rw [Set.ncard_coe_finset, hT, Fintype.card_piFinset_const]
  rw [← hcard]
  refine Set.ncard_le_ncard_of_injOn (fun f i => f.coeff i) ?_ ?_ T.finite_toSet
  · intro f hf
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    exact fun i => hf.2 i
  · intro f hf g hg hfg
    rw [hS, Set.mem_setOf_eq] at hf hg
    rw [ext_iff_natDegree_le hf.1 hg.1]
    exact fun i hi => congrFun hfg ⟨i, Nat.lt_succ_of_le hi⟩

/-- The integer polynomials of degree at most `d` all of whose coefficients are bounded by `B` in
absolute value number at most `(2 * B + 1) ^ (d + 1)`: each of the `d + 1` coefficients
`coeff 0, …, coeff d` ranges over the `2 * B + 1` integers in `[-B, B]`. -/
theorem ncard_natDegree_le_abs_intCoeff_le (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)}.ncard ≤ (2 * B + 1) ^ (d + 1) := by
  have hU : (Finset.Icc (-(B : ℤ)) B).card = 2 * B + 1 := by
    rw [Int.card_Icc]; omega
  have hset : {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)} =
      {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Finset.Icc (-(B : ℤ)) B} := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.mem_Icc, abs_le]
  rw [hset]
  calc {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Finset.Icc (-(B : ℤ)) B}.ncard
      ≤ (Finset.Icc (-(B : ℤ)) B).card ^ (d + 1) :=
        ncard_natDegree_le_coeff_mem_le d _
    _ = (2 * B + 1) ^ (d + 1) := by rw [hU]

end TauCeti.Polynomial
