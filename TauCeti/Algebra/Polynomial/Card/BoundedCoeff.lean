/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

import Mathlib.Algebra.Polynomial.OfFn

/-!
# Counting polynomials of bounded degree and bounded coefficients

For a (semi)ring `R` and a finite set `U` of allowed coefficient values, the polynomials of
degree at most `d` all of whose coefficients lie in `U` form a set of cardinality at most
`#U ^ (d + 1)`: a polynomial of degree `≤ d` is determined by its `d + 1` coefficients
`coeff 0, …, coeff d`, each of which ranges over `U`.

Mathlib uses the *finiteness* of this set inline, as the engine of its `bUnion_roots_finite`
(the set of roots of all polynomials of bounded degree with coefficients in a finite set is
finite), where the same injection `f ↦ (f.coeff i)ᵢ` appears, but does not expose that
finiteness; this file supplies it together with the cardinality bound.

When the allowed values are prescribed coefficient by coefficient, for `coeff 0, …, coeff d`
only, the count is exact: the coefficient map is then a bijection onto the box of allowed
coefficient vectors, since every vector is the coefficient vector of a polynomial
(`Polynomial.ofFn`). Mathlib's `Polynomial.ncard_boxPoly` (in `Mathlib.NumberTheory.MahlerMeasure`)
is this exact count for integer polynomials with real interval bounds on each coefficient;
`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_pi` generalises it to any semiring and arbitrary
finite sets of allowed values, and its proof follows the `Polynomial.ofFn` argument of
`Polynomial.ncard_boxPoly`.

The integer specialisation counts the polynomials of degree `≤ d` whose coefficients are bounded
in absolute value by `B`: there are exactly `(2 * B + 1) ^ (d + 1)` of them. This is the
elementary counting input for an explicit count of number fields of bounded discriminant:
Mathlib's `NumberField.finite_of_discr_bdd` already bounds the degree and coefficient height of a
generating polynomial of such a field (`natDegree_le_rankOfDiscrBdd`, `boundOfDiscBdd`).

The cardinality bound counts a number but does not by itself record finiteness (`Set.ncard` is
`0` on an infinite set), so each count is paired with the matching finiteness statement: these are
what turn an injection of some family into one of these boxes into an explicit count of the
family. Mathlib proves this finiteness only inline, inside `Polynomial.bUnion_roots_finite`,
rather than exposing it.

## Main results

* `TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`: at most `#U ^ (d + 1)` polynomials of
  degree `≤ d` with every coefficient in a finite set `U`.
* `TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem`: that family is finite.
* `TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_pi`,
  `TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem_pi`: the coefficient-dependent version,
  exactly `∏ᵢ #(s i)` polynomials of degree `≤ d` whose `i`-th coefficient lies in `s i`.
* `TauCeti.Polynomial.ncard_natDegree_le_abs_intCoeff_le`: exactly `(2 * B + 1) ^ (d + 1)`
  integer polynomials of degree `≤ d` with every coefficient bounded by `B` in absolute value.
* `TauCeti.Polynomial.finite_setOf_natDegree_le_abs_intCoeff_le`: that family is finite.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [Semiring R]

/-- The coefficient map `f ↦ (f.coeff i)ᵢ` into `Fin (d + 1) → R` is injective on the polynomials
of degree at most `d`: such a polynomial is determined by its first `d + 1` coefficients. This is
the shared injection behind both the count and the finiteness of the bounded-coefficient family. -/
private theorem coeff_injOn_natDegree_le (d : ℕ) :
    Set.InjOn (fun (f : R[X]) (i : Fin (d + 1)) => f.coeff i) {f | f.natDegree ≤ d} := by
  intro f hf g hg hfg
  rw [Set.mem_ofPred_eq] at hf hg
  exact (ext_iff_natDegree_le hf hg).2 fun i hi => congrFun hfg ⟨i, Nat.lt_succ_of_le hi⟩

/-- The polynomials of degree at most `d` whose coefficients all lie in a finite set `U` number
at most `#U ^ (d + 1)`: such a polynomial is determined by the `d + 1` coefficients
`coeff 0, …, coeff d`, each ranging over `U`, so the coefficient map injects the set into the
`(d + 1)`-fold product `Fin (d + 1) → U`. -/
theorem ncard_natDegree_le_coeff_mem_le (d : ℕ) (U : Finset R) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U}.ncard ≤ U.card ^ (d + 1) := by
  classical
  set S : Set R[X] := {f | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U}
  -- The coefficient map sends `S` into the finite product `Fin (d + 1) → U`.
  set T : Finset (Fin (d + 1) → R) := Fintype.piFinset (fun _ => U) with hT
  have hcard : (T : Set (Fin (d + 1) → R)).ncard = U.card ^ (d + 1) := by
    rw [Set.ncard_coe_finset, hT, Fintype.card_piFinset_const]
  rw [← hcard]
  refine Set.ncard_le_ncard_of_injOn (fun f i => f.coeff i) ?_ ?_ T.finite_toSet
  · intro f hf
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    exact fun i => hf.2 i
  · exact (coeff_injOn_natDegree_le d).mono fun f hf => hf.1

/-- The polynomials of degree at most `d` whose coefficients all lie in a finite set `U` form a
finite set: the same coefficient map that gives the count above injects them into the finite
product `Fin (d + 1) → U`. Finiteness needs no computable finset data, so `U` is an arbitrary
finite `Set`. (Mathlib proves this only inline, inside `Polynomial.bUnion_roots_finite`.) -/
theorem finite_setOf_natDegree_le_coeff_mem (d : ℕ) {U : Set R} (hU : U.Finite) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U}.Finite := by
  classical
  let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
  refine ((Set.Finite.pi fun _ => hU).subset ?_).of_finite_image
    (?_ : Set.InjOn π _)
  · refine Set.image_subset_iff.2 fun f hf => ?_
    exact fun i _ => hf.2 i
  · exact (coeff_injOn_natDegree_le d).mono fun f hf => hf.1

/-- The polynomials of degree at most `d` whose `i`-th coefficient lies in a finite set `s i`
number exactly `∏ᵢ #(s i)`: the coefficient map is a bijection from them onto
`Fintype.piFinset s`, with inverse `Polynomial.ofFn`. Unlike
`TauCeti.Polynomial.ncard_natDegree_le_coeff_mem_le`, the allowed values may depend on the
coefficient, for instance to fix the leading coefficient of a monic polynomial, and only
`coeff 0, …, coeff d` are constrained.

This generalises Mathlib's `Polynomial.ncard_boxPoly`, the case `R = ℤ` with each `s i` the
integers in a real interval, and the surjectivity half of the proof follows its `ofFn`
argument (`ofFn_coeff_eq_val_of_lt`, `ofFn_natDegree_lt`). -/
theorem ncard_natDegree_le_coeff_mem_pi (d : ℕ) (s : Fin (d + 1) → Finset R) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i : Fin (d + 1), f.coeff i ∈ s i}.ncard =
      ∏ i, (s i).card := by
  classical
  have hinj : Set.InjOn (fun (f : R[X]) (i : Fin (d + 1)) => f.coeff i)
      {f : R[X] | f.natDegree ≤ d ∧ ∀ i : Fin (d + 1), f.coeff i ∈ s i} :=
    (coeff_injOn_natDegree_le d).mono fun f hf => hf.1
  rw [← hinj.ncard_image, ← Fintype.card_piFinset s, ← Set.ncard_coe_finset]
  congr 1
  ext c
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf.2
  · -- Every coefficient vector `c` is that of the polynomial `ofFn (d + 1) c`.
    intro hc
    have hcoeff (i : Fin (d + 1)) : (ofFn (d + 1) c).coeff i = c i :=
      ofFn_coeff_eq_val_of_lt c i.2
    refine ⟨ofFn (d + 1) c, ⟨Nat.le_of_lt_succ (ofFn_natDegree_lt d.succ_pos c), fun i => ?_⟩,
      funext hcoeff⟩
    rw [hcoeff]
    exact hc i

/-- The polynomials of degree at most `d` whose `i`-th coefficient lies in a finite set `s i` form
a finite set: the coefficient map injects them into `Fintype.piFinset s`. -/
theorem finite_setOf_natDegree_le_coeff_mem_pi (d : ℕ) (s : Fin (d + 1) → Finset R) :
    {f : R[X] | f.natDegree ≤ d ∧ ∀ i : Fin (d + 1), f.coeff i ∈ s i}.Finite := by
  classical
  refine Set.Finite.of_finite_image ((Fintype.piFinset s).finite_toSet.subset ?_)
    ((coeff_injOn_natDegree_le d).mono fun f hf => hf.1)
  refine Set.image_subset_iff.2 fun f hf => ?_
  rw [Set.mem_preimage, Finset.mem_coe, Fintype.mem_piFinset]
  exact hf.2

/-- Bounding an integer coefficient by `B` in absolute value is membership in the interval
`[-B, B]`, and for a polynomial of degree at most `d` only `coeff 0, …, coeff d` need checking
(the others vanish), so the two spellings of the bounded-degree, bounded-coefficient family
agree. -/
private theorem setOf_abs_intCoeff_le_eq (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)} =
      {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i : Fin (d + 1), f.coeff i ∈ Finset.Icc (-(B : ℤ)) B} := by
  ext f
  simp only [Set.mem_ofPred_eq, Finset.mem_Icc, ← abs_le]
  refine and_congr_right fun hd => ⟨fun h i => h i, fun h i => ?_⟩
  rcases le_or_gt i d with hi | hi
  · exact h ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt hi), abs_zero]
    exact B.cast_nonneg

/-- The integer polynomials of degree at most `d` all of whose coefficients are bounded by `B` in
absolute value number exactly `(2 * B + 1) ^ (d + 1)`: each of the `d + 1` coefficients
`coeff 0, …, coeff d` ranges independently over the `2 * B + 1` integers in `[-B, B]`. -/
theorem ncard_natDegree_le_abs_intCoeff_le (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)}.ncard = (2 * B + 1) ^ (d + 1) := by
  have hU : (Finset.Icc (-(B : ℤ)) B).card = 2 * B + 1 := by
    rw [Int.card_Icc]; omega
  rw [setOf_abs_intCoeff_le_eq, ncard_natDegree_le_coeff_mem_pi]
  simp [hU]

/-- The integer polynomials of degree at most `d` all of whose coefficients are bounded by `B` in
absolute value form a finite set: their coefficients range over the finite interval `[-B, B]`. -/
theorem finite_setOf_natDegree_le_abs_intCoeff_le (d B : ℕ) :
    {f : ℤ[X] | f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (B : ℤ)}.Finite := by
  rw [setOf_abs_intCoeff_le_eq]
  exact finite_setOf_natDegree_le_coeff_mem_pi d _

end TauCeti.Polynomial
