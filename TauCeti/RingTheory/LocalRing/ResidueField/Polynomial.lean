/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial evaluation over local rings with large residue field

Over a local ring `R`, any finite family of polynomials in `R[X]` with nonzero reductions modulo
the maximal ideal whose total degree is strictly less than the cardinality of the residue field
simultaneously evaluates to units at some element of `R`. In particular, this holds for every
finite family when the residue field is infinite.

## Main results

* `Polynomial.exists_forall_isUnit_eval_of_sum_map_residue_natDegree_lt`: simultaneous unit
  evaluation when the sum of the degrees of the reductions is strictly less than
  `ENat.card (ResidueField R)`.
* `Polynomial.exists_forall_isUnit_eval`: the infinite-residue-field corollary.
-/

public section

namespace Polynomial

/-- Over a local ring `R`, finitely many polynomials with nonzero reductions modulo the maximal
ideal whose total degree is strictly less than `ENat.card (ResidueField R)` simultaneously
evaluate to units at some ring element. -/
theorem exists_forall_isUnit_eval_of_sum_map_residue_natDegree_lt {R ι : Type*}
    [CommRing R] [IsLocalRing R]
    (s : Finset ι) (f : ι → R[X])
    (hf : ∀ j ∈ s, (f j).map (IsLocalRing.residue R) ≠ 0)
    (hcard : ((∑ j ∈ s, ((f j).map (IsLocalRing.residue R)).natDegree : ℕ) : ENat) <
      ENat.card (IsLocalRing.ResidueField R)) :
    ∃ u : R, ∀ j ∈ s, IsUnit ((f j).eval u) := by
  let P : (IsLocalRing.ResidueField R)[X] := ∏ j ∈ s, (f j).map (IsLocalRing.residue R)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr hf
  have hdeg : (P.natDegree : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField R) :=
    Cardinal.natCast_lt_toENat.mp ((Nat.cast_le.mpr (natDegree_prod_le s _)).trans_lt hcard)
  obtain ⟨y, hy⟩ := exists_eval_ne_zero_of_natDegree_lt_card P hP hdeg
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective y
  rw [eval_prod, Finset.prod_ne_zero_iff] at hy
  exact ⟨u, fun j hj ↦ by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval_map_apply]
    exact hy j hj⟩

/-- Over a local ring with infinite residue field, finitely many polynomials with nonzero
reduction modulo the maximal ideal simultaneously evaluate to units at some ring element. -/
theorem exists_forall_isUnit_eval {R ι : Type*} [CommRing R] [IsLocalRing R]
    [Infinite (IsLocalRing.ResidueField R)] (s : Finset ι) (f : ι → R[X])
    (hf : ∀ j ∈ s, (f j).map (IsLocalRing.residue R) ≠ 0) :
    ∃ u : R, ∀ j ∈ s, IsUnit ((f j).eval u) :=
  exists_forall_isUnit_eval_of_sum_map_residue_natDegree_lt s f hf
    (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)

end Polynomial
