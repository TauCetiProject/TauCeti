/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

/-!
# Simply-laced Cartan matrices are positive definite

`TauCeti.IsFiniteType` carries a positive definite symmetrization, but behind an existential over
the symmetrizer, so it says nothing directly about the matrix itself.  For a simply-laced Cartan
matrix the constant-one vector is a symmetrizer, and its symmetrization is the matrix itself read
over `ℚ`, so positive definiteness holds on the nose.  The per-family statements are proved beside
the coordinate models they use, in `TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical` and
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin`; this file collects them into the statement a
consumer indexing over `TauCeti.DynkinType` wants, so that nobody repeats the case split.

The hypothesis is placed on the matrix rather than on the type.  By
`TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff` that is the weaker of the two: besides the
simply-laced types `A`, `D`, `E₆`, `E₇` and `E₈` it admits `B 0`, `B 1`, `C 0` and `C 1`, whose
matrices are the empty matrix and `A 1`.  The statement for a simply-laced type is the corollary
`TauCeti.DynkinType.IsSimplyLaced.posDef_map_intCast_cartanMatrix`.

## Main results

* `TauCeti.DynkinType.posDef_map_intCast_cartanMatrix_of_isSimplyLaced`: a simply-laced standard
  Cartan matrix is positive definite over `ℚ`.
* `TauCeti.DynkinType.IsSimplyLaced.posDef_map_intCast_cartanMatrix`: the Cartan matrix of a
  simply-laced Dynkin type is positive definite over `ℚ`.
-/

public section

namespace TauCeti.DynkinType

/-- The degenerate types `B 0` and `B 1`, whose Cartan matrices are the empty matrix and `A 1`. -/
private theorem posDef_map_intCast_cartanMatrix_B_of_le_one {n : ℕ} (hn : n ≤ 1) :
    ((CartanMatrix.B n).map (Int.cast : ℤ → ℚ)).PosDef := by
  interval_cases n
  · exact Matrix.posDef_of_isEmpty _
  · rw [CartanMatrix.B_one]
    exact posDef_map_intCast_cartanMatrix_A 1

/-- **A simply-laced standard Cartan matrix is positive definite** over `ℚ`.  The types whose
matrix is simply laced are `A`, `D`, `E₆`, `E₇`, `E₈` and the degenerate `B 0`, `B 1`, `C 0`,
`C 1` (`TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff`); the last four have the empty matrix or
`A 1` as their Cartan matrix. -/
theorem posDef_map_intCast_cartanMatrix_of_isSimplyLaced (t : DynkinType)
    (ht : t.cartanMatrix.IsSimplyLaced) : (t.cartanMatrix.map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [isSimplyLaced_cartanMatrix_iff] at ht
  cases t with
  | A n => rw [cartanMatrix_A]; exact posDef_map_intCast_cartanMatrix_A n
  | D n => rw [cartanMatrix_D]; exact posDef_map_intCast_cartanMatrix_D n
  | E6 => rw [cartanMatrix_E6]; exact posDef_map_intCast_cartanMatrix_E6
  | E7 => rw [cartanMatrix_E7]; exact posDef_map_intCast_cartanMatrix_E7
  | E8 => rw [cartanMatrix_E8]; exact posDef_map_intCast_cartanMatrix_E8
  | B n =>
    rw [cartanMatrix_B]
    exact posDef_map_intCast_cartanMatrix_B_of_le_one (by simpa using ht)
  | C n =>
    have h := (posDef_map_intCast_cartanMatrix_B_of_le_one (n := n) (by simpa using ht)).transpose
    rw [← Matrix.transpose_map, CartanMatrix.B_transpose] at h
    rw [cartanMatrix_C]
    exact h
  | F4 => simp at ht
  | G2 => simp at ht

/-- **The Cartan matrix of a simply-laced Dynkin type is positive definite** over `ℚ`.  The
simply-laced types are exactly `A`, `D`, `E₆`, `E₇` and `E₈`. -/
theorem IsSimplyLaced.posDef_map_intCast_cartanMatrix {t : DynkinType} (ht : t.IsSimplyLaced) :
    (t.cartanMatrix.map (Int.cast : ℤ → ℚ)).PosDef :=
  posDef_map_intCast_cartanMatrix_of_isSimplyLaced t
    ((isSimplyLaced_cartanMatrix_iff t).mpr (Or.inl ht))

end TauCeti.DynkinType
