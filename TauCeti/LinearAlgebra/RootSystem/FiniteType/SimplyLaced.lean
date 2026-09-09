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
the symmetrizer, so it says nothing directly about the matrix itself.  For a simply-laced type the
symmetrizer is trivial and the matrix is its own symmetrization, so positive definiteness holds on
the nose.  The per-family statements are proved beside the coordinate models they use, in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical` and
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin`; this file collects them into the statement a
consumer indexing over `TauCeti.DynkinType` wants, so that nobody repeats the case split.

## Main results

* `TauCeti.DynkinType.posDef_cartanMatrix_of_isSimplyLaced`: the Cartan matrix of a simply-laced
  Dynkin type is positive definite over `ℚ`.
-/

public section

namespace TauCeti.DynkinType

/-- **The Cartan matrix of a simply-laced Dynkin type is positive definite** over `ℚ`.  The
simply-laced types are exactly `A`, `D`, `E₆`, `E₇` and `E₈`; the hypothesis rules out the rest. -/
theorem posDef_cartanMatrix_of_isSimplyLaced (t : DynkinType) (ht : t.IsSimplyLaced) :
    (t.cartanMatrix.map (Int.cast : ℤ → ℚ)).PosDef := by
  cases t with
  | A n => rw [cartanMatrix_A]; exact posDef_cartanMatrix_A n
  | D n => rw [cartanMatrix_D]; exact posDef_cartanMatrix_D n
  | E6 => rw [cartanMatrix_E6]; exact posDef_cartanMatrix_E6
  | E7 => rw [cartanMatrix_E7]; exact posDef_cartanMatrix_E7
  | E8 => rw [cartanMatrix_E8]; exact posDef_cartanMatrix_E8
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

end TauCeti.DynkinType
