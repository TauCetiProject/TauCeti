/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Parabolic
public import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Stabilizer cardinalities of parabolic conjugacy classes

A parabolic integral matrix is nonscalar with discriminant zero. Its centralizer in `SL(2, ℤ)`
is infinite. Consequently, the stabilizer cardinality attached to its conjugacy class in a
fixed trace-and-determinant fibre is zero in `ℕ`, since `Nat.card` of an infinite type is zero.
This records a cardinality convention, not a computation of the parabolic contribution to
the trace formula or of the Popa–Zagier conjugacy-class weight.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1 and §4.
-/

public section

open Matrix MulAction
open scoped MatrixGroups

namespace TauCeti

/-- A parabolic conjugacy class in a fixed trace-and-determinant fibre has infinite
stabilizer, hence stabilizer cardinality zero in `ℕ`. -/
theorem cardStabilizerOnOrbit_eq_zero_of_isParabolic {t n : ℤ}
    (X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n))
    (hX : (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ).IsParabolic) :
    cardStabilizerOnOrbit X = 0 := by
  have hcard := card_stabilizer_congr (MulEquiv.refl (ConjAct SL(2, ℤ)))
    (f := fun M : traceDetFiber (Fin 2) t n ↦ (M : Matrix (Fin 2) (Fin 2) ℤ))
    X.out (fun _ ↦ rfl) (fun _ h ↦ Subtype.ext h)
  have : Infinite (stabilizer (ConjAct SL(2, ℤ))
      (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ)) := infinite_stabilizer_of_isParabolic _ hX
  have hzero : Nat.card (stabilizer (ConjAct SL(2, ℤ)) X.out) = 0 :=
    hcard.symm.trans Nat.card_eq_zero_of_infinite
  simpa only [← cardStabilizerOnOrbit_mk, Quotient.out_eq] using hzero

end TauCeti
