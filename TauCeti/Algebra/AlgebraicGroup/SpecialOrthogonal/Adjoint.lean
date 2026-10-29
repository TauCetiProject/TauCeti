/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Center
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Adjoint.Basic

/-!
# Odd-dimensional special orthogonal groups are adjoint

Over a field of characteristic different from two, `SOₙ` is semisimple for `n ≥ 3`.
In odd dimension its scheme-theoretic center is trivial, making it an adjoint semisimple group.
This combines the semisimplicity theorem in `SpecialOrthogonal.Semisimple` with the calculation
of universal central points in `SpecialOrthogonal.Center`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 21 and 24.
-/

public section

namespace TauCeti.SpecialOrthogonal

universe u

/-- Odd-dimensional `SOₙ`, for `n ≥ 3`, is adjoint semisimple over every field of
characteristic different from two. -/
theorem adjointSemisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_of_odd
    (k : Type u) [Field k] [NeZero (2 : k)] (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    adjointSemisimpleCommHopfAlgProperty k
      ⟨finiteTypeCoordinateHopfAlgebra k n,
        semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n (by omega)⟩ := by
  apply (adjointSemisimpleCommHopfAlgProperty_iff _).mpr
  -- Direct rewriting leaves the augmentation's CommRing instance tied to the old object,
  -- producing an ill-typed motive. Abstracting the bundled Hopf algebra transports it too.
  exact (congrArg (fun H : _root_.CommHopfAlgCat k ↦
    CommHopfAlgCat.centerDefiningIdeal H = HopfIdeal.augmentation k H)
      (finiteTypeCoordinateHopfAlgebra_obj k n)).mpr
        (centerDefiningIdeal_eq_augmentation_of_odd k n hn hodd)

end TauCeti.SpecialOrthogonal
