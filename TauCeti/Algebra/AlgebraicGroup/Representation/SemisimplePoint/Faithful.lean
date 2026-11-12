/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality

/-!
# Detecting semisimple points in a faithful representation

Over a perfect value field, semisimplicity can be tested in one faithful finite-dimensional
representation. The proof uses the Jordan decomposition and injectivity of the faithful point
action, as in `TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Faithful`.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open LinearMap WithConv

namespace TauCeti.HopfAlgebra

universe u

variable {k H K : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

/-- Over a perfect value field, a faithful finite-dimensional representation detects semisimple
points. -/
theorem isSemisimplePoint_iff_isSemisimple_pointsAction_of_isFaithful
    (M : FGComoduleCat.{u, u, u} k H)
    (hM : Comodule.IsFaithful (k := k) (H := H) (V := M))
    (g : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint g ↔
      GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) := by
  constructor
  · exact fun hg ↦ (isSemisimplePoint_def g).mp hg M
  · intro hg
    rw [isSemisimplePoint_iff_unipotentPart_eq_one]
    apply Comodule.eq_one_of_ofLinearEquiv_pointsAction_eq_one_of_isFaithful hM
    rw [Point.ofLinearEquiv_pointsAction_unipotentPart,
      GeneralLinearGroup.unipotentPart_eq_one_of_isSemisimple hg]

end TauCeti.HopfAlgebra
