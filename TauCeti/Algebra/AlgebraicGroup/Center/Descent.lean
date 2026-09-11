/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Descent of finiteness of the center

A field extension preserves and reflects finiteness of the scheme-theoretic center of an
affine group. Thus finiteness may be proved over an algebraic closure and then descended to
the original field, as in the finite-center theorem for semisimple groups. No smoothness,
connectedness, or finite-type assumption on the ambient group is needed for this descent.

The coordinate comparison is `CommHopfAlgCat.centerCoordinateBaseChangeIso`. Finiteness of
its tensor-product side descends by Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A field extension preserves and reflects finiteness of the full scheme-theoretic center,
including any non-reduced structure. -/
@[simp]
theorem moduleFinite_centerCoordinate_baseChange_iff
    (H : _root_.CommHopfAlgCat.{v} k) :
    Module.Finite K (centerCoordinateHopfAlgebra (baseChange (K := K) H)) ↔
      Module.Finite k (centerCoordinateHopfAlgebra H) := by
  let e := centerCoordinateBaseChangeIso (K := K) H
  constructor
  · intro h
    let _ := h
    let _ : Module.Finite K (baseChange (K := K) (centerCoordinateHopfAlgebra H)) :=
      Module.Finite.of_surjective e.hom.hom.toAlgHom.toLinearMap
        (ConcreteCategory.bijective_of_isIso e.hom).surjective
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K
  · intro h
    let _ := h
    exact Module.Finite.of_surjective e.inv.hom.toAlgHom.toLinearMap
      (ConcreteCategory.bijective_of_isIso e.inv).surjective

end TauCeti.CommHopfAlgCat
