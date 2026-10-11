/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Injectivity of projective conjugation coordinates

The coordinate morphism of `GLₙ → PGLₙ` is injective over every commutative base ring.
In particular, it detects nilpotent elements, which field-valued points alone cannot do.

Over a field, `O(PGLₙ)` is geometrically reduced. This allows algebraically closed points
to detect coordinate identities when studying the homomorphism `SLₙ → PGLₙ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 5.49.
* M.-A. Knus, M. Ojanguren, *Théorie de la descente et algèbres d'Azumaya*, Chapter IV.
-/

public section

open WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u

variable (n : ℕ)

section Ring

variable (R : Type u) [CommRing R]

/-- The coordinate morphism of `GLₙ → PGLₙ` is injective, including over nonreduced bases
and in rank zero. -/
theorem conjugationMap_injective : Function.Injective (conjugationMap n R).hom := by
  intro x y hxy
  have hx : (conjugationMap n R).hom (x - y) = 0 := by simp [hxy]
  apply sub_eq_zero.mp
  apply eq_zero_of_localization (x - y)
  intro m hm
  let A := Localization.AtPrime m
  let q : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra n R)
      (CommAlgCat.of R A) := toConv (IsScalarTower.toAlgHom R (coordinateHopfAlgebra n R) A)
  obtain ⟨g, hg⟩ := mapPointsFunctor_conjugationMap_app_surjective n A q
  have h : g.ofConv ((conjugationMap n R).hom (x - y)) = q.ofConv (x - y) :=
    (CommHopfAlgCat.mapPointsFunctor_app_apply_apply
      (conjugationMap n R) (CommAlgCat.of R A) g (x - y)).symm.trans
        (congrArg (fun p ↦ p.ofConv (x - y)) hg)
  simpa only [q, WithConv.ofConv_toConv, IsScalarTower.toAlgHom_apply, hx, map_zero]
    using h.symm

end Ring

variable (k : Type u) [Field k]

/-- The coordinate algebra of `PGLₙ` is geometrically reduced over every field. -/
instance instIsGeometricallyReducedCoordinateHopfAlgebra :
    Algebra.IsGeometricallyReduced k (coordinateHopfAlgebra n k) := by
  let _ := isGeometricallyReduced_of_smooth k (GeneralLinear.coordinateHopfAlgebra k n)
  exact Algebra.IsGeometricallyReduced.of_injective (conjugationMap n k).hom.toAlgHom
    (conjugationMap_injective n k)

end TauCeti.ProjectiveGeneralLinear
