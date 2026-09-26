/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.CartierDuality.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The center of a semisimple group is finite locally free

The scheme-theoretic center of a semisimple affine group over a field is a finite locally free
commutative group scheme. In Hopf coordinates, its coordinate algebra is finite by the finiteness
theorem for semisimple centers, projective because it is a vector space over a field, and
cocommutative because the center is a central subgroup. It is also faithfully flat: the counit
shows that the coordinate algebra is nonzero, and every nonzero vector space is faithfully flat.

This file packages those three facts in the category used by Cartier duality. It also records that
the structure morphism from the center to the trivial group is a central isogeny. These are the
finite-flat inputs needed when constructing the quotient of a semisimple group by its center.

## Main declarations

* `TauCeti.semisimpleCommHopfAlgProperty.centerFiniteLocallyFree`: the center, packaged as a
  finite locally free bicommutative Hopf algebra.
* `TauCeti.semisimpleCommHopfAlgProperty.isCentralIsogeny_centerStructureMorphism`: the center's
  structure morphism to the trivial group is a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.21 and §21.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 2 and 6.
-/

public section

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The center of a semisimple affine group, packaged as a finite locally free bicommutative
Hopf algebra. This is the form in which the center can be fed directly to Cartier duality. -/
noncomputable abbrev centerFiniteLocallyFree
    (hH : semisimpleCommHopfAlgProperty k H) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} k :=
  haveI : Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    hH.moduleFinite_centerCoordinate
  let _ : Module.Free k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    Module.Free.of_divisionRing k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)
  haveI : Module.Projective k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    inferInstance
  haveI : Coalgebra.IsCocomm k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isCocomm_quotient
  FiniteLocallyFreeBicommutativeHopfAlgCat.of k
    (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)

/-- The structure morphism from the center of a semisimple affine group to the trivial group is
a central isogeny. Its kernel is the whole center, which is finite locally free and commutative. -/
theorem isCentralIsogeny_centerStructureMorphism
    (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.IsCentralIsogeny
      (CommHopfAlgCat.ofHom
        (Bialgebra.unitBialgHom k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj))) := by
  let _ : Module.Finite k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    hH.moduleFinite_centerCoordinate
  let _ : Nontrivial (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    ⟨⟨0, 1, fun h ↦ (zero_ne_one : (0 : k) ≠ 1) (by
      simpa using congrArg (Coalgebra.counit (R := k)) h)⟩⟩
  let _ : Module.Free k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    Module.Free.of_divisionRing k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)
  let _ : Coalgebra.IsCocomm k (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj) :=
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isCocomm_quotient
  exact CommHopfAlgCat.isCentralIsogeny_unit_of_isCocomm
    (CommHopfAlgCat.centerCoordinateHopfAlgebra H.obj)

end TauCeti.semisimpleCommHopfAlgProperty
