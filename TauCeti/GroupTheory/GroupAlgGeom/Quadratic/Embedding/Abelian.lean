/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.GroupAlgGeom.Abelian
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# The quadratic embedding theorem over an abelian group

Kharlampovich and Myasnikov prove that the coordinate group of a consistent quadratic equation
over a fully residually free group `G` embeds, over `G`, in an iterated extension of centralizers
of `G` ([VAR-I], Theorem 1). For abelian `G` this holds for every consistent system in finitely
many variables (`TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_isMulCommutative`),
although the descriptions of radicals of quadratic equations over nonabelian groups fail there:
over `ℤ` every commutator of variables lies in the radical of the genus-two equation
`[x₁, y₁][x₂, y₂] = 1`. We check the theorem on this equation.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Theorem 1.
-/

namespace TauCeti.GroupAlgGeom

open LimitGroup

variable {X : Type*}

/-- Over `ℤ`, the coordinate group of the genus-two equation `[x₁, y₁][x₂, y₂] = 1`, which every
point solves, embeds in an iterated extension of centralizers of `ℤ`. -/
example [Finite X] {x y : Fin 2 → X} (inj : (Sum.elim x y).Injective) :
    ∃ (E : Type) (_ : Group E) (j : Multiplicative ℤ →* E) (_ : ICE (Multiplicative ℤ) E j)
      (f : GHom (CoordGroup.coeff (.id (Multiplicative ℤ))
        {(Quadratic.Standard.orientable 2 two_pos x y inj).toWord}) j),
      Function.Injective f :=
  exists_ice_embedding_coordGroup_of_isMulCommutative
    isFullyResiduallyFree_multiplicative_int.isResiduallyFree _
    ⟨1, Quadratic.Standard.one_mem_V_orientable _ two_pos inj⟩

end TauCeti.GroupAlgGeom
