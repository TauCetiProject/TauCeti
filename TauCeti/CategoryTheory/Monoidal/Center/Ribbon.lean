/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Abelian
public import TauCeti.CategoryTheory.Monoidal.Center.Pivotal
public import TauCeti.CategoryTheory.Monoidal.Center.Simple
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Ribbon.OfSpherical

/-!
# The centre of a spherical category is ribbon

Let `C` be a rigid monoidal category with a pivotal structure `φ`. Its Drinfeld centre `Center C`
is braided, rigid and pivotal (`CategoryTheory.Center.pivotalCategory`), so it carries the twist
`TauCeti.balancedOfBraidedPivotal (Center C)`, which compares `φ` with the Drinfeld isomorphism
`u_X : X ≅ Xᘁᘁ` of the braiding of the centre. Both are computed from data in `C`: the braiding of
the centre at `(X, β)` is the half-braiding `β`, so `u_X` contracts `X` against `Xᘁ` through
`β Xᘁ`, and the inverse twist of `(X, β)` is the loop

`X ⟶ X ⊗ Xᘁ ⊗ X ⟶ Xᘁ ⊗ X ⊗ X ⟶ X`

that inserts the coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` of the pivotal pairing of `C`, moves `X` past `Xᘁ`
with `β Xᘁ`, and evaluates.

These computations are `CategoryTheory.Center.drinfeldIso_hom_f` and
`CategoryTheory.Center.balancedOfBraidedPivotal_twist_inv_app_f`, which need only the rigid and
pivotal structures and are stated with them in `Center/Rigid.lean` and
`Center/Pivotal.lean`.

When `C` is spherical, so is its centre (`CategoryTheory.Center.sphericalCategory`). If moreover
the centre is a split finite semisimple category with simple unit, sphericity makes the induced
twist ribbon (Müger). The semisimplicity of the centre is a hypothesis here: it does not follow
from that of `C` alone (for a fusion category it also needs the global dimension of `C` to be
nonzero), and it cannot simply be dropped, since in a non-semisimple braided category a spherical
pivotal structure need not induce a ribbon twist.

## Main declarations

* `CategoryTheory.Center.ribbonCategory_of_sphericalCategory`: the twist induced on the centre of
  a spherical category is ribbon, when the centre is split finite semisimple with simple unit.

## References

* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra 180 (2003)
* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.2,
  eq. (3) and Appendix A.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13 and 8.10
-/

public section

open CategoryTheory MonoidalCategory TauCeti

universe v u

namespace CategoryTheory.Center

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

variable (k : Type*) [Field k] [IsAlgClosed k] [SphericalCategory C] [Abelian C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory (Center C)] [Simple (𝟙_ (Center C))]
  [hfin : ∀ (X : Center C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin

/-- **The centre of a spherical category is ribbon** (Müger). For a spherical category `C` whose
centre is a split finite semisimple category with simple unit, the twist induced on `Center C` by
its braiding and its pivotal structure is ribbon. The twist is the one built from the pivotal
structure induced from `C`, not an arbitrary twist of the centre, and the abelian, linear, rigid
and pivotal structures of the centre are the canonical ones.

The simple unit of the centre and the finite-dimensionality of the endomorphisms of its simple
objects are found by instance search when `C` has a simple unit and finite-dimensional
endomorphism spaces (`CategoryTheory.Center.instSimpleUnit`,
`CategoryTheory.Center.instFiniteDimensionalHom`). -/
theorem ribbonCategory_of_sphericalCategory :
    letI := balancedOfBraidedPivotal (Center C)
    RibbonCategory (Center C) :=
  TauCeti.ribbonCategory_of_sphericalCategory (hfin := hfin) k

end CategoryTheory.Center
