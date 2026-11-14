/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Semisimple
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
twist ribbon (`ribbonCategory_of_sphericalCategory`, Müger). Semisimplicity of the centre cannot
simply be dropped, since in a non-semisimple braided category a spherical pivotal structure need
not induce a ribbon twist. When `C` is a spherical fusion category over an algebraically closed
field `k` with `globalDim C ≠ 0` — and unconditionally when `CharZero k` — finite semisimplicity of
`Center C` is supplied by `Center/Semisimple.lean`, giving
`ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero` and
`ribbonCategory_of_sphericalCategory_of_charZero`.

## Main declarations

* `CategoryTheory.Center.ribbonCategory_of_sphericalCategory`: the twist induced on the centre of
  a spherical category is ribbon, when the centre is split finite semisimple with simple unit;
* `CategoryTheory.Center.ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero`: the centre of a
  spherical fusion category with `globalDim C ≠ 0` is ribbon;
* `CategoryTheory.Center.ribbonCategory_of_sphericalCategory_of_charZero`: the centre of a
  spherical fusion category in characteristic zero is ribbon.

## References

* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra 180 (2003), Theorem 3.16
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  Theorem 2.15
* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.2,
  eq. (3) and Appendix A.2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 8.10, 9.3
-/

public section

open CategoryTheory MonoidalCategory TauCeti

universe v u

namespace CategoryTheory.Center

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

section CenterSemisimple

variable (k : Type*) [Field k] [IsAlgClosed k] [SphericalCategory C] [Abelian C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory (Center C)] [Simple (𝟙_ (Center C))]
  [hfin : ∀ (X : Center C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin in
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

end CenterSemisimple

section Fusion

variable (k : Type*) [Field k] [IsAlgClosed k] [SphericalCategory C] [Abelian C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

include k in
/-- **The centre of a spherical fusion category of nonzero global dimension is ribbon**
(Müger, Etingof–Nikshych–Ostrik). For a spherical fusion category `C` over an algebraically closed
field `k` with `globalDim C ≠ 0`, the twist induced on `Center C` by its braiding and pivotal
structure is ribbon. -/
theorem ribbonCategory_of_sphericalCategory_of_globalDim_ne_zero [Fintype (SimpleClasses C)]
    (hdim : globalDim C ≠ 0) :
    letI := balancedOfBraidedPivotal (Center C)
    RibbonCategory (Center C) := by
  have := isFiniteSemisimpleCategory_of_globalDim_ne_zero k hdim
  exact ribbonCategory_of_sphericalCategory (hfin := inferInstance) k

include k in
/-- **The centre of a spherical fusion category in characteristic zero is ribbon**
(Müger, Etingof–Nikshych–Ostrik). -/
theorem ribbonCategory_of_sphericalCategory_of_charZero [CharZero k] [Finite (SimpleClasses C)] :
    letI := balancedOfBraidedPivotal (Center C)
    RibbonCategory (Center C) := by
  have := isFiniteSemisimpleCategory_of_charZero k (C := C)
  exact ribbonCategory_of_sphericalCategory (hfin := inferInstance) k

end Fusion

end CategoryTheory.Center
