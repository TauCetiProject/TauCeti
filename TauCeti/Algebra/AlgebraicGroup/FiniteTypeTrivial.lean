/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteTypeCommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Trivial

/-!
# The finite-type trivial affine group

This file packages the base ring `R`, with its canonical Hopf algebra structure over itself,
as the finite-type coordinate Hopf algebra of the trivial affine group. In the coordinate
Hopf-algebra category this object is initial: the unique morphism from `R` to a coordinate
Hopf algebra is the bialgebra unit map `R → H`. Contravariantly, this is the terminal object
`Spec R` over `Spec R` in the affine-group-scheme dictionary.

The file also records the counit morphism `H → R` and the pointwise formulas for the unit and
counit maps.

This is Layer 0 infrastructure for the ReductiveGroups roadmap: the finite-type
coordinate-Hopf-algebra model needs the terminal affine group object over the base, separate
from the already available raw Hopf-algebra points calculation in `TrivialGroup.pointsMulEquiv`.

## References

The bialgebra unit and counit maps are Mathlib's `Bialgebra.unitBialgHom` and
`Bialgebra.counitBialgHom`.
-/

public section

open CategoryTheory CategoryTheory.Limits WithConv

namespace TauCeti

universe u v w

namespace FiniteTypeCommHopfAlgCat

variable (R : Type u) [CommRing R]

/-- The finite-type coordinate Hopf algebra of the trivial affine group over `R`.

Its underlying Hopf algebra is `R` over itself, and the finite-type proof is the canonical
finite-generation of the base algebra over itself. -/
noncomputable abbrev trivial : FiniteTypeCommHopfAlgCat.{u, u} R :=
  of R R

/-- The underlying coordinate Hopf algebra of the finite-type trivial coordinate Hopf algebra
is the base ring over itself. -/
@[simp]
lemma trivial_obj :
    (trivial R).obj = (_root_.CommHopfAlgCat.of R R) :=
  rfl

variable {R}

/-- The coordinate morphism from the trivial affine group to a finite-type affine group.

On coordinate Hopf algebras this is the bialgebra unit map `R → H`, contravariant to the
unique morphism from the represented affine group to the terminal affine group `Spec R`. -/
noncomputable abbrev unit (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    trivial R ⟶ H :=
  ofHom (_root_.Bialgebra.unitBialgHom R H)

/-- The coordinate morphism from a finite-type affine group to the trivial affine group.

On coordinate Hopf algebras this is the bialgebra counit map `H → R`, contravariant to the
identity section `Spec R → G`. -/
noncomputable abbrev counit (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    H ⟶ trivial R :=
  ofHom (_root_.Bialgebra.counitBialgHom R H)

/-- The finite-type coordinate unit morphism unwraps to Mathlib's bialgebra unit map. -/
@[simp]
lemma toBialgHom_unit (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    toBialgHom (unit H) = _root_.Bialgebra.unitBialgHom R H :=
  rfl

/-- The finite-type coordinate counit morphism unwraps to Mathlib's bialgebra counit map. -/
@[simp]
lemma toBialgHom_counit (H : FiniteTypeCommHopfAlgCat.{u, u} R) :
    toBialgHom (counit H) = _root_.Bialgebra.counitBialgHom R H :=
  rfl

/-- Pointwise formula for the coordinate unit map `R → H`. -/
lemma unit_apply (H : FiniteTypeCommHopfAlgCat.{u, u} R) (r : R) :
    toBialgHom (unit H) r = algebraMap R H r :=
  rfl

/-- Pointwise formula for the coordinate counit map `H → R`. -/
lemma counit_apply (H : FiniteTypeCommHopfAlgCat.{u, u} R) (h : H) :
    toBialgHom (counit H) h = Coalgebra.counit h :=
  _root_.Bialgebra.counitBialgHom_apply h

/-- The finite-type trivial coordinate Hopf algebra is initial in the coordinate category.

Equivalently, in the opposite affine-group-scheme direction it represents the terminal
object `Spec R` over the base. -/
noncomputable def trivialIsInitial :
    IsInitial (trivial R : FiniteTypeCommHopfAlgCat.{u, u} R) :=
  IsInitial.ofUniqueHom
    (fun H => unit H)
    (fun H f => by
      apply hom_ext
      apply _root_.BialgHom.coe_toAlgHom_injective
      exact Subsingleton.elim _ _)

/-- The unique morphism out of the finite-type trivial coordinate Hopf algebra is the unit. -/
lemma eq_unit (H : FiniteTypeCommHopfAlgCat.{u, u} R)
    (f : trivial R ⟶ H) :
    f = unit H :=
  (trivialIsInitial (R := R)).hom_ext f (unit H)

end FiniteTypeCommHopfAlgCat

end TauCeti
