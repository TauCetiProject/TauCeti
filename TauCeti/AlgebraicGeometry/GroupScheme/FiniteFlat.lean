/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite flat commutative group schemes

This file defines finite locally free commutative group schemes over a base scheme `S`: schemes
finite, flat and locally of finite presentation over `S`, with a commutative group-object
structure in `Over S`, together with their homomorphisms, isomorphisms and base change. Over an
affine base, see `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat`.

## Main definitions

* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme S`: finite locally free commutative group
  schemes over `S`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.toOver`: the underlying object of
  `Over S`, with its commutative group-object instances `grpObj` and `isCommMonObj`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.Section`: sections of the structure
  morphism.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.Hom` and
  `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.Iso`: homomorphisms and isomorphisms, as
  morphisms and isomorphisms of the underlying group objects in `Grp (Over S)`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange`: base change along a morphism
  of schemes, with `grpMk_baseChange` identifying its group object with the image of that of `G`
  under `(Over.pullback f).mapGrp`, and `Hom.baseChange`: base change of homomorphisms, with
  `Hom.baseChange_eq`, `Hom.baseChange_id` and `Hom.baseChange_comp`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.12.
* The Stacks Project, [Tag 02KB](https://stacks.math.columbia.edu/tag/02KB), for finite locally
  free morphisms as the finite, flat morphisms locally of finite presentation.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- A finite locally free commutative group scheme over `S`: a scheme over `S` whose structure
morphism is finite, flat, and locally of finite presentation, with a commutative group-object
structure in `Over S`. -/
structure FiniteFlatCommGroupScheme (S : Scheme.{u}) where
  /-- The underlying scheme. -/
  carrier : Scheme.{u}
  /-- The structure morphism to the base. -/
  structureMap : carrier ⟶ S
  /-- The group law, as a group object in the category of schemes over `S`. -/
  grp : GrpObj (Over.mk structureMap)
  /-- The group law is commutative. -/
  comm : IsCommMonObj (Over.mk structureMap)
  /-- The structure morphism is finite. -/
  finite : IsFinite structureMap
  /-- The structure morphism is flat. -/
  flat : Flat structureMap
  /-- The structure morphism is locally of finite presentation. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation structureMap

attribute [instance] FiniteFlatCommGroupScheme.finite FiniteFlatCommGroupScheme.flat
  FiniteFlatCommGroupScheme.locallyOfFinitePresentation

namespace FiniteFlatCommGroupScheme

/-- The underlying object of `Over S`. -/
noncomputable abbrev toOver {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) : Over S :=
  Over.mk G.structureMap

/-- The group law of a finite flat commutative group scheme, as a group object over `S`. -/
noncomputable instance grpObj {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) :
    GrpObj G.toOver :=
  G.grp

/-- The group law of a finite flat commutative group scheme is commutative. -/
instance isCommMonObj {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) : IsCommMonObj G.toOver :=
  G.comm

/-- Sections of the structure morphism of a finite flat group scheme: morphisms `s : S ⟶ G.carrier`
with `s ≫ G.structureMap = 𝟙 S`. -/
@[expose]
def Section {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) :=
  {s : S ⟶ G.carrier // s ≫ G.structureMap = 𝟙 S}

/-- A homomorphism of finite flat commutative group schemes over `S`: a morphism of the underlying
group objects in `Grp (Over S)`, that is, a morphism of schemes over `S` compatible with the group
laws. -/
abbrev Hom {S : Scheme.{u}} (G H : FiniteFlatCommGroupScheme S) : Type u :=
  Grp.mk G.toOver ⟶ Grp.mk H.toOver

/-- An isomorphism of finite flat commutative group schemes over `S`: an isomorphism of the
underlying group objects in `Grp (Over S)`. -/
abbrev Iso {S : Scheme.{u}} (G H : FiniteFlatCommGroupScheme S) : Type u :=
  Grp.mk G.toOver ≅ Grp.mk H.toOver

/-- The base change of a finite flat commutative group scheme `G` over `S` along `f : T ⟶ S`: the
fibre product of `G.structureMap` and `f`, with the second projection as structure morphism and
the group law obtained by applying the pullback functor `Over.pullback f`. -/
noncomputable def baseChange {S T : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) (f : T ⟶ S) :
    FiniteFlatCommGroupScheme T where
  carrier := pullback G.structureMap f
  structureMap := pullback.snd G.structureMap f
  grp := Functor.grpObjObj (F := Over.pullback f) (G := G.toOver)
  comm := Functor.isCommMonObj_obj (F := Over.pullback f) (M := G.toOver)
  finite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance

/-- The underlying scheme of the base change of `G` along `f` is the fibre product of
`G.structureMap` and `f`. -/
theorem baseChange_carrier {S T : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) (f : T ⟶ S) :
    (G.baseChange f).carrier = pullback G.structureMap f :=
  (rfl)

/-- The group object underlying the base change of `G` along `f` is the image of the group object
underlying `G` under the pullback functor `Over.pullback f`. -/
theorem grpMk_baseChange {S T : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) (f : T ⟶ S) :
    Grp.mk (G.baseChange f).toOver = (Over.pullback f).mapGrp.obj (Grp.mk G.toOver) :=
  (rfl)

/-- The base change along `f : T ⟶ S` of a homomorphism of finite flat commutative group schemes
over `S`: the image of the homomorphism under `(Over.pullback f).mapGrp`, read through
`grpMk_baseChange`. -/
noncomputable def Hom.baseChange {S T : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S}
    (φ : G.Hom H) (f : T ⟶ S) : (G.baseChange f).Hom (H.baseChange f) :=
  eqToHom (G.grpMk_baseChange f) ≫ (Over.pullback f).mapGrp.map φ ≫
    eqToHom (H.grpMk_baseChange f).symm

/-- The base change of a homomorphism is the image of the homomorphism under
`(Over.pullback f).mapGrp`, read through `grpMk_baseChange`. -/
theorem Hom.baseChange_eq {S T : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} (φ : G.Hom H)
    (f : T ⟶ S) : φ.baseChange f = eqToHom (G.grpMk_baseChange f) ≫
      (Over.pullback f).mapGrp.map φ ≫ eqToHom (H.grpMk_baseChange f).symm :=
  (rfl)

/-- Base change of homomorphisms preserves identities. -/
@[simp]
theorem Hom.baseChange_id {S T : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) (f : T ⟶ S) :
    Hom.baseChange (𝟙 (Grp.mk G.toOver)) f = 𝟙 _ := by
  simp [Hom.baseChange_eq]

/-- Base change of homomorphisms preserves composition. -/
@[simp]
theorem Hom.baseChange_comp {S T : Scheme.{u}} {G H K : FiniteFlatCommGroupScheme S}
    (φ : G.Hom H) (ψ : H.Hom K) (f : T ⟶ S) :
    Hom.baseChange (φ ≫ ψ) f = φ.baseChange f ≫ ψ.baseChange f := by
  simp [Hom.baseChange_eq]

end FiniteFlatCommGroupScheme

end TauCeti.AlgebraicGeometry
