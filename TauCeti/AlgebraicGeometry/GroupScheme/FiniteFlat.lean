/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel

/-!
# Finite flat commutative group schemes

This file defines finite locally free commutative group schemes over a base scheme `S`: schemes
finite, flat and locally of finite presentation over `S`, with a commutative group-object
structure in `Over S`, together with their homomorphisms, isomorphisms and base change, and the
kernels of finite locally free homomorphisms of commutative group schemes. Over an
affine base, see `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat`.

## Main definitions

* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme S`: finite locally free commutative group
  schemes over `S`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.toOver`: the underlying object of
  `Over S`, with its commutative group-object instances `grpObj` and `isCommMonObj`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.Section`: sections of the structure
  morphism.
* Group-scheme homomorphisms give the category structure. The functor `toGrp` to `Grp (Over S)`
  is fully faithful.
* The comparison with the affine category is in `GroupScheme/FiniteFlat/Affine.lean`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange`: base change along a morphism
  of schemes, with `grpMk_baseChange` identifying its group object with the image of that of `G`
  under `(Over.pullback f).mapGrp`. The functor `baseChangeFunctor` bundles base change on
  objects and homomorphisms.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.ofKernel`: the scheme-theoretic kernel of a
  finite locally free homomorphism out of a commutative group scheme, with `grpMk_ofKernel`
  identifying its group object with the categorical kernel, and its inclusion `ofKernelι`, a kernel
  of the homomorphism (`isLimitOfKernelι`).

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

/-- Finite locally free commutative group schemes form a category with their group-scheme
homomorphisms as morphisms. -/
noncomputable instance {S : Scheme.{u}} : Category (FiniteFlatCommGroupScheme S) where
  Hom G H := Grp.mk G.toOver ⟶ Grp.mk H.toOver
  id G := 𝟙 (Grp.mk G.toOver)
  comp f g := f ≫ g

/-- Homomorphisms of finite locally free group schemes are determined by their maps over the
base. -/
@[ext]
theorem hom_ext {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} (f g : G ⟶ H)
    (h : f.hom.hom = g.hom.hom) : f = g :=
  Grp.hom_ext f g h

/-- The identity homomorphism has the identity as its underlying map over the base. -/
@[simp]
theorem id_hom_hom {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) :
    (𝟙 G : G ⟶ G).hom.hom = 𝟙 G.toOver :=
  (rfl)

/-- Composition of homomorphisms composes the underlying maps over the base. -/
@[simp, reassoc]
theorem comp_hom_hom {S : Scheme.{u}} {G H K : FiniteFlatCommGroupScheme S}
    (f : G ⟶ H) (g : H ⟶ K) : (f ≫ g).hom.hom = f.hom.hom ≫ g.hom.hom :=
  (rfl)

/-- The fully faithful functor forgetting finiteness and commutativity of a finite locally free
commutative group scheme. The object map is exposed so that its morphisms are the underlying
group-object homomorphisms without transports. -/
@[expose]
noncomputable def toGrp (S : Scheme.{u}) : FiniteFlatCommGroupScheme S ⥤ Grp (Over S) where
  obj G := Grp.mk G.toOver
  map f := f

/-- The forgetful functor retains the underlying group object. -/
@[simp]
theorem toGrp_obj {S : Scheme.{u}} (G : FiniteFlatCommGroupScheme S) :
    (toGrp S).obj G = Grp.mk G.toOver :=
  (rfl)

/-- The forgetful functor retains the underlying homomorphism. -/
@[simp]
theorem toGrp_map {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    (toGrp S).map f = f :=
  (rfl)

/-- Forgetting finiteness and commutativity does not change group-scheme homomorphisms. -/
noncomputable def fullyFaithfulToGrp (S : Scheme.{u}) : (toGrp S).FullyFaithful where
  preimage f := f

instance {S : Scheme.{u}} : (toGrp S).Full := (fullyFaithfulToGrp S).full

instance {S : Scheme.{u}} : (toGrp S).Faithful := (fullyFaithfulToGrp S).faithful

/-- The explicit fully faithful structure lifts a homomorphism without changing it. -/
@[simp]
theorem fullyFaithfulToGrp_preimage {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S}
    (f : (toGrp S).obj G ⟶ (toGrp S).obj H) : (fullyFaithfulToGrp S).preimage f = f :=
  (rfl)

/-- The forgetful functor lifts a homomorphism without changing it. -/
@[simp]
theorem toGrp_preimage {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S}
    (f : (toGrp S).obj G ⟶ (toGrp S).obj H) : (toGrp S).preimage f = f :=
  (toGrp S).map_preimage f

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

/-- Base change of finite locally free commutative group schemes and their homomorphisms.
The object map is exposed so its morphisms can be read through `grpMk_baseChange` without
additional dependent transports. -/
@[expose]
noncomputable def baseChangeFunctor {S T : Scheme.{u}} (f : T ⟶ S) :
    FiniteFlatCommGroupScheme S ⥤ FiniteFlatCommGroupScheme T where
  obj G := G.baseChange f
  -- The intermediate pullback group objects live in `Grp (Over T)`, so compose there before
  -- regarding the resulting homomorphism as one of finite flat group schemes.
  map {G H} φ := (eqToHom (G.grpMk_baseChange f) ≫ (Over.pullback f).mapGrp.map φ ≫
    eqToHom (H.grpMk_baseChange f).symm :
      Grp.mk (G.baseChange f).toOver ⟶ Grp.mk (H.baseChange f).toOver)
  map_id G := by
    -- The category instance uses group-object homomorphisms definitionally. Restate its identity
    -- in `Grp (Over T)` so the pullback functor law and transport cancellation match syntactically.
    change eqToHom _ ≫ (Over.pullback f).mapGrp.map (𝟙 (Grp.mk G.toOver)) ≫ _ =
      𝟙 (Grp.mk (G.baseChange f).toOver)
    simp
  map_comp {G H K} φ ψ := by
    -- Likewise expose composition in `Grp (Over T)`; rewriting object equalities alone does not
    -- identify the category operations on finite flat group schemes with these operations.
    change eqToHom _ ≫ (Over.pullback f).mapGrp.map (φ ≫ ψ) ≫ _ =
      (eqToHom _ ≫ (Over.pullback f).mapGrp.map φ ≫ _) ≫
        (eqToHom _ ≫ (Over.pullback f).mapGrp.map ψ ≫ _)
    simp

/-- The object map of the base-change functor is scheme-theoretic base change. -/
@[simp]
theorem baseChangeFunctor_obj {S T : Scheme.{u}} (f : T ⟶ S)
    (G : FiniteFlatCommGroupScheme S) : (baseChangeFunctor f).obj G = G.baseChange f :=
  (rfl)

/-- The base-change functor acts on homomorphisms by the pullback functor on group objects. -/
theorem baseChangeFunctor_map {S T : Scheme.{u}} (f : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (φ : G ⟶ H) :
    (toGrp T).map ((baseChangeFunctor f).map φ) =
      eqToHom (G.grpMk_baseChange f) ≫ (Over.pullback f).mapGrp.map ((toGrp S).map φ) ≫
        eqToHom (H.grpMk_baseChange f).symm :=
  (rfl)

/-- Base change commutes with forgetting to group objects over the base. -/
noncomputable def baseChangeFunctorCompToGrpIso {S T : Scheme.{u}} (f : T ⟶ S) :
    baseChangeFunctor f ⋙ toGrp T ≅ toGrp S ⋙ (Over.pullback f).mapGrp :=
  Iso.refl _

/-- The forward base-change comparison is the canonical identification of group objects. -/
@[simp]
theorem baseChangeFunctorCompToGrpIso_hom_app {S T : Scheme.{u}} (f : T ⟶ S)
    (G : FiniteFlatCommGroupScheme S) :
    (baseChangeFunctorCompToGrpIso f).hom.app G = eqToHom (G.grpMk_baseChange f) :=
  (rfl)

/-- The inverse base-change comparison is the inverse identification of group objects. -/
@[simp]
theorem baseChangeFunctorCompToGrpIso_inv_app {S T : Scheme.{u}} (f : T ⟶ S)
    (G : FiniteFlatCommGroupScheme S) :
    (baseChangeFunctorCompToGrpIso f).inv.app G = eqToHom (G.grpMk_baseChange f).symm :=
  (rfl)

section Kernel

variable {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H) [IsCommMonObj G.X]
  [IsFinite f.hom.hom.left] [Flat f.hom.hom.left] [LocallyOfFinitePresentation f.hom.hom.left]

/-- **The kernel of a finite locally free homomorphism of group schemes** out of a commutative group
scheme, as a finite locally free commutative group scheme over the base. Its group object is the
categorical kernel `Limits.kernel f` (`grpMk_ofKernel`). -/
noncomputable def ofKernel : FiniteFlatCommGroupScheme S where
  carrier := (kernel f).X.left
  structureMap := (kernel f).X.hom
  grp := inferInstanceAs (GrpObj (kernel f).X)
  comm := inferInstanceAs (IsCommMonObj (kernel f).X)
  finite := inferInstanceAs (IsFinite (kernel f).X.hom)
  flat := inferInstanceAs (Flat (kernel f).X.hom)
  locallyOfFinitePresentation := inferInstanceAs (LocallyOfFinitePresentation (kernel f).X.hom)

/-- The underlying scheme of `ofKernel f` is that of the categorical kernel of `f`. -/
theorem ofKernel_carrier : (ofKernel f).carrier = (kernel f).X.left :=
  (rfl)

/-- The scheme over `S` underlying `ofKernel f` is that of the categorical kernel of `f`. -/
theorem ofKernel_toOver : (ofKernel f).toOver = (kernel f).X :=
  (rfl)

/-- The group object underlying `ofKernel f` is the categorical kernel of `f` in `Grp (Over S)`. -/
theorem grpMk_ofKernel : Grp.mk (ofKernel f).toOver = kernel f :=
  (rfl)

/-- The inclusion of `ofKernel f` into the source of `f`, the inclusion `Limits.kernel.ι f` of the
categorical kernel. -/
noncomputable def ofKernelι : Grp.mk (ofKernel f).toOver ⟶ G :=
  kernel.ι f

/-- The inclusion of `ofKernel f` is killed by `f`. -/
@[reassoc (attr := simp)]
theorem ofKernelι_comp : ofKernelι f ≫ f = 0 :=
  kernel.condition f

/-- `ofKernelι f` is a kernel of `f` in `Grp (Over S)`. -/
noncomputable def isLimitOfKernelι :
    IsLimit (KernelFork.ofι (ofKernelι f) (ofKernelι_comp f)) :=
  kernelIsKernel f

end Kernel

end FiniteFlatCommGroupScheme

end TauCeti.AlgebraicGeometry
