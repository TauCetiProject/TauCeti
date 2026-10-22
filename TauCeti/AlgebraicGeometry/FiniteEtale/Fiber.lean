/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic

/-!
# Base change and geometric fibres of finite étale schemes

Finite étale morphisms are stable under base change, so pulling back along `f : T ⟶ S`
restricts Mathlib's `Over.pullback f` to a functor `FiniteEtaleScheme.pullback f` from finite
étale `S`-schemes to finite étale `T`-schemes. Base change along identities and composites is
identified with the identity and with composites of base changes by `pullbackId` and
`pullbackComp`, whose components are those of `Over.pullbackId` and `Over.pullbackComp`.

For a geometric point `x : Spec Ω ⟶ S`, with `Ω` a separably closed field, the
*geometric fibre functor* `FiniteEtaleScheme.fiber x` sends a finite étale `S`-scheme `X` to the
finite set attached to `X ×_S Spec Ω` by the classification of finite étale schemes over a
separably closed field. This is the functor on finite étale covers whose automorphisms define
the étale fundamental group based at `x`.

The fibre functor is corepresented by the geometric point itself:
`FiniteEtaleScheme.fiberCompInclIso` identifies `fiber x` with the set of lifts of `x` to
`X`, that is, with morphisms `Over.mk x ⟶ X` in `Over S`. Its proof combines the adjunction
`Over.map x ⊣ Over.pullback x` with `equivOfIsSepClosedFunctorCompInclIso`, which identifies
the finite set attached to a finite étale `Spec Ω`-scheme with its set of sections.
Changing the geometric point along a morphism of bases is `pullbackCompFiberIso`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §§4–7.
* H. W. Lenstra, *Galois theory for schemes*.
* The Stacks Project, Section 58.5 (*Finite étale covers of schemes*).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S T U : Scheme.{u}}

/-- Base change of finite étale schemes along `f : T ⟶ S`, sending `X` to `X ×_S T` over `T`.
On underlying objects over the bases it is Mathlib's `Over.pullback f`. -/
@[expose] noncomputable def pullback (f : T ⟶ S) : FiniteEtaleScheme S ⥤ FiniteEtaleScheme T :=
  (finiteEtaleSchemeProperty T).lift ((finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f)
    fun X ↦ (finiteEtaleSchemeProperty_iff _).mpr
      ⟨inferInstanceAs (IsFinite (Limits.pullback.snd X.obj.hom f)),
        inferInstanceAs (Etale (Limits.pullback.snd X.obj.hom f))⟩

/-- Forgetting finiteness and étaleness, base change is `Over.pullback`. -/
@[simp]
theorem pullback_comp_ι (f : T ⟶ S) :
    pullback f ⋙ (finiteEtaleSchemeProperty T).ι =
      (finiteEtaleSchemeProperty S).ι ⋙ Over.pullback f :=
  (rfl)

/-- The scheme over `T` underlying a base change is `Over.pullback f` of the original. -/
@[simp]
theorem pullback_obj_obj (f : T ⟶ S) (X : FiniteEtaleScheme S) :
    ((pullback f).obj X).obj = (Over.pullback f).obj X.obj :=
  (rfl)

/-- On morphisms, base change is `Over.pullback f`. -/
@[simp]
theorem pullback_map_hom (f : T ⟶ S) {X Y : FiniteEtaleScheme S} (g : X ⟶ Y) :
    ((pullback f).map g).hom = (Over.pullback f).map g.hom :=
  (rfl)

/-- Base change along the identity is the identity, with components those of
`Over.pullbackId`. -/
noncomputable def pullbackId : pullback (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (Over.pullbackId.app X.obj))
    fun f ↦ ObjectProperty.hom_ext _ (Over.pullbackId.hom.naturality f.hom)

/-- The components of `pullbackId.hom` are those of `Over.pullbackId.hom`. -/
@[simp]
theorem pullbackId_hom_app_hom (X : FiniteEtaleScheme S) :
    (pullbackId.hom.app X).hom = Over.pullbackId.hom.app X.obj :=
  (rfl)

/-- The components of `pullbackId.inv` are those of `Over.pullbackId.inv`. -/
@[simp]
theorem pullbackId_inv_app_hom (X : FiniteEtaleScheme S) :
    (pullbackId.inv.app X).hom = Over.pullbackId.inv.app X.obj :=
  (rfl)

/-- Base change along a composite is the composite of the base changes, with components those
of `Over.pullbackComp`. -/
noncomputable def pullbackComp (f : T ⟶ S) (g : S ⟶ U) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ ((Over.pullbackComp f g).app X.obj))
    fun h ↦ ObjectProperty.hom_ext _ ((Over.pullbackComp f g).hom.naturality h.hom)

/-- The components of `(pullbackComp f g).hom` are those of `Over.pullbackComp`. -/
@[simp]
theorem pullbackComp_hom_app_hom (f : T ⟶ S) (g : S ⟶ U) (X : FiniteEtaleScheme U) :
    ((pullbackComp f g).hom.app X).hom = (Over.pullbackComp f g).hom.app X.obj :=
  (rfl)

/-- The components of `(pullbackComp f g).inv` are those of `Over.pullbackComp`. -/
@[simp]
theorem pullbackComp_inv_app_hom (f : T ⟶ S) (g : S ⟶ U) (X : FiniteEtaleScheme U) :
    ((pullbackComp f g).inv.app X).hom = (Over.pullbackComp f g).inv.app X.obj :=
  (rfl)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre functor at a geometric point `x : Spec Ω ⟶ S`, for `Ω` separably
closed: a finite étale `S`-scheme `X` goes to the finite set classifying `X ×_S Spec Ω`. -/
@[expose] noncomputable def fiber (x : Spec (.of Ω) ⟶ S) : FiniteEtaleScheme S ⥤ FintypeCat.{u} :=
  pullback x ⋙ (equivOfIsSepClosed Ω).functor

/-- The geometric fibre functor is base change to the geometric point followed by the
classification of finite étale schemes over a separably closed field. -/
theorem fiber_def (x : Spec (.of Ω) ⟶ S) :
    fiber x = pullback x ⋙ (equivOfIsSepClosed Ω).functor :=
  (rfl)

/-- The geometric fibre functor at `x` is corepresented by `x`: the fibre of `X` is naturally
the set of lifts of `x` to `X`, that is, of morphisms `Over.mk x ⟶ X` over `S`. -/
noncomputable def fiberCompInclIso (x : Spec (.of Ω) ⟶ S) :
    fiber x ⋙ FintypeCat.incl ≅
      (finiteEtaleSchemeProperty S).ι ⋙ coyoneda.obj (op (Over.mk x)) :=
  Iso.symm <| Functor.isoWhiskerLeft _
      (coyoneda.mapIso (Over.isoMk (Iso.refl _) :
          (Over.map x).obj (Over.mk (𝟙 _)) ≅ Over.mk x).op ≪≫
        (Over.mapPullbackAdj x).compCoyonedaIso.app (op (Over.mk (𝟙 _)))) ≪≫
    Functor.isoWhiskerLeft (pullback x) (equivOfIsSepClosedFunctorCompInclIso Ω).symm

/-- A lift `g : Over.mk x ⟶ X` of the geometric point `x` gives the point of the fibre
corresponding, under `equivOfIsSepClosedFunctorCompInclIso`, to the section of `X ×_S Spec Ω`
adjoint to `g` under `Over.map x ⊣ Over.pullback x`. -/
theorem fiberCompInclIso_inv_app_apply (x : Spec (.of Ω) ⟶ S) (X : FiniteEtaleScheme S)
    (g : Over.mk x ⟶ X.obj) :
    (fiberCompInclIso x).inv.app X g =
      (equivOfIsSepClosedFunctorCompInclIso Ω).inv.app ((pullback x).obj X)
        ((Over.mapPullbackAdj x).homEquiv _ _ (Over.homMk (𝟙 _) ≫ g)) :=
  (rfl)

/-- A point `y` of the fibre gives the lift of `x` adjoint, under `Over.map x ⊣ Over.pullback x`,
to the section of `X ×_S Spec Ω` corresponding to `y` under
`equivOfIsSepClosedFunctorCompInclIso`. -/
theorem fiberCompInclIso_hom_app_apply (x : Spec (.of Ω) ⟶ S) (X : FiniteEtaleScheme S)
    (y : (fiber x).obj X) :
    (fiberCompInclIso x).hom.app X y =
      Over.homMk (𝟙 _) ≫ ((Over.mapPullbackAdj x).homEquiv _ _).symm
        ((equivOfIsSepClosedFunctorCompInclIso Ω).hom.app ((pullback x).obj X) y) :=
  (rfl)

variable (Ω) in
/-- The geometric fibre functor of `Spec Ω` at its identity point is the classification of
finite étale schemes over the separably closed field `Ω` by finite sets. -/
noncomputable def fiberIdIso : fiber (𝟙 (Spec (.of Ω))) ≅ (equivOfIsSepClosed Ω).functor :=
  Functor.isoWhiskerRight pullbackId _ ≪≫ Functor.leftUnitor _

variable (Ω) in
/-- The components of `fiberIdIso` are the images of those of `pullbackId`. -/
@[simp]
theorem fiberIdIso_hom_app (X : FiniteEtaleScheme (Spec (.of Ω))) :
    (fiberIdIso Ω).hom.app X = (equivOfIsSepClosed Ω).functor.map (pullbackId.hom.app X) :=
  (rfl)

variable (Ω) in
/-- The components of `(fiberIdIso Ω).inv` are the images of those of `pullbackId.inv`. -/
@[simp]
theorem fiberIdIso_inv_app (X : FiniteEtaleScheme (Spec (.of Ω))) :
    (fiberIdIso Ω).inv.app X = (equivOfIsSepClosed Ω).functor.map (pullbackId.inv.app X) :=
  (rfl)

/-- Base change along `f : T ⟶ S` followed by the geometric fibre at `x : Spec Ω ⟶ T` is the
geometric fibre at the composite geometric point `x ≫ f`. -/
noncomputable def pullbackCompFiberIso (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T) :
    pullback f ⋙ fiber x ≅ fiber (x ≫ f) :=
  Functor.isoWhiskerRight (pullbackComp x f).symm _

/-- The components of `pullbackCompFiberIso` are the images of those of `pullbackComp`. -/
@[simp]
theorem pullbackCompFiberIso_hom_app (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T)
    (X : FiniteEtaleScheme S) :
    (pullbackCompFiberIso f x).hom.app X =
      (equivOfIsSepClosed Ω).functor.map ((pullbackComp x f).inv.app X) :=
  (rfl)

/-- The components of `(pullbackCompFiberIso f x).inv` are the images of those of
`pullbackComp`. -/
@[simp]
theorem pullbackCompFiberIso_inv_app (f : T ⟶ S) (x : Spec (.of Ω) ⟶ T)
    (X : FiniteEtaleScheme S) :
    (pullbackCompFiberIso f x).inv.app X =
      (equivOfIsSepClosed Ω).functor.map ((pullbackComp x f).hom.app X) :=
  (rfl)

end TauCeti.FiniteEtaleScheme
