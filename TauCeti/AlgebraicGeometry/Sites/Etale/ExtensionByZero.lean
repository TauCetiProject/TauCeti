/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.BaseChange
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Sites.ExtensionByZero.FullyFaithful
public import TauCeti.CategoryTheory.Sites.Point.Comap

/-!
# Extension by zero on the small étale site

For an étale morphism `j : X ⟶ Y`, extension by zero `j_!` of sheaves on the small étale site is
the left adjoint of the inverse image `j^*`, which is restriction along
`j.smallEtaleMap : X.Etale ⥤ Y.Etale`. We write it
`j.smallEtaleExtensionByZero A : Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A`;
it is Mathlib's `Functor.sheafPullback` along `j.smallEtaleMap`, and
`j.smallEtaleExtensionByZeroAdjunction A` is the adjunction `j_! ⊣ j^*`.

When `j` is moreover a monomorphism, for instance an open immersion, `j.smallEtaleMap` is fully
faithful, and an étale `Y`-scheme admitting a `Y`-morphism to an étale `X`-scheme is itself an
étale `X`-scheme. Then `j_!` exists for sheaves with values in any category with an initial object
in which sheafification exists, and it is exact when the values have a zero object and finite
limits. Its geometric stalks are computed as follows: at `s ≫ j` for a geometric point
`s : Spec Ω ⟶ X` the stalk of `j_! F` is the stalk of `F` at `s`, and at a geometric point of
`Y` not factoring through `j` it is zero when the coefficient category has zero morphisms (the
latter for every étale `j`). For sheaves of
`Λ`-modules, `j_!` preserves short exact sequences. Restricting back along an étale monomorphism
recovers the sheaf, `j^* j_! ≅ 𝟭`, so `j_!` is fully faithful; and for every étale `j`, the
pullback of `j_! F` along a morphism whose image avoids the image of `j` is zero.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smallEtaleExtensionByZero`: extension by zero `j_!`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleExtensionByZeroAdjunction`: `j_! ⊣ j^*`.
* `AlgebraicGeometry.Scheme.Hom.preservesFiniteLimits_smallEtaleExtensionByZero`: `j_!` is exact
  for an étale monomorphism `j`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleExtensionByZeroCompSheafFiberIso` and
  `AlgebraicGeometry.Scheme.Hom.isZero_sheafFiber_smallEtaleExtensionByZero_obj`: the stalks of
  `j_! F`.
* `AlgebraicGeometry.Scheme.Hom.shortExact_map_smallEtaleExtensionByZero`: `j_!` preserves short
  exact sequences of étale sheaves of `Λ`-modules.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleExtensionByZeroCompSmallEtalePullbackIso` and
  `AlgebraicGeometry.Scheme.Hom.fullyFaithfulSmallEtaleExtensionByZero`: `j^* j_! ≅ 𝟭` for an
  étale monomorphism `j`, so `j_!` is fully faithful.
* `AlgebraicGeometry.Scheme.Hom.isZero_smallEtalePullback_smallEtaleExtensionByZero_obj`: the
  pullback of `j_! F` to a scheme mapping into the complement of the image of `j` is zero.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §11.3.
* The Stacks Project, Section 59.70, Extension by zero (tag 03S3).
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [Etale j]

section Definition

variable (A : Type*) [Category* A]
  [(j.smallEtaleMap.sheafPushforwardContinuous A (smallEtaleTopology X)
    (smallEtaleTopology Y)).IsRightAdjoint]

/-- **Extension by zero** `j_!` along an étale morphism `j : X ⟶ Y`: the left adjoint of
restriction of small étale sheaves along `j.smallEtaleMap`, that is, of the inverse image `j^*`. -/
noncomputable abbrev smallEtaleExtensionByZero :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  j.smallEtaleMap.sheafPullback A (smallEtaleTopology X) (smallEtaleTopology Y)

/-- Extension by zero is left adjoint to the inverse image: `j_! ⊣ j^*`. -/
noncomputable def smallEtaleExtensionByZeroAdjunction :
    j.smallEtaleExtensionByZero A ⊣ j.smallEtalePullback A :=
  (j.smallEtaleMap.sheafAdjunctionContinuous A (smallEtaleTopology X)
    (smallEtaleTopology Y)).ofNatIsoRight (j.smallEtalePullbackIsoMapPushforward A).symm

end Definition

section Mono

variable [Mono j]

/-- For an étale monomorphism `j`, presheaves on `X.Etale` with values in a category with an
initial object have pointwise left Kan extensions along `j.smallEtaleMap.op`. -/
instance hasPointwiseLeftKanExtension_smallEtaleMap_op {A : Type*} [Category* A] [HasInitial A]
    (F : X.Etaleᵒᵖ ⥤ A) : j.smallEtaleMap.op.HasPointwiseLeftKanExtension F :=
  Functor.hasPointwiseLeftKanExtension_op_of_fullyFaithful (.ofFullyFaithful _)
    (fun _ _ f ↦ j.smallEtaleMap_essImage f) F

/-- **Extension by zero is exact.** For an étale monomorphism `j` (for instance an open
immersion), `j_!` preserves finite limits; as a left adjoint it also preserves colimits. -/
instance preservesFiniteLimits_smallEtaleExtensionByZero (A : Type*) [Category* A]
    [HasZeroObject A] [HasFiniteLimits A] [HasSheafify (smallEtaleTopology Y) A] :
    PreservesFiniteLimits (j.smallEtaleExtensionByZero A) :=
  Functor.preservesFiniteLimits_sheafPullback_of_fullyFaithful (.ofFullyFaithful _)
    (fun _ _ f ↦ j.smallEtaleMap_essImage f) _ _

section Stalks

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

variable (A : Type*) [Category* A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
  [(j.smallEtaleMap.sheafPushforwardContinuous A (smallEtaleTopology X)
    (smallEtaleTopology Y)).IsRightAdjoint]

/-- **Stalks of an extension by zero on the image.** For an étale monomorphism `j` and a geometric
point `s : Spec Ω ⟶ X`, the stalk of `j_! F` at `s ≫ j` is naturally the stalk of `F` at `s`. -/
noncomputable abbrev smallEtaleExtensionByZeroCompSheafFiberIso (s : Spec (.of Ω) ⟶ X) :
    j.smallEtaleExtensionByZero A ⋙ (pointSmallEtale (s ≫ j)).sheafFiber ≅
      (pointSmallEtale s).sheafFiber :=
  (pointSmallEtale (s ≫ j)).sheafPullbackCompSheafFiberIso j.smallEtaleMap
    (j.smallEtaleMapCompFiberIso s) A

omit [Mono j] in
/-- **Stalks of an extension by zero off the image.** When the coefficient category has zero
morphisms, at a geometric point `s : Spec Ω ⟶ Y` that does not factor through the étale morphism
`j`, the stalk of `j_! F` is zero. -/
theorem isZero_sheafFiber_smallEtaleExtensionByZero_obj [HasZeroMorphisms A]
    {s : Spec (.of Ω) ⟶ Y} (hs : ∀ s' : Spec (.of Ω) ⟶ X, s' ≫ j ≠ s)
    (F : Sheaf (smallEtaleTopology X) A) :
    IsZero ((pointSmallEtale s).sheafFiber.obj ((j.smallEtaleExtensionByZero A).obj F)) := by
  let adj := (j.smallEtaleMap.sheafAdjunctionContinuous A (smallEtaleTopology X)
    (smallEtaleTopology Y)).comp (pointSmallEtale s).skyscraperSheafAdjunction
  rw [IsZero.iff_id_eq_zero]
  refine (adj.homEquiv F _).injective ?_
  ext W : 3
  exact Pi.hom_ext _ _ fun t ↦
    (hs (t.left ≫ W.unop.hom) ((Category.assoc _ _ _).trans (CategoryTheory.Over.w t))).elim

end Stalks

section Restriction

variable (A : Type*) [Category* A]
  [(j.smallEtaleMap.sheafPushforwardContinuous A (smallEtaleTopology X)
    (smallEtaleTopology Y)).IsRightAdjoint]

/-- **Restriction of an extension by zero.** For an étale monomorphism `j` (for instance an open
immersion), restricting `j_! F` back along `j` recovers `F`: `j^* j_! ≅ 𝟭`. It comes from
`j.smallEtaleMap ⋙ j.smallEtaleBaseChange ≅ 𝟭`. -/
noncomputable def smallEtaleExtensionByZeroCompSmallEtalePullbackIso :
    j.smallEtaleExtensionByZero A ⋙ j.smallEtalePullback A ≅ 𝟭 _ :=
  Functor.sheafPullbackComp' j.smallEtaleMapCompSmallEtaleBaseChangeIso A _ _ _ ≪≫
    Functor.sheafPullbackId' (Iso.refl _) A _

/-- The unit `F ⟶ j^* j_! F` of `j_! ⊣ j^*` is an isomorphism for an étale monomorphism `j`. -/
instance isIso_smallEtaleExtensionByZeroAdjunction_unit :
    IsIso (j.smallEtaleExtensionByZeroAdjunction A).unit :=
  (j.smallEtaleExtensionByZeroAdjunction A).isIso_unit_of_iso
    (j.smallEtaleExtensionByZeroCompSmallEtalePullbackIso A)

/-- **Extension by zero is fully faithful** along an étale monomorphism `j`. -/
noncomputable def fullyFaithfulSmallEtaleExtensionByZero :
    (j.smallEtaleExtensionByZero A).FullyFaithful :=
  (j.smallEtaleExtensionByZeroAdjunction A).fullyFaithfulLOfCompIsoId
    (j.smallEtaleExtensionByZeroCompSmallEtalePullbackIso A)

end Restriction

/-- **Extension by zero of étale module sheaves is exact.** For an étale monomorphism `j` (for
instance an open immersion), `j_!` sends short exact sequences of étale sheaves of `Λ`-modules on
`X` to short exact sequences on `Y`. -/
theorem shortExact_map_smallEtaleExtensionByZero {Λ : Type u} [Ring Λ]
    {T : ShortComplex (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))} (hT : T.ShortExact) :
    (T.map (j.smallEtaleExtensionByZero (ModuleCat.{u} Λ))).ShortExact :=
  hT.map_of_exact _

end Mono

/-- **Extension by zero vanishes off the image.** For an étale `j : X ⟶ Y` and a morphism
`g : Z ⟶ Y` whose image is disjoint from the image of `j`, the pullback along `g` of the extension
by zero `j_! F` of an étale sheaf of `Λ`-modules is zero: all its stalks vanish. -/
theorem isZero_smallEtalePullback_smallEtaleExtensionByZero_obj {Z : Scheme.{u}} (g : Z ⟶ Y)
    (hg : Disjoint (Set.range g) (Set.range j)) {Λ : Type u} [Ring Λ]
    [(j.smallEtaleMap.sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology X)
      (smallEtaleTopology Y)).IsRightAdjoint]
    (F : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) :
    IsZero ((g.smallEtalePullback (ModuleCat.{u} Λ)).obj
      ((j.smallEtaleExtensionByZero (ModuleCat.{u} Λ)).obj F)) := by
  set G := (g.smallEtalePullback (ModuleCat.{u} Λ)).obj
    ((j.smallEtaleExtensionByZero (ModuleCat.{u} Λ)).obj F)
  have hG (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z) :
      IsZero ((TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s).obj G) :=
    IsZero.of_iso (j.isZero_sheafFiber_smallEtaleExtensionByZero_obj _ (fun s' h ↦
        Set.disjoint_left.mp hg ⟨s default, rfl⟩
          ⟨s' default, by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]⟩) F)
      ((g.smallEtalePullbackCompEtaleStalkIso Λ s).app _)
  have : IsIso (0 : G ⟶ G) :=
    TauCeti.AlgebraicGeometry.Scheme.isIso_of_forall_isIso_etaleStalk _ fun Ω _ _ s ↦
      (hG Ω s).isIso (hG Ω s) _
  exact ((isIsoZero_iff_source_target_isZero G G).mp this).1

end AlgebraicGeometry.Scheme.Hom
