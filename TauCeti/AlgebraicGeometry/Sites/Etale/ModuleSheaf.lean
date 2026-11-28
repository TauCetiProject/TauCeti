/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable
public import TauCeti.AlgebraicGeometry.Sites.Etale.LocallyConstant
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Module

import Mathlib.Algebra.BigOperators.Pi
import TauCeti.AlgebraicGeometry.Sites.Etale.Covering

/-!
# Étale sheaves of modules: geometric stalks and finite lisse sheaves

Let `S` be a scheme and `Λ` a ring. This file studies sheaves of `Λ`-modules on the small étale
site of `S` through their stalks at geometric points, and defines finite lisse sheaves.

A geometric point `s : Spec Ω ⟶ S`, with `Ω` a separably closed field, is a point
`AlgebraicGeometry.Scheme.pointSmallEtale s` of the small étale site (Mathlib). Its fibre
functor on sheaves of `Λ`-modules is the stalk functor
`TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s`, with values in `Λ`-modules. Its underlying set
is the stalk of the underlying sheaf of sets. The stalk functor is exact, and the stalks at a
family of geometric points meeting every point of `S` are jointly conservative, because the
corresponding points of the étale site form a conservative family (Mathlib's
`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale`). Hence exactness of a sequence of étale
sheaves of modules can be tested on stalks. For a morphism of schemes `f : X ⟶ Y`, the inverse
image functor `f.smallEtalePullback (ModuleCat.{u} Λ)` commutes with `etaleStalk` up to natural
isomorphism (`AlgebraicGeometry.Scheme.Hom.smallEtalePullbackCompEtaleStalkIso`) and preserves
short exact sequences (`AlgebraicGeometry.Scheme.Hom.shortExact_map_smallEtalePullback`).

A sheaf of `Λ`-modules is *finite lisse* if it is étale locally isomorphic to the constant sheaf
on a finitely generated `Λ`-module (`CategoryTheory.Sheaf.IsFiniteLisse`); for a finite ring
`Λ` these are the étale locally constant sheaves with finite fibres. Its stalks are finitely
generated `Λ`-modules, and being finite lisse is stable under pullback along arbitrary morphisms of
schemes (`CategoryTheory.Sheaf.IsFiniteLisse.smallEtalePullback`) and satisfies étale and Zariski
descent (`CategoryTheory.Sheaf.isFiniteLisse_iff_of_etaleCover`,
`CategoryTheory.Sheaf.isFiniteLisse_iff_of_openCover`). No invertibility hypothesis on `Λ` is
needed.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.etaleStalk`: the stalk at a geometric point, as a functor to
  `Λ`-modules.
* `TauCeti.AlgebraicGeometry.Scheme.etaleStalkCompForgetIso`: the underlying set of the stalk is
  the stalk of the underlying sheaf of sets.
* `TauCeti.AlgebraicGeometry.Scheme.shortExact_map_etaleStalk`: stalks preserve short exact
  sequences.
* `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackCompEtaleStalkIso`,
  `AlgebraicGeometry.Scheme.Hom.shortExact_map_smallEtalePullback`: étale inverse image of
  module sheaves commutes with geometric stalks and preserves short exact sequences.
* `TauCeti.AlgebraicGeometry.Scheme.jointlyReflectIsomorphisms_etaleStalk`,
  `TauCeti.AlgebraicGeometry.Scheme.isIso_of_forall_isIso_etaleStalk`: stalks at geometric points
  whose images cover `S` jointly reflect isomorphisms.
* `CategoryTheory.ShortComplex.exact_iff_exact_map_etaleStalk`,
  `CategoryTheory.ShortComplex.shortExact_iff_shortExact_map_etaleStalk`: a short complex of étale
  sheaves of modules is (short) exact if and only if it is so on the stalks at a family of
  geometric points whose images cover `S`; `exact_iff_forall_exact_map_etaleStalk` and
  `shortExact_iff_forall_shortExact_map_etaleStalk` use all geometric points.
* `CategoryTheory.Sheaf.IsFiniteLisse`: finite lisse étale sheaves of modules.
* `CategoryTheory.Sheaf.IsFiniteLisse.finite_etaleStalk`: the stalks of a finite lisse sheaf are
  finitely generated.
* `CategoryTheory.Sheaf.isFiniteLisse_constantSheaf_iff`: on a scheme with a geometric point, the
  constant sheaf on a `Λ`-module `M` is finite lisse exactly when `M` is finitely generated.
* `CategoryTheory.Sheaf.isFiniteLisse_iff`,
  `CategoryTheory.Sheaf.IsFiniteLisse.smallEtalePullback`,
  `CategoryTheory.Sheaf.isFiniteLisse_iff_of_etaleCover`,
  `CategoryTheory.Sheaf.isFiniteLisse_iff_of_openCover`: geometric characterization, base-change
  stability, and étale/Zariski descent for finite lisse sheaves.
* `CategoryTheory.Sheaf.exists_etaleCover_map_constantSheaf`,
  `CategoryTheory.Sheaf.exists_etaleCover_lift_constantSheaf_of_projective`: étale-local
  constancy of morphisms between constant sheaves and local lifting from finitely generated
  projective modules along epimorphisms onto constant sheaves.

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §3, for stalks at geometric
  points, and Exposé IX, §2, for locally constant sheaves.
* The Stacks Project, Section 59.29, Stalks of étale sheaves, and Section 59.64, Locally constant
  sheaves.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (Λ : Type u) [Ring Λ]

section Stalk

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The stalk at the geometric point `s : Spec Ω ⟶ S` of an étale sheaf of `Λ`-modules, as a
`Λ`-module: the fibre functor of the point `pointSmallEtale s` of the small étale site. -/
noncomputable abbrev etaleStalk :
    Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
  (pointSmallEtale s).sheafFiber

/-- The underlying set of the stalk of an étale sheaf of `Λ`-modules at a geometric point is the
stalk of its underlying sheaf of sets. -/
noncomputable def etaleStalkCompForgetIso :
    etaleStalk Λ s ⋙ CategoryTheory.forget (ModuleCat.{u} Λ) ≅
      sheafCompose (smallEtaleTopology S) (CategoryTheory.forget (ModuleCat.{u} Λ)) ⋙
        (pointSmallEtale s).sheafFiber :=
  ((pointSmallEtale s).sheafFiberCompIso (CategoryTheory.forget (ModuleCat.{u} Λ))).symm

variable {Λ}

/-- Under the inverse of `etaleStalkCompForgetIso`, the germ of a section of the underlying sheaf
of sets is the underlying element of its germ as a section of the sheaf of `Λ`-modules. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toPresheafFiber_etaleStalkCompForgetIso_inv_app
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) (U : S.Etale)
    (u : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtale s).toPresheafFiber U u (F.obj ⋙ CategoryTheory.forget (ModuleCat.{u} Λ)) ≫
        (etaleStalkCompForgetIso Λ s).inv.app F =
      (CategoryTheory.forget (ModuleCat.{u} Λ)).map
        ((pointSmallEtale s).toPresheafFiber U u F.obj) :=
  (pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app _ U u F.obj

/-- Under `etaleStalkCompForgetIso`, the underlying element of the germ of a section of a sheaf of
`Λ`-modules is its germ as a section of the underlying sheaf of sets. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toPresheafFiber_etaleStalkCompForgetIso_hom_app
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) (U : S.Etale)
    (u : (pointSmallEtale s).fiber.obj U) :
    (CategoryTheory.forget (ModuleCat.{u} Λ)).map
        ((pointSmallEtale s).toPresheafFiber U u F.obj) ≫ (etaleStalkCompForgetIso Λ s).hom.app F =
      (pointSmallEtale s).toPresheafFiber U u (F.obj ⋙ CategoryTheory.forget (ModuleCat.{u} Λ)) :=
  ((Iso.comp_inv_eq ((etaleStalkCompForgetIso Λ s).app F)).1
    (toPresheafFiber_etaleStalkCompForgetIso_inv_app s F U u)).symm

/-- **Stalks are exact.** The stalk functor at a geometric point sends short exact sequences of
étale sheaves of `Λ`-modules to short exact sequences of `Λ`-modules. -/
theorem shortExact_map_etaleStalk
    {T : ShortComplex (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))} (hT : T.ShortExact) :
    (T.map (etaleStalk Λ s)).ShortExact :=
  hT.map_of_exact _

end Stalk

section Conservative

variable {Λ}

/-- Stalks at a family of geometric points of `S` whose images cover `S` jointly reflect
isomorphisms of étale sheaves of `Λ`-modules. -/
theorem jointlyReflectIsomorphisms_etaleStalk {ι : Type*} {Ω : ι → Type u}
    [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)] (s : ∀ i, Spec (.of (Ω i)) ⟶ S)
    (hs : ⋃ i, Set.range (s i) = .univ) :
    JointlyReflectIsomorphisms fun i ↦ etaleStalk Λ (s i) where
  isIso f h :=
    have : ∀ Φ : (ObjectProperty.ofObj fun i ↦ pointSmallEtale (s i)).FullSubcategory,
        IsIso (Φ.obj.sheafFiber.map f) := by
      rintro ⟨_, ⟨i⟩⟩
      exact h i
    ((isConservative_pointSmallEtale s hs).jointlyReflectIsomorphisms (ModuleCat.{u} Λ)).isIso f

/-- **Stalks are conservative.** A morphism of étale sheaves of `Λ`-modules on `S` is an
isomorphism as soon as it induces isomorphisms on the stalks at all geometric points. -/
theorem isIso_of_forall_isIso_etaleStalk {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (φ : F ⟶ G) (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      IsIso ((etaleStalk Λ s).map φ)) :
    IsIso φ := by
  rw [((isConservativeFamilyOfPoints_pointSmallEtale' S).jointlyReflectIsomorphisms
    (ModuleCat.{u} Λ)).isIso_iff]
  rintro ⟨_, ⟨_⟩⟩
  exact h _ _

end Conservative

end TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme

/-- At a geometric point `s : Spec Ω ⟶ X`, the stalk of
`(f.smallEtalePullback (ModuleCat.{u} Λ)).obj F` as a `Λ`-module identifies naturally with the
stalk of `F` at `s ≫ f`. -/
noncomputable abbrev smallEtalePullbackCompEtaleStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type u) [Ring Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    f.smallEtalePullback (ModuleCat.{u} Λ) ⋙ etaleStalk Λ s ≅ etaleStalk Λ (s ≫ f) :=
  f.smallEtalePullbackCompSheafFiberIso (ModuleCat.{u} Λ) s

/-- **Inverse image of étale module sheaves is exact.** Pulling back along any morphism of schemes
`f : X ⟶ Y` sends short exact sequences of étale sheaves of `Λ`-modules on `Y` to short exact
sequences on `X`. -/
theorem shortExact_map_smallEtalePullback {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ : Type u} [Ring Λ]
    {T : ShortComplex (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))} (hT : T.ShortExact) :
    (T.map (f.smallEtalePullback (ModuleCat.{u} Λ))).ShortExact :=
  hT.map_of_exact _

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.ShortComplex

open TauCeti.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
  (T : ShortComplex (Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)))

/-- **Exactness is tested on stalks.** A short complex of étale sheaves of `Λ`-modules on `S` is
exact if and only if it is exact on the stalks at a family of geometric points whose images
cover `S`. -/
theorem exact_iff_exact_map_etaleStalk {ι : Type*} {Ω : ι → Type u} [∀ i, Field (Ω i)]
    [∀ i, IsSepClosed (Ω i)] (s : ∀ i, Spec (.of (Ω i)) ⟶ S)
    (hs : ⋃ i, Set.range (s i) = .univ) :
    T.Exact ↔ ∀ i, (T.map (etaleStalk Λ (s i))).Exact :=
  (jointlyReflectIsomorphisms_etaleStalk s hs).exact_iff T

/-- A short complex of étale sheaves of `Λ`-modules on `S` is short exact if and only if it is
short exact on the stalks at a family of geometric points whose images cover `S`. -/
theorem shortExact_iff_shortExact_map_etaleStalk {ι : Type*} {Ω : ι → Type u}
    [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)] (s : ∀ i, Spec (.of (Ω i)) ⟶ S)
    (hs : ⋃ i, Set.range (s i) = .univ) :
    T.ShortExact ↔ ∀ i, (T.map (etaleStalk Λ (s i))).ShortExact :=
  (jointlyReflectIsomorphisms_etaleStalk s hs).shortExact_iff T

/-- A short complex of étale sheaves of `Λ`-modules on `S` is exact if and only if it is exact on
the stalks at all geometric points. -/
theorem exact_iff_forall_exact_map_etaleStalk :
    T.Exact ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (T.map (etaleStalk Λ s)).Exact := by
  refine ⟨fun hT _ _ _ s ↦ hT.map _, fun h ↦ ?_⟩
  rw [((isConservativeFamilyOfPoints_pointSmallEtale' S).jointlyReflectIsomorphisms
    (ModuleCat.{u} Λ)).exact_iff]
  rintro ⟨_, ⟨_⟩⟩
  exact h _ _

/-- A short complex of étale sheaves of `Λ`-modules on `S` is short exact if and only if it is
short exact on the stalks at all geometric points. -/
theorem shortExact_iff_forall_shortExact_map_etaleStalk :
    T.ShortExact ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (T.map (etaleStalk Λ s)).ShortExact := by
  refine ⟨fun hT _ _ _ s ↦ shortExact_map_etaleStalk s hT, fun h ↦ ?_⟩
  rw [((isConservativeFamilyOfPoints_pointSmallEtale' S).jointlyReflectIsomorphisms
    (ModuleCat.{u} Λ)).shortExact_iff]
  rintro ⟨_, ⟨_⟩⟩
  exact h _ _

end CategoryTheory.ShortComplex

namespace CategoryTheory.Sheaf

open TauCeti.AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- An étale sheaf of `Λ`-modules on `S` is *finite lisse* if it is étale locally isomorphic to the
constant sheaf on a finitely generated `Λ`-module: every étale `S`-scheme is covered by étale
maps `V ⟶ U` over which the sheaf is the constant sheaf on a finitely generated module. -/
abbrev IsFiniteLisse (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) : Prop :=
  F.IsLocallyConstantIn (smallEtaleTopology S) (ModuleCat.isFG Λ)

/-- The constant étale sheaf on a finitely generated `Λ`-module is finite lisse. -/
theorem isFiniteLisse_constantSheaf (M : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M).IsFiniteLisse :=
  isLocallyConstantIn_constantSheaf (P := ModuleCat.isFG Λ) ‹_›

theorem IsFiniteLisse.of_iso {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (e : F ≅ G) (hF : F.IsFiniteLisse) : G.IsFiniteLisse :=
  IsLocallyConstantIn.of_iso e hF

/-- Being finite lisse is invariant under isomorphism of sheaves. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    fun F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ) ↦ F.IsFiniteLisse :=
  ⟨fun e h ↦ h.of_iso e⟩

/-- The stalks of a finite lisse étale sheaf of `Λ`-modules at geometric points are finitely
generated `Λ`-modules. -/
theorem IsFiniteLisse.finite_etaleStalk {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Module.Finite Λ ((etaleStalk Λ s).obj F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := IsLocallyConstantIn.exists_sheafFiber_iso hF (pointSmallEtale s)
  have := M.isFG_iff.1 hM
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- On a scheme with a geometric point, the constant étale sheaf on a `Λ`-module `M` is finite
lisse exactly when `M` is finitely generated: its stalk at the point is `M`. -/
theorem isFiniteLisse_constantSheaf_iff {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (M : ModuleCat.{u} Λ) :
    ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M).IsFiniteLisse ↔
      Module.Finite Λ M :=
  ⟨fun h ↦ have := h.finite_etaleStalk s
    .equiv ((pointSmallEtale s).sheafFiberConstantSheafIso M).toLinearEquiv,
    fun _ ↦ isFiniteLisse_constantSheaf M⟩

/-- An étale sheaf of `Λ`-modules on `S` is finite lisse as soon as it becomes isomorphic to
constant sheaves on finitely generated `Λ`-modules along a jointly surjective family of étale
morphisms `u : ∀ i, U i ⟶ S`. -/
theorem IsFiniteLisse.of_etaleCover_constantSheaf
    {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)]
    (hu : ⋃ i, Set.range (u i) = .univ)
    (h : ∀ i, ∃ M : ModuleCat.{u} Λ, Module.Finite Λ M ∧
      Nonempty (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj F ≅
        (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M)) :
    F.IsFiniteLisse :=
  IsLocallyConstantIn.of_etaleCover_constantSheaf u hu h

/-- **Geometric characterization of finite lisse sheaves.** An étale sheaf of `Λ`-modules on `S` is
finite lisse if and only if there exists a `Type u`-indexed jointly surjective family of étale
morphisms `u : ∀ i, U i ⟶ S` over each of which `(u i)^* F` is isomorphic to the constant sheaf on
a finitely generated `Λ`-module. -/
theorem isFiniteLisse_iff (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :
    F.IsFiniteLisse ↔
      ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
        (⋃ i, Set.range (u i) = .univ) ∧
          ∀ i, ∃ M : ModuleCat.{u} Λ, Module.Finite Λ M ∧
            Nonempty (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj F ≅
              (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj M) :=
  F.isLocallyConstantIn_smallEtaleTopology_iff _

/-- **Stability of finite lisse sheaves under base change.** Pulling back a finite lisse étale
sheaf of `Λ`-modules along any morphism of schemes `f : X ⟶ Y` yields a finite lisse sheaf on
`X`. -/
theorem IsFiniteLisse.smallEtalePullback {X Y : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)} (hF : F.IsFiniteLisse) (f : X ⟶ Y) :
    ((f.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  IsLocallyConstantIn.smallEtalePullback hF f

section Descent

variable (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))

/-- **Étale descent for finite lisse sheaves.** An étale sheaf of `Λ`-modules on `S` is finite
lisse if and only if its pullbacks along a jointly surjective étale family `u : ∀ i, U i ⟶ S` are
finite lisse. -/
theorem isFiniteLisse_iff_of_etaleCover {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)] (hu : ⋃ i, Set.range (u i) = .univ) :
    F.IsFiniteLisse ↔ ∀ i, (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  F.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover _ u hu

/-- An étale sheaf of `Λ`-modules on `S` is finite lisse if and only if its pullback along a
surjective étale morphism `u : U ⟶ S` is finite lisse. -/
theorem isFiniteLisse_iff_of_etale_of_surjective {U : Scheme.{u}} (u : U ⟶ S)
    [Etale u] [Surjective u] :
    F.IsFiniteLisse ↔ ((u.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  F.isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_surjective _ u

/-- **Zariski descent for finite lisse sheaves.** An étale sheaf of `Λ`-modules on `S` is finite
lisse if and only if its restrictions to the pieces of an open cover `𝒰 : S.OpenCover` are finite
lisse. -/
theorem isFiniteLisse_iff_of_openCover (𝒰 : S.OpenCover) :
    F.IsFiniteLisse ↔ ∀ i, (((𝒰.f i).smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  F.isLocallyConstantIn_smallEtaleTopology_iff_of_openCover _ 𝒰

end Descent

section ConstantSheaf

/-- Any morphism `φ : const M ⟶ const N` of constant étale sheaves of `Λ`-modules on `S` with
`M` finitely generated comes étale-locally from a constant `Λ`-linear map `M ⟶ N`. -/
theorem exists_etaleCover_map_constantSheaf
    {M N : ModuleCat.{u} Λ} [Module.Finite Λ M]
    (φ : (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M ⟶
      (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ f : M ⟶ N,
          ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) M).inv ≫
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
              (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map f := by
  obtain ⟨R, hR, hRg⟩ := exists_mem_overPullback_map_eq_of_iso (J := smallEtaleTopology S)
    φ (Y := Etale.mk (𝟙 S)) (Iso.refl _) (Iso.refl _)
  obtain ⟨ι, U, u, hu_et, _, hgR, hcov⟩ := exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  have := hu_et i
  obtain ⟨gi, hgi⟩ := hgR i
  obtain ⟨f, hf⟩ := hRg gi hgi
  have hrefl (G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) :
      (overIsoRestrict (Iso.refl (G.over (Etale.mk (𝟙 S)))) gi).hom = 𝟙 _ := by
    ext W : 3
    exact (overIsoRestrict_hom_hom_app (Iso.refl _) gi W).trans rfl
  rw [hrefl, hrefl, Category.comp_id, Category.id_comp] at hf
  let e := (Etale.mk (u i)).smallEtalePullbackIsoOver (ModuleCat.{u} Λ)
  have hpb : ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map φ =
      ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map
        ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map f) := by
    have h₁ := e.hom.naturality φ
    have h₂ := e.hom.naturality ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).map f)
    have h₃ := congrArg ((Etale.mk (u i)).overSheafEquiv (ModuleCat.{u} Λ)).functor.map hf
    exact (cancel_mono (e.hom.app _)).1 ((h₁.trans (congrArg (e.hom.app _ ≫ ·) h₃)).trans h₂.symm)
  exact ⟨f, by
    rw [hpb, Hom.smallEtalePullbackConstantSheafIso_hom_naturality, Iso.inv_hom_id_assoc]⟩

private theorem exists_etaleCover_lift_constantSheaf_fin
    {N : ModuleCat.{u} Λ} {a : ℕ}
    {E : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (g : E ⟶ (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) [Epi g]
    (πN : ModuleCat.of Λ (Fin a → Λ) ⟶ N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ h : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj
            (ModuleCat.of Λ (Fin a → Λ)) ⟶
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj E,
          h ≫ ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map g ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map πN := by
  let F₀ : ModuleCat.{u} Λ := ModuleCat.of Λ (Fin a → Λ)
  let n : Fin a → N := fun k ↦ πN (Pi.single k 1)
  let T_S : S.Etale := Etale.mk (𝟙 S)
  let R := ⨅ k : Fin a, Presheaf.imageSieve g.hom
    ((toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app (op T_S) (n k))
  have hloc : Presheaf.IsLocallySurjective (smallEtaleTopology S) g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := g)).2 inferInstance
  have hR : R ∈ smallEtaleTopology S T_S :=
    (smallEtaleTopology S).iInf_mem fun k ↦ Presheaf.imageSieve_mem (smallEtaleTopology S) g.hom _
  obtain ⟨ι, U, u, hu_et, _, hαR, hcov⟩ := exists_etaleCover_of_mem_smallEtaleTopology_terminal hR
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  have := hu_et i
  obtain ⟨αi, hαi⟩ := hαR i
  choose s hs using fun k : Fin a ↦ (iInf_le _ k : R ≤ _) _ hαi
  let T_U : (U i).Etale := Etale.mk (𝟙 (U i))
  let hterm_U : IsTerminal T_U :=
    IsTerminal.isTerminalOfObj (Etale.forget (U i)) _ CategoryTheory.Over.mkIdTerminal
  let s' : Fin a → (((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj E).obj.obj (op T_U) :=
    fun k ↦ (u i).evalUnitSelf E (s k)
  let h := ((constantSheafAdj (smallEtaleTopology (U i)) (ModuleCat.{u} Λ) hterm_U).homEquiv
    F₀ _).symm (ModuleCat.ofHom (Fintype.linearCombination Λ s'))
  refine ⟨h, ((constantSheafAdj (smallEtaleTopology (U i))
    (ModuleCat.{u} Λ) hterm_U).homEquiv F₀ _).injective ?_⟩
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, constantSheafAdj_homEquiv_map]
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  conv_lhs => rw [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_ofHom, Fintype.linearCombination_apply, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' c, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_smul, map_smul]
  refine congrArg (c k • ·) ?_
  have hsk := (hs k).trans (toSheafify_app_const_map_apply (smallEtaleTopology S) N αi.op (n k))
  simpa only [Functor.flip_obj_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ConcreteCategory.comp_apply, s'] using
    (u i).smallEtalePullback_map_comp_constantSheafIso_evalUnitSelf g hsk

/-- Given an epimorphism `g : E ⟶ const N` and a linear map `πN : F₀ ⟶ N` from a finitely
generated projective `Λ`-module `F₀`, there exists an étale cover of `S` over each piece of which
`πN` lifts along the pullback of `g` to `const F₀ ⟶ u^* E`. -/
theorem exists_etaleCover_lift_constantSheaf_of_projective
    {F₀ N : ModuleCat.{u} Λ} [Module.Projective Λ F₀] [Module.Finite Λ F₀]
    {E : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (g : E ⟶ (constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj N) [Epi g]
    (πN : F₀ ⟶ N) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
      (⋃ i, Set.range (u i) = .univ) ∧
        ∀ i, ∃ h : (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).obj F₀ ⟶
            ((u i).smallEtalePullback (ModuleCat.{u} Λ)).obj E,
          h ≫ ((u i).smallEtalePullback (ModuleCat.{u} Λ)).map g ≫
            ((u i).smallEtalePullbackConstantSheafIso (ModuleCat.{u} Λ) N).hom =
            (constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map πN := by
  obtain ⟨a, p, hp⟩ := Module.Finite.exists_fin' Λ F₀
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  obtain ⟨ι, U, u, hu_et, hcov, hlifts⟩ :=
    exists_etaleCover_lift_constantSheaf_fin g (ModuleCat.ofHom p ≫ πN)
  refine ⟨ι, U, u, hu_et, hcov, fun i ↦ ?_⟩
  obtain ⟨h, hh⟩ := hlifts i
  refine ⟨(constantSheaf (smallEtaleTopology (U i)) (ModuleCat.{u} Λ)).map (ModuleCat.ofHom s) ≫ h,
    ?_⟩
  rw [Category.assoc, hh, ← Functor.map_comp, ← Category.assoc, ← ModuleCat.ofHom_comp, hs,
    ModuleCat.ofHom_id, Category.id_comp]

end ConstantSheaf

end CategoryTheory.Sheaf
