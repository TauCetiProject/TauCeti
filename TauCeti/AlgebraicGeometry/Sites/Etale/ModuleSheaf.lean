/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import TauCeti.Algebra.Category.ModuleCat.ForgetCorepresentable
public import TauCeti.CategoryTheory.Sites.LocallyConstant

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
sheaves of modules can be tested on stalks.

A sheaf of `Λ`-modules is *finite lisse* if it is étale locally isomorphic to the constant sheaf
on a finitely generated `Λ`-module (`CategoryTheory.Sheaf.IsFiniteLisse`); for a finite ring
`Λ` these are the étale locally constant sheaves with finite fibres. Its stalks are finitely
generated `Λ`-modules. No invertibility hypothesis on `Λ` is needed.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.etaleStalk`: the stalk at a geometric point, as a functor to
  `Λ`-modules.
* `TauCeti.AlgebraicGeometry.Scheme.etaleStalkCompForgetIso`: the underlying set of the stalk is
  the stalk of the underlying sheaf of sets.
* `TauCeti.AlgebraicGeometry.Scheme.shortExact_map_etaleStalk`: stalks preserve short exact
  sequences.
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
  F.IsLocallyConstantIn (smallEtaleTopology S) fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M

/-- The constant étale sheaf on a finitely generated `Λ`-module is finite lisse. -/
theorem isFiniteLisse_constantSheaf (M : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    ((constantSheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).obj M).IsFiniteLisse :=
  isLocallyConstantIn_constantSheaf (P := fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M) ‹_›

theorem IsFiniteLisse.of_iso {F G : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (e : F ≅ G) (hF : F.IsFiniteLisse) : G.IsFiniteLisse :=
  IsLocallyConstantIn.of_iso e hF

/-- The stalks of a finite lisse étale sheaf of `Λ`-modules at geometric points are finitely
generated `Λ`-modules. -/
theorem IsFiniteLisse.finite_etaleStalk {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Module.Finite Λ ((etaleStalk Λ s).obj F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := IsLocallyConstantIn.exists_sheafFiber_iso hF (pointSmallEtale s)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end CategoryTheory.Sheaf
