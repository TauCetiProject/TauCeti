/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
public import TauCeti.AlgebraicGeometry.Sites.EtaleSepClosed

/-!
# Étale sheaves of modules: geometric stalks, pullback, and finite lisse sheaves

Let `S` be a scheme and `Λ` a ring. This file studies sheaves of `Λ`-modules on the small étale
site of `S` through their stalks at geometric points and pullback along scheme morphisms, and
develops the basic properties of finite lisse sheaves.

A geometric point `s : Spec Ω ⟶ S`, with `Ω` a separably closed field, is a point
`AlgebraicGeometry.Scheme.pointSmallEtale s` of the small étale site (Mathlib). Its fibre
functor on sheaves of `Λ`-modules is the stalk functor
`TauCeti.AlgebraicGeometry.Scheme.etaleStalk Λ s`, with values in `Λ`-modules. Its underlying set
is the stalk of the underlying sheaf of sets, and it identifies naturally with pulling back along
`s` to `Spec Ω` and taking global sections
(`TauCeti.AlgebraicGeometry.Scheme.smallEtalePullbackCompΓIsoEtaleStalk`). For any morphism of
schemes `f : X ⟶ Y`, the stalk of `f^* F` at `x` identifies with the stalk of `F` at `x ≫ f`, and
both `etaleStalk Λ s` and `f.smallEtalePullback (ModuleCat.{u} Λ)` preserve short exact sequences.
Stalks at a family of geometric points meeting every point of `S` are jointly conservative
(Mathlib's `AlgebraicGeometry.Scheme.isConservative_pointSmallEtale`), so exactness of a sequence
of étale sheaves of modules can be tested on stalks.

A sheaf of `Λ`-modules is *finite lisse* if it is étale locally isomorphic to the constant sheaf
on a finitely generated `Λ`-module (`CategoryTheory.Sheaf.IsFiniteLisse`); for a finite ring
`Λ` these are the étale locally constant sheaves with finite fibres. Finite lisse sheaves contain
`0`, are closed under binary biproducts and arbitrary base change, and have finitely generated
stalks; the predicate `IsFiniteLisse` is étale local along jointly surjective étale families (in
particular étale covers and surjective étale morphisms). Over the spectrum of a separably closed
field `Ω`, an étale sheaf of `Λ`-modules is finite lisse if and only if its module of global
sections is finitely generated over `Λ` (equivalently, it is globally isomorphic to a constant
sheaf on a finitely generated `Λ`-module). No invertibility hypothesis on `Λ` is needed.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.etaleStalk`: the stalk at a geometric point, as a functor to
  `Λ`-modules.
* `TauCeti.AlgebraicGeometry.Scheme.etaleStalkCompForgetIso`: the underlying set of the stalk is
  the stalk of the underlying sheaf of sets.
* `TauCeti.AlgebraicGeometry.Scheme.smallEtalePullbackCompEtaleStalkIso`,
  `TauCeti.AlgebraicGeometry.Scheme.smallEtalePullbackCompΓIsoEtaleStalk`: stalk comparison
  `(f^* F)_x ≅ F_{x ≫ f}` and identification `Γ(Spec Ω, s^* F) ≅ F_s`.
* `TauCeti.AlgebraicGeometry.Scheme.shortExact_map_etaleStalk`,
  `AlgebraicGeometry.Scheme.Hom.shortExact_map_smallEtalePullback`: geometric stalks and
  scheme-morphism pullbacks preserve short exact sequences of étale module sheaves.
* `TauCeti.AlgebraicGeometry.Scheme.jointlyReflectIsomorphisms_etaleStalk`,
  `TauCeti.AlgebraicGeometry.Scheme.isIso_of_forall_isIso_etaleStalk`: stalks at geometric points
  whose images cover `S` jointly reflect isomorphisms.
* `CategoryTheory.ShortComplex.exact_iff_exact_map_etaleStalk`,
  `CategoryTheory.ShortComplex.shortExact_iff_shortExact_map_etaleStalk`: a short complex of étale
  sheaves of modules is (short) exact if and only if it is so on the stalks at a family of
  geometric points whose images cover `S`; `exact_iff_forall_exact_map_etaleStalk` and
  `shortExact_iff_forall_shortExact_map_etaleStalk` use all geometric points.
* `CategoryTheory.Sheaf.IsFiniteLisse`: finite lisse étale sheaves of modules, closed under zero
  (`CategoryTheory.Sheaf.isFiniteLisse_zero`), binary biproducts
  (`CategoryTheory.Sheaf.IsFiniteLisse.biprod`), and scheme base change
  (`CategoryTheory.Sheaf.IsFiniteLisse.smallEtalePullback`).
* `CategoryTheory.Sheaf.isFiniteLisse_iff_of_etale_of_iUnion_range_eq_univ`,
  `CategoryTheory.Sheaf.isFiniteLisse_iff_of_etale_cover`,
  `CategoryTheory.Sheaf.isFiniteLisse_iff_of_etale_of_surjective`: étale locality of
  `IsFiniteLisse`.
* `CategoryTheory.Sheaf.isFiniteLisse_iff_finite_Γ_of_isSepClosed`,
  `CategoryTheory.Sheaf.isFiniteLisse_iff_exists_finite_iso_constantSheaf_of_isSepClosed`,
  `CategoryTheory.Sheaf.isFiniteLisse_smallEtalePullback_iff_finite_etaleStalk`: characterization
  of finite lisse sheaves on a separably closed field and after pullback to a geometric point.

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé VIII, §3, for stalks at geometric
  points, and Exposé IX, §2, for locally constant sheaves.
* The Stacks Project, Section 59.29, Stalks of étale sheaves, and Section 59.64, Locally constant
  sheaves.
-/

public section

universe u

open CategoryTheory Limits ZeroObject Opposite AlgebraicGeometry Scheme

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

section Pullback

variable {X Y : Scheme.{u}}

/-- For a morphism of schemes `f : X ⟶ Y` and a geometric point `x : Spec Ω ⟶ X`, the stalk of
`f^* F` at `x` identifies naturally with the stalk of `F` at `x ≫ f` in `ModuleCat.{u} Λ`. -/
noncomputable abbrev smallEtalePullbackCompEtaleStalkIso (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    f.smallEtalePullback (ModuleCat.{u} Λ) ⋙ etaleStalk Λ x ≅ etaleStalk Λ (x ≫ f) :=
  f.smallEtalePullbackCompSheafFiberIso x (ModuleCat.{u} Λ)

/-- Pulling an étale sheaf of `Λ`-modules on `S` back along a geometric point `s : Spec Ω ⟶ S` and
taking global sections over `Spec Ω` recovers the geometric stalk at `s`. -/
noncomputable abbrev smallEtalePullbackCompΓIsoEtaleStalk
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    s.smallEtalePullback (ModuleCat.{u} Λ) ⋙
        Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ) ≅
      etaleStalk Λ s :=
  s.smallEtalePullbackCompΓIsoSheafFiber (ModuleCat.{u} Λ)

variable {Λ} in
/-- Under the inverse of `smallEtalePullbackCompΓIsoEtaleStalk`, the germ at `v` of a section of
`F` over `V : S.Etale` is obtained by applying the `(s^*, s_*)` unit over `V`, restricting along
`s.smallEtaleBaseChangeSection V v` to `Spec Ω`, and identifying sections over `𝟙 (Spec Ω)` with
global sections. -/
@[reassoc, elementwise nosimp]
theorem toPresheafFiber_smallEtalePullbackCompΓIsoEtaleStalk_inv_app
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) (V : S.Etale)
    (v : (pointSmallEtale s).fiber.obj V) :
    (pointSmallEtale s).toPresheafFiber V v F.obj ≫
        (smallEtalePullbackCompΓIsoEtaleStalk Λ s).inv.app F =
      ((s.smallEtaleAdjunction (ModuleCat.{u} Λ)).unit.app F).hom.app (op V) ≫
        ((s.smallEtalePullback (ModuleCat.{u} Λ)).obj F).obj.map
          (s.smallEtaleBaseChangeSection V v).op ≫
        (Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u} Λ) (Etale.mkIdTerminal _)).inv.app
          ((s.smallEtalePullback (ModuleCat.{u} Λ)).obj F) :=
  s.toPresheafFiber_smallEtalePullbackCompΓIsoSheafFiber_inv_app (ModuleCat.{u} Λ) F V v

end Pullback

end TauCeti.AlgebraicGeometry.Scheme

/-- **Pullback of étale sheaves of modules is exact.** Inverse image along any morphism of schemes
`f : X ⟶ Y` preserves short exact sequences of étale sheaves of `Λ`-modules. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.shortExact_map_smallEtalePullback
    {X Y : Scheme.{u}} {Λ : Type u} [Ring Λ] (f : X ⟶ Y)
    {T : ShortComplex (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))} (hT : T.ShortExact) :
    (T.map (f.smallEtalePullback (ModuleCat.{u} Λ))).ShortExact :=
  hT.map_of_exact _

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

variable {S X Y : Scheme.{u}} {Λ : Type u} [Ring Λ]

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

/-- The zero étale sheaf of `Λ`-modules is finite lisse. -/
theorem isFiniteLisse_zero :
    (0 : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)).IsFiniteLisse := by
  have : Subsingleton (0 : ModuleCat.{u} Λ) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero _)
  exact isLocallyConstantIn_zero (P := fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M) inferInstance

/-- Binary biproducts of finite lisse étale sheaves of `Λ`-modules are finite lisse. -/
theorem IsFiniteLisse.biprod {F₁ F₂ : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (h₁ : F₁.IsFiniteLisse) (h₂ : F₂.IsFiniteLisse) :
    (F₁ ⊞ F₂).IsFiniteLisse :=
  IsLocallyConstantIn.biprod (P := fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M)
    (fun M₁ M₂ _ _ ↦ Module.Finite.equiv (ModuleCat.biprodIsoProd M₁ M₂).symm.toLinearEquiv) h₁ h₂

/-- The stalks of a finite lisse étale sheaf of `Λ`-modules at geometric points are finitely
generated `Λ`-modules. -/
theorem IsFiniteLisse.finite_etaleStalk {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Module.Finite Λ ((etaleStalk Λ s).obj F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := IsLocallyConstantIn.exists_sheafFiber_iso hF (pointSmallEtale s)
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- **Base-change stability of finite lisse sheaves.** Pulling a finite lisse étale sheaf of
`Λ`-modules back along any morphism of schemes `f : X ⟶ Y` yields a finite lisse sheaf on `X`. -/
theorem IsFiniteLisse.smallEtalePullback {F : Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)}
    (hF : F.IsFiniteLisse) (f : X ⟶ Y) :
    ((f.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  IsLocallyConstantIn.smallEtalePullback hF f

/-- **Étale locality of `IsFiniteLisse`.** For a jointly surjective family of étale morphisms
`g i : U i ⟶ S`, an étale sheaf of `Λ`-modules `F` on `S` is finite lisse if and only if each
pullback `(g i)^* F` is finite lisse on `U i`. -/
theorem isFiniteLisse_iff_of_etale_of_iUnion_range_eq_univ
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))
    {ι : Type*} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ S) [∀ i, AlgebraicGeometry.Etale (g i)]
    (hg : ⋃ i, Set.range (g i) = .univ) :
    F.IsFiniteLisse ↔ ∀ i, (((g i).smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_iUnion_range_eq_univ F g hg

/-- Being finite lisse can be tested on any étale cover of `S`. -/
theorem isFiniteLisse_iff_of_etale_cover
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))
    (𝒰 : S.Cover (Scheme.precoverage @AlgebraicGeometry.Etale)) :
    F.IsFiniteLisse ↔
      ∀ i : 𝒰.I₀, (((𝒰.f i).smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  isLocallyConstantIn_smallEtaleTopology_iff_of_etale_cover F 𝒰

/-- Being finite lisse can be tested after pullback along any surjective étale morphism
`g : X ⟶ S`. -/
theorem isFiniteLisse_iff_of_etale_of_surjective
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))
    (g : X ⟶ S) [AlgebraicGeometry.Etale g] [Surjective g] :
    F.IsFiniteLisse ↔ ((g.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_surjective F g

section SepClosed

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

private lemma isClosedUnderIsomorphisms_finite :
    ObjectProperty.IsClosedUnderIsomorphisms (fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M) :=
  ⟨fun e _ ↦ Module.Finite.equiv e.toLinearEquiv⟩

/-- **Finite lisse sheaves on a separably closed field.** Over `Spec Ω` with `Ω` separably closed,
an étale sheaf of `Λ`-modules is finite lisse if and only if its module of global sections is
finitely generated over `Λ`. -/
theorem isFiniteLisse_iff_finite_Γ_of_isSepClosed
    (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)) :
    F.IsFiniteLisse ↔
      Module.Finite Λ ((Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)).obj F) :=
  have := isClosedUnderIsomorphisms_finite (Λ := Λ)
  isLocallyConstantIn_iff_prop_Γ_obj (fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M) F

/-- Over `Spec Ω` with `Ω` separably closed, an étale sheaf of `Λ`-modules is finite lisse if and
only if it is globally isomorphic to the constant sheaf on a finitely generated `Λ`-module. -/
theorem isFiniteLisse_iff_exists_finite_iso_constantSheaf_of_isSepClosed
    (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)) :
    F.IsFiniteLisse ↔
      ∃ (M : ModuleCat.{u} Λ) (_ : Module.Finite Λ M),
        Nonempty (F ≅ (constantSheaf (smallEtaleTopology (Spec (.of Ω)))
          (ModuleCat.{u} Λ)).obj M) :=
  (isLocallyConstantIn_iff_exists_iso_constantSheaf
    (fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M) F).trans
    ⟨fun ⟨M, hM, e⟩ ↦ ⟨M, hM, e⟩, fun ⟨M, hM, e⟩ ↦ ⟨M, hM, e⟩⟩

/-- For any étale sheaf of `Λ`-modules `F` on `S` and any geometric point `s : Spec Ω ⟶ S`, the
pullback `s^* F` on `Spec Ω` is finite lisse if and only if the geometric stalk `F_s` is a finitely
generated `Λ`-module. -/
theorem isFiniteLisse_smallEtalePullback_iff_finite_etaleStalk
    (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)) (s : Spec (.of Ω) ⟶ S) :
    ((s.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse ↔
      Module.Finite Λ ((etaleStalk Λ s).obj F) :=
  have := isClosedUnderIsomorphisms_finite (Λ := Λ)
  isLocallyConstantIn_smallEtalePullback_iff_prop_sheafFiber_obj s
    (fun M : ModuleCat.{u} Λ ↦ Module.Finite Λ M) F

end SepClosed

end CategoryTheory.Sheaf
