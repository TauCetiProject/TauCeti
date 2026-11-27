/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.DerivedHom
public import TauCeti.Algebra.Homology.InternalHomComplex.Homotopy
public import TauCeti.Algebra.Homology.InternalHomComplex.KInjective

/-!
# The derived internal Hom of unbounded complexes

Let `C` be a closed monoidal abelian category with countable products in which every cochain
complex, with no boundedness assumption, has a K-injective replacement; for instance the
category of `𝒪_X`-modules on a scheme `X`. The derived internal Hom
`TauCeti.derivedInternalHom C : D(C)ᵒᵖ ⥤ D(C) ⥤ D(C)` sends `K` and `L` to the internal Hom
complex `CochainComplex.internalHomComplex I J` between their K-injective replacements `I` and `J`.
It is functorial in both variables because the replacement functor
`TauCeti.kInjectiveReplacement` is, and because the internal Hom complex descends to homotopy
categories (`TauCeti.internalHomComplexHomotopyFunctor`).

The derived internal Hom `R𝓗om(K, L)` of [Stacks, Section 20.42 (08DH)] is the internal Hom
complex `𝓗om^•(K, J)` from the complex `K` itself into a K-injective replacement `J` of `L`.
Replacing `K` by `I` as well does not change it when `𝓗om^•(-, J)` sends quasi-isomorphisms to
quasi-isomorphisms. This holds when `C` has a separating family of objects `G` for which `- ⊗ G`
preserves acyclic complexes (`TauCeti.quasiIso_internalHomComplexPrecomp`), as the extensions by
zero `j_! 𝒪_U` of the structure sheaves of opens do for `C = X.Modules`. Under this hypothesis
`TauCeti.derivedInternalHomQObjObjIso` identifies `R𝓗om(K, L)` with `𝓗om^•(K, J)`.

The global sections `Hom(𝟙, -)` of the internal Hom complex `𝓗om^•(I, J)` representing
`R𝓗om(K, L)` form the Hom complex of `I` and `J`, which represents the derived Hom complex
`TauCeti.derivedHom ℤ C` (`TauCeti.globalSectionsDerivedInternalHomIso`). Its cohomology is
therefore the group of morphisms `K ⟶ L⟦n⟧` in the derived category
(`TauCeti.globalSectionsDerivedInternalHomHomologyAddEquiv`).

## Main definitions

* `TauCeti.derivedInternalHom`: the derived internal Hom bifunctor.
* `TauCeti.derivedInternalHomQObjObjIso`: given a separating family of objects `G` for which
  `- ⊗ G` preserves acyclic complexes, `R𝓗om(K, L)` is the internal Hom complex from `K` into the
  K-injective replacement of `L`.
* `TauCeti.derivedInternalHomObjIsoOfQuasiIso`: under the same hypothesis, `R𝓗om(L, -)` is
  computed by the internal Hom complex out of any complex with a quasi-isomorphism to the
  K-injective replacement of `L`.
* `TauCeti.globalSectionsDerivedInternalHomIso`: the global sections of the internal Hom complex
  representing `R𝓗om(K, L)` represent the derived Hom complex `RHom(K, L)`.
* `TauCeti.globalSectionsDerivedInternalHomHomologyAddEquiv`: their `n`-th cohomology is
  `K ⟶ L⟦n⟧`.

## References

* [Stacks Project, Section 20.42 (08DH)](https://stacks.math.columbia.edu/tag/08DH) and
  [Stacks Project, Section 21.35 (08J7)](https://stacks.math.columbia.edu/tag/08J7).
* The construction follows `TauCeti.derivedHom` for the `R`-linear Hom complex.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory DerivedCategory CochainComplex Opposite

namespace TauCeti

universe w' w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [HasCountableProducts C] [HasKInjectiveResolutions C]
  [HasDerivedCategory.{w} C]

/-- The derived internal Hom `R𝓗om(K, L)` of objects `K` and `L` of the derived category of a
closed monoidal abelian category `C`: the internal Hom complex between the K-injective
replacements of `K` and `L`. -/
-- Expose the composite so that its values on objects and morphisms have computed types.
@[expose]
def derivedInternalHom : (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory C ⥤ DerivedCategory C :=
  (kInjectiveReplacement C).op ⋙ internalHomComplexHomotopyFunctor C ⋙
    (Functor.whiskeringLeft _ _ _).obj (kInjectiveReplacement C) ⋙
      (Functor.whiskeringRight _ _ _).obj Qh

variable {C}

/-- The derived internal Hom is the internal Hom complex between the K-injective replacements. -/
lemma derivedInternalHom_obj_obj (K L : DerivedCategory C) :
    ((derivedInternalHom C).obj (op K)).obj L =
      Qh.obj ((HomotopyCategory.quotient _ _).obj (internalHomComplex
        ((kInjectiveReplacement C).obj K).as ((kInjectiveReplacement C).obj L).as)) :=
  (rfl)

/-- The derived internal Hom acts on morphisms of its second variable by postcomposition with the
induced map of K-injective replacements. -/
lemma derivedInternalHom_obj_map (K : DerivedCategory C) {L L' : DerivedCategory C}
    (g : L ⟶ L') :
    ((derivedInternalHom C).obj (op K)).map g =
      Qh.map (((internalHomComplexHomotopyFunctor C).obj
        (op ((kInjectiveReplacement C).obj K))).map ((kInjectiveReplacement C).map g)) :=
  (rfl)

/-- The derived internal Hom acts on morphisms of its first variable by precomposition with the
induced map of K-injective replacements. -/
lemma derivedInternalHom_map_app {K K' : DerivedCategory C} (f : K' ⟶ K) (L : DerivedCategory C) :
    ((derivedInternalHom C).map f.op).app L =
      Qh.map (((internalHomComplexHomotopyFunctor C).map
        ((kInjectiveReplacement C).map f).op).app ((kInjectiveReplacement C).obj L)) :=
  (rfl)

/-- Let `C` have a separating family `P` of objects `G` for which `- ⊗ G` preserves acyclic
complexes. Then the derived internal Hom `R𝓗om(K, L)` of a cochain complex `K` is the internal
Hom complex `𝓗om^•(K, J)` from `K` itself into the K-injective replacement `J` of `L`, as in
[Stacks, Section 20.42 (08DH)]. The isomorphism is induced by a quasi-isomorphism from `K` to its
K-injective replacement. -/
def derivedInternalHomQObjObjIso {P : ObjectProperty C} (hP : P.IsSeparating)
    (hPacyclic : ∀ G, P G → ∀ X : CochainComplex C ℤ, X.Acyclic →
      (((tensorRight G).mapHomologicalComplex _).obj X).Acyclic)
    (K : CochainComplex C ℤ) (L : DerivedCategory C) :
    ((derivedInternalHom C).obj (op (Q.obj K))).obj L ≅
      Q.obj (internalHomComplex K ((kInjectiveReplacement C).obj L).as) :=
  let s := (HomotopyCategory.quotient _ _).preimage
    ((kInjectiveReplacementAdjunction C).unit.app ((HomotopyCategory.quotient _ _).obj K))
  have := quasiIso_of_quotient_map_eq_kInjectiveReplacementAdjunction_unit_app s
    ((HomotopyCategory.quotient _ _).map_preimage _)
  have hs : IsIso (Qh.map ((HomotopyCategory.quotient _ _).map
      (internalHomComplexPrecomp s ((kInjectiveReplacement C).obj L).as))) := by
    rw [isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    exact quasiIso_internalHomComplexPrecomp hP hPacyclic s _
  ((derivedInternalHom C).mapIso ((quotientCompQhIso C).app K).op).app L ≪≫
    @asIso _ _ _ _ (Qh.map ((HomotopyCategory.quotient _ _).map
      (internalHomComplexPrecomp s ((kInjectiveReplacement C).obj L).as))) hs ≪≫
    (quotientCompQhIso C).app _

/-- Let `C` have a separating family of objects `G` for which `- ⊗ G` preserves acyclic
complexes. If `p : K ⟶ I` is a quasi-isomorphism to the K-injective replacement `I` of `L`, the
derived internal Hom `R𝓗om(L, -)` is the internal Hom complex out of `K` into K-injective
replacements; the isomorphism is precomposition with `p`. -/
def derivedInternalHomObjIsoOfQuasiIso {S : ObjectProperty C} (hS : S.IsSeparating)
    (hSacyclic : ∀ G, S G → ∀ X : CochainComplex C ℤ, X.Acyclic →
      (((tensorRight G).mapHomologicalComplex _).obj X).Acyclic)
    (L : DerivedCategory C) {K : CochainComplex C ℤ}
    (p : K ⟶ ((kInjectiveReplacement C).obj L).as) [QuasiIso p] :
    (derivedInternalHom C).obj (op L) ≅ kInjectiveReplacement C ⋙
      (internalHomComplexHomotopyFunctor C).obj (op ((HomotopyCategory.quotient _ _).obj K)) ⋙
        Qh :=
  have : IsIso (Functor.whiskerLeft (kInjectiveReplacement C) (Functor.whiskerRight
      ((internalHomComplexHomotopyFunctor C).map ((HomotopyCategory.quotient _ _).map p).op)
        Qh)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app]
    -- The component at `M` is the image under `Qh` of precomposition with `p` on the internal
    -- Hom complex into the K-injective replacement of `M`, whose class is that replacement.
    have h := (isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      ((HomologicalComplex.mem_quasiIso_iff _).2
        (quasiIso_internalHomComplexPrecomp hS hSacyclic p ((kInjectiveReplacement C).obj M).as)))
    rw [← internalHomComplexHomotopyFunctor_map_app] at h
    exact h
  @asIso _ _ _ _ _ this

/-- The component of `derivedInternalHomObjIsoOfQuasiIso` at `M` is the image of precomposition
with `p` on the internal Hom complex into the K-injective replacement of `M`. -/
@[simp]
lemma derivedInternalHomObjIsoOfQuasiIso_hom_app {S : ObjectProperty C} (hS : S.IsSeparating)
    (hSacyclic : ∀ G, S G → ∀ X : CochainComplex C ℤ, X.Acyclic →
      (((tensorRight G).mapHomologicalComplex _).obj X).Acyclic)
    (L : DerivedCategory C) {K : CochainComplex C ℤ}
    (p : K ⟶ ((kInjectiveReplacement C).obj L).as) [QuasiIso p] (M : DerivedCategory C) :
    (derivedInternalHomObjIsoOfQuasiIso hS hSacyclic L p).hom.app M =
      Qh.map ((HomotopyCategory.quotient _ _).map
        (internalHomComplexPrecomp p ((kInjectiveReplacement C).obj M).as)) :=
  (rfl)

section GlobalSections

variable [HasDerivedCategory.{w'} (ModuleCat.{v} ℤ)]

/-- The global sections `Hom(𝟙, 𝓗om^•(I, J))` of the internal Hom complex between the
K-injective replacements `I` and `J` of `K` and `L`, which represents `R𝓗om(K, L)`, represent the
derived Hom complex `RHom(K, L)` of abelian groups. -/
def globalSectionsDerivedInternalHomIso (K L : DerivedCategory C) :
    Qh.obj ((HomotopyCategory.quotient _ _).obj
      ((((linearCoyoneda ℤ C).obj (op (𝟙_ C))).mapHomologicalComplex _).obj
        (internalHomComplex ((kInjectiveReplacement C).obj K).as
          ((kInjectiveReplacement C).obj L).as))) ≅
      ((derivedHom ℤ C).obj (op K)).obj L :=
  Qh.mapIso ((HomotopyCategory.quotient _ _).mapIso
    (globalSectionsInternalHomComplexIso _ _))

/-- The `n`-th cohomology of the global sections `Hom(𝟙, 𝓗om^•(I, J))` of the internal Hom
complex representing `R𝓗om(K, L)` is the group of morphisms `K ⟶ L⟦n⟧` in the derived
category. -/
def globalSectionsDerivedInternalHomHomologyAddEquiv (K L : DerivedCategory C) (n : ℤ) :
    ((((linearCoyoneda ℤ C).obj (op (𝟙_ C))).mapHomologicalComplex _).obj
      (internalHomComplex ((kInjectiveReplacement C).obj K).as
        ((kInjectiveReplacement C).obj L).as)).homology n ≃+ (K ⟶ L⟦n⟧) :=
  (((homologyFunctorFactors (ModuleCat.{v} ℤ) n).app _).symm ≪≫
    (homologyFunctor (ModuleCat.{v} ℤ) n).mapIso
      (((quotientCompQhIso (ModuleCat.{v} ℤ)).app _).symm ≪≫
        globalSectionsDerivedInternalHomIso K L)).toLinearEquiv.toAddEquiv.trans
    { toEquiv := (derivedHomHomologyLinearEquiv ℤ K L n).toEquiv
      map_add' := (derivedHomHomologyLinearEquiv ℤ K L n).map_add }

end GlobalSections

end TauCeti
