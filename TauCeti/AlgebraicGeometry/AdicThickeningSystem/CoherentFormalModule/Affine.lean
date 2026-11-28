/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Spf
public import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Coherent formal modules on the formal completion of an affine scheme

Let `R` be a commutative ring and `J` an ideal of `R`. Via the canonical identification
`specIso J : (Spec R).formalCompletion V(J) ≅ spf J` (Stacks, Lemma 87.14.6), coherent formal
modules on the formal completion `(Spec R)/V(J)` correspond to coherent formal modules on `spf J`.

Transporting the section-tower functors along `specIso J` yields:
* `specSectionsTower J`: the additive, fully faithful global-section tower functor into all
  `ModuleTower R` for any commutative ring `R`.
* `specFiniteSectionsTower J`: its lift to `FiniteAdicSystem J`, which is additive and fully
  faithful for any commutative ring `R`, is an equivalence if and only if every quotient
  `R ⧸ J ^ (n + 1)` is Noetherian (`isEquivalence_specFiniteSectionsTower`,
  `isEquivalence_specFiniteSectionsTower_iff`) — in particular when `J` is finitely generated and
  `R ⧸ J` is Noetherian (`isEquivalence_specFiniteSectionsTower_of_fg`), or when `R` is
  Noetherian — and fails to be essentially surjective without Noetherianity even for `J = ⊥`
  (`not_essSurj_specFiniteSectionsTower_mvPolynomial`).
* `coherentFormalModuleEquivSpecSelf`: when `R` is Noetherian and `J`-adically complete, coherent
  formal modules on `(Spec R)/V(J)` are equivalent to finite `R`-modules (`FGModuleCat R`), with
  inverse functor `specFiniteSectionsLim J` taking the inverse limit of levelwise global sections.
* `coherentFormalModuleEquivSpecOfFG` and `coherentFormalModuleEquivSpec` (Stacks, Lemma 30.23.1):
  for any finitely generated ideal `J` with `R ⧸ J` Noetherian — and in particular for any ideal `J`
  of a Noetherian ring `R` — coherent formal modules on `(Spec R)/V(J)` are equivalent to finite
  modules over the `J`-adic completion `AdicCompletion J R`, combining
  `specIsoSpfCompletion J fg : (Spec R)/V(J) ≅ Spf R̂` with
  `CoherentFormalModule.spfEquivFGModuleCat` and Noetherianity of `AdicCompletion J R`
  (`Ideal.isNoetherianRing_adicCompletion_of_fg`).

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion.specSectionsTower`, `specFiniteSectionsTower`:
  levelwise global sections of coherent formal modules on `(Spec R)/V(J)`.
* `AlgebraicGeometry.Scheme.formalCompletion.specSectionsLim`, `specFiniteSectionsLim`:
  inverse-limit global sections of coherent formal modules on `(Spec R)/V(J)`.
* `AlgebraicGeometry.Scheme.formalCompletion.coherentFormalModuleEquivSpecSelf`:
  equivalence `FGModuleCat R ≌ CoherentFormalModule ((Spec R)/V(J))` for `J`-adically complete
  Noetherian `R`.
* `AlgebraicGeometry.Scheme.formalCompletion.coherentFormalModuleEquivSpecOfFG`,
  `AlgebraicGeometry.Scheme.formalCompletion.coherentFormalModuleEquivSpec`:
  equivalence `FGModuleCat (AdicCompletion J R) ≌ CoherentFormalModule ((Spec R)/V(J))`
  (Stacks, Lemma 30.23.1).

## References

* [Stacks Project, Lemma 30.23.1](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

noncomputable section

variable {R : Type u} [CommRing R]

/-- The tower of levelwise global sections of a coherent formal module on the formal completion of
`Spec R` along `V(J)`, obtained by transporting `CoherentFormalModule.sectionsTower J` across
`specIso J`. -/
-- `@[expose]` is needed so `(specSectionsLim J).obj M` and
-- `((specFiniteSectionsTower J).obj M).obj` reduce to `(specSectionsTower J).obj M` below.
@[expose]
def specSectionsTower (J : Ideal R) :
    CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) ⥤
      TauCeti.ModuleTower.{u} R :=
  CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.sectionsTower J

instance (J : Ideal R) : (specSectionsTower J).Additive :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.sectionsTower J).Additive

instance (J : Ideal R) : (specSectionsTower J).Full :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.sectionsTower J).Full

instance (J : Ideal R) : (specSectionsTower J).Faithful :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.sectionsTower J).Faithful

/-- `specSectionsTower J` is the composition of `CoherentFormalModule.pullback (specIso J).inv`
with `CoherentFormalModule.sectionsTower J`. -/
theorem specSectionsTower_eq (J : Ideal R) :
    specSectionsTower J =
      CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.sectionsTower J :=
  (rfl)

/-- On objects, `specSectionsTower J` evaluates `(CoherentFormalModule.sectionsTower J).obj` on the
pullback along `(specIso J).inv`. -/
@[simp]
theorem specSectionsTower_obj (J : Ideal R)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) :
    (specSectionsTower J).obj M =
      (CoherentFormalModule.sectionsTower J).obj
        ((CoherentFormalModule.pullback (specIso J).inv).obj M) :=
  (rfl)

/-- On morphisms, `specSectionsTower J` evaluates `(CoherentFormalModule.sectionsTower J).map` on
the pullback along `(specIso J).inv`. -/
@[simp]
theorem specSectionsTower_map (J : Ideal R)
    {M N : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))} (f : M ⟶ N) :
    (specSectionsTower J).map f =
      (CoherentFormalModule.sectionsTower J).map
        ((CoherentFormalModule.pullback (specIso J).inv).map f) :=
  (rfl)

/-- The global-sections tower of a coherent formal module on `(Spec R)/V(J)`, valued in `J`-adic
systems of `R`-modules with finite first term. -/
-- `@[expose]` is needed so `specFiniteSectionsTower_map_hom` reduces
-- `((specFiniteSectionsTower J).obj M).obj`.
@[expose]
def specFiniteSectionsTower (J : Ideal R) :
    CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) ⥤
      TauCeti.ModuleTower.FiniteAdicSystem.{u} J :=
  CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.finiteSectionsTower J

instance (J : Ideal R) : (specFiniteSectionsTower J).Additive :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsTower J).Additive

instance (J : Ideal R) : (specFiniteSectionsTower J).Full :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsTower J).Full

instance (J : Ideal R) : (specFiniteSectionsTower J).Faithful :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsTower J).Faithful

/-- `specFiniteSectionsTower J` is the composition of
`CoherentFormalModule.pullback (specIso J).inv` with
`CoherentFormalModule.finiteSectionsTower J`. -/
theorem specFiniteSectionsTower_eq (J : Ideal R) :
    specFiniteSectionsTower J =
      CoherentFormalModule.pullback (specIso J).inv ⋙
        CoherentFormalModule.finiteSectionsTower J :=
  (rfl)

/-- On objects, the underlying tower of `(specFiniteSectionsTower J).obj M` is
`(specSectionsTower J).obj M`. -/
@[simp]
theorem specFiniteSectionsTower_obj_obj (J : Ideal R)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) :
    ((specFiniteSectionsTower J).obj M).obj = (specSectionsTower J).obj M :=
  (rfl)

/-- On morphisms, the underlying tower morphism of `(specFiniteSectionsTower J).map f` is
`(specSectionsTower J).map f`. -/
@[simp]
theorem specFiniteSectionsTower_map_hom (J : Ideal R)
    {M N : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))} (f : M ⟶ N) :
    ((specFiniteSectionsTower J).map f).hom = (specSectionsTower J).map f :=
  (rfl)

/-- When every quotient `R ⧸ J ^ (n + 1)` is Noetherian — in particular when `R` is Noetherian —
taking levelwise global sections identifies coherent formal modules on `(Spec R)/V(J)` with
`J`-adic systems of `R`-modules having finite first term, without any `J`-adic completeness
assumption on `R`. -/
instance isEquivalence_specFiniteSectionsTower (J : Ideal R)
    [∀ n, IsNoetherianRing (R ⧸ J ^ (n + 1))] :
    (specFiniteSectionsTower J).IsEquivalence :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsTower J).IsEquivalence

/-- Taking levelwise global sections identifies coherent formal modules on `(Spec R)/V(J)` with
finite `J`-adic systems if and only if every quotient `R ⧸ J ^ (n + 1)` is Noetherian. -/
theorem isEquivalence_specFiniteSectionsTower_iff (J : Ideal R) :
    (specFiniteSectionsTower J).IsEquivalence ↔ ∀ n, IsNoetherianRing (R ⧸ J ^ (n + 1)) := by
  refine ⟨fun h ↦ (CoherentFormalModule.essSurj_finiteSectionsTower_iff J).1 ⟨fun F ↦ ?_⟩,
    fun h ↦ @isEquivalence_specFiniteSectionsTower _ _ J h⟩
  have := h
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := specFiniteSectionsTower J) F
  exact ⟨(CoherentFormalModule.pullback (specIso J).inv).obj M, ⟨e⟩⟩

/-- When `J` is finitely generated and `R ⧸ J` is Noetherian, taking levelwise global sections
identifies coherent formal modules on `(Spec R)/V(J)` with finite `J`-adic systems, without any
`J`-adic completeness or global Noetherianity assumption on `R`. -/
theorem isEquivalence_specFiniteSectionsTower_of_fg (J : Ideal R) (fg : J.FG)
    [IsNoetherianRing (R ⧸ J)] :
    (specFiniteSectionsTower J).IsEquivalence :=
  have : ∀ n, IsNoetherianRing (R ⧸ J ^ (n + 1)) := fun n ↦
    Ideal.isNoetherianRing_quotient_pow_of_fg J fg (n + 1)
  inferInstance

/-- **Essential surjectivity of `specFiniteSectionsTower` fails without Noetherianity.** Over
`MvPolynomial ℕ k` (`k` nontrivial), `specFiniteSectionsTower ⊥` is not essentially surjective. -/
theorem not_essSurj_specFiniteSectionsTower_mvPolynomial (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ (specFiniteSectionsTower (⊥ : Ideal (MvPolynomial ℕ k))).EssSurj := by
  intro hEss
  refine CoherentFormalModule.not_essSurj_finiteSectionsTower_mvPolynomial k ⟨fun F ↦ ?_⟩
  obtain ⟨M, ⟨e⟩⟩ := hEss.mem_essImage F
  exact ⟨(CoherentFormalModule.pullback (specIso (⊥ : Ideal (MvPolynomial ℕ k))).inv).obj M, ⟨e⟩⟩

/-- The inverse limit of levelwise global sections of a coherent formal module on
`(Spec R)/V(J)`. -/
-- `@[expose]` is needed so `specSectionsLim_map` reduces `(specSectionsLim J).obj M`.
@[expose]
def specSectionsLim (J : Ideal R) :
    CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) ⥤
      ModuleCat.{u} R :=
  CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.sectionsLim J

instance (J : Ideal R) : (specSectionsLim J).Additive :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.sectionsLim J).Additive

/-- `specSectionsLim J` is the composition of `CoherentFormalModule.pullback (specIso J).inv`
with `CoherentFormalModule.sectionsLim J`. -/
theorem specSectionsLim_eq (J : Ideal R) :
    specSectionsLim J =
      CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.sectionsLim J :=
  (rfl)

/-- On objects, `specSectionsLim J` sends `M` to the inverse limit of
`(specSectionsTower J).obj M`. -/
@[simp]
theorem specSectionsLim_obj (J : Ideal R)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) :
    (specSectionsLim J).obj M = ModuleCat.of R ((specSectionsTower J).obj M).lim :=
  (rfl)

/-- On morphisms, `specSectionsLim J` sends `f` to the induced map on inverse limits. -/
@[simp]
theorem specSectionsLim_map (J : Ideal R)
    {M N : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))} (f : M ⟶ N) :
    (specSectionsLim J).map f =
      ModuleCat.ofHom (TauCeti.ModuleTower.limMap ((specSectionsTower J).map f)) :=
  (rfl)

/-- Over a `J`-adically precomplete ring `R`, the inverse limit of levelwise global sections of a
coherent formal module on `(Spec R)/V(J)` as a finite `R`-module. -/
-- `@[expose]` is needed so `specFiniteSectionsLim_map_hom` reduces
-- `((specFiniteSectionsLim J).obj M).obj`.
@[expose]
def specFiniteSectionsLim (J : Ideal R) [IsPrecomplete J R] :
    CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) ⥤
      FGModuleCat.{u} R :=
  CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.finiteSectionsLim J

instance (J : Ideal R) [IsPrecomplete J R] : (specFiniteSectionsLim J).Additive :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsLim J).Additive

/-- `specFiniteSectionsLim J` is the composition of
`CoherentFormalModule.pullback (specIso J).inv` with
`CoherentFormalModule.finiteSectionsLim J`. -/
theorem specFiniteSectionsLim_eq (J : Ideal R) [IsPrecomplete J R] :
    specFiniteSectionsLim J =
      CoherentFormalModule.pullback (specIso J).inv ⋙
        CoherentFormalModule.finiteSectionsLim J :=
  (rfl)

/-- On objects, the underlying module of `(specFiniteSectionsLim J).obj M` is the inverse limit
of `(specSectionsTower J).obj M`. -/
@[simp]
theorem specFiniteSectionsLim_obj_obj (J : Ideal R) [IsPrecomplete J R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) :
    ((specFiniteSectionsLim J).obj M).obj = ModuleCat.of R ((specSectionsTower J).obj M).lim :=
  (rfl)

/-- On morphisms, the underlying `ModuleCat` morphism of `(specFiniteSectionsLim J).map f` is
`ModuleTower.limMap ((specSectionsTower J).map f)`. -/
@[simp]
theorem specFiniteSectionsLim_map_hom (J : Ideal R) [IsPrecomplete J R]
    {M N : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))} (f : M ⟶ N) :
    ((specFiniteSectionsLim J).map f).hom =
      ModuleCat.ofHom (TauCeti.ModuleTower.limMap ((specSectionsTower J).map f)) :=
  (rfl)

/-- **Coherent formal modules on `(Spec R)/V(J)` over a complete Noetherian ring** (Stacks,
Lemma 30.23.1): when `R` is Noetherian and `J`-adically complete, coherent formal modules on the
formal completion of `Spec R` along `V(J)` are equivalent to finite `R`-modules. -/
-- `@[expose]` is forced by dependent typing: the inverse module must reduce to the limit in the
-- type of `coherentFormalModuleEquivSpecSelfInverseCompFiniteReductionIso_hom_app_reductionπ`.
@[expose, stacks 087W]
def coherentFormalModuleEquivSpecSelf (J : Ideal R) [IsNoetherianRing R] [IsAdicComplete J R] :
    FGModuleCat.{u} R ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  (CoherentFormalModule.spfEquivFGModuleCat ⟨R, J, IsNoetherian.noetherian J⟩).symm.trans
    (CoherentFormalModule.pullbackEquiv (specIso J))

/-- `coherentFormalModuleEquivSpecSelf J` preserves addition of morphisms. -/
instance (J : Ideal R) [IsNoetherianRing R] [IsAdicComplete J R] :
    (coherentFormalModuleEquivSpecSelf J).functor.Additive where
  map_add {X Y f g} := by
    have hfun : (CoherentFormalModule.spfEquivFGModuleCat
        ⟨R, J, IsNoetherian.noetherian J⟩).functor.Additive :=
      inferInstanceAs (CoherentFormalModule.finiteSectionsLim J).Additive
    have hinv : (CoherentFormalModule.spfEquivFGModuleCat
        ⟨R, J, IsNoetherian.noetherian J⟩).inverse.Additive :=
      @Equivalence.inverse_additive _ _ _ _ _ _
        (CoherentFormalModule.spfEquivFGModuleCat ⟨R, J, IsNoetherian.noetherian J⟩) hfun
    exact (congrArg (CoherentFormalModule.pullbackEquiv (specIso J)).functor.map
      (hinv.map_add (f := f) (g := g))).trans
      (Functor.map_add (F := (CoherentFormalModule.pullbackEquiv (specIso J)).functor))

@[simp]
theorem coherentFormalModuleEquivSpecSelf_inverse (J : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete J R] :
    (coherentFormalModuleEquivSpecSelf J).inverse = specFiniteSectionsLim J := by
  rw [coherentFormalModuleEquivSpecSelf, Equivalence.trans_inverse, Equivalence.symm_inverse,
    CoherentFormalModule.spfEquivFGModuleCat_functor, specFiniteSectionsLim_eq]
  exact congrArg (· ⋙ CoherentFormalModule.finiteSectionsLim J)
    (CoherentFormalModule.pullbackEquiv_inverse (specIso J))

/-- Under `coherentFormalModuleEquivSpecSelf J`, the global-sections tower of the coherent formal
module associated to a finite `R`-module `M` is naturally isomorphic to the reduction tower
`(M ⧸ J ^ (n + 1) M)ₙ`. -/
def coherentFormalModuleEquivSpecSelfFunctorCompSpecFiniteSectionsTowerIso (J : Ideal R)
    [IsNoetherianRing R] [IsAdicComplete J R] :
    (coherentFormalModuleEquivSpecSelf J).functor ⋙ specFiniteSectionsTower J ≅
      TauCeti.ModuleTower.finiteReduction J :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight
          (eqToIso (CoherentFormalModule.pullbackEquiv_inverse (specIso J)).symm) _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (CoherentFormalModule.pullbackEquiv (specIso J)).unitIso.symm _ ≪≫
        Functor.leftUnitor _) ≪≫
    CoherentFormalModule.spfEquivFGModuleCatInverseCompFiniteSectionsTowerIso
      ⟨R, J, IsNoetherian.noetherian J⟩

/-- Under `coherentFormalModuleEquivSpecSelf J`, the reduction tower of the finite `R`-module
corresponding to a coherent formal module on `(Spec R)/V(J)` is naturally isomorphic to
`specFiniteSectionsTower J`. -/
def coherentFormalModuleEquivSpecSelfInverseCompFiniteReductionIso (J : Ideal R)
    [IsNoetherianRing R] [IsAdicComplete J R] :
    (coherentFormalModuleEquivSpecSelf J).inverse ⋙ TauCeti.ModuleTower.finiteReduction J ≅
      specFiniteSectionsTower J :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CoherentFormalModule.spfEquivFGModuleCatFunctorCompFiniteReductionIso
        ⟨R, J, IsNoetherian.noetherian J⟩) ≪≫
    Functor.isoWhiskerRight (eqToIso (CoherentFormalModule.pullbackEquiv_inverse (specIso J))) _

/-- The reductions-to-sections comparison for `coherentFormalModuleEquivSpecSelf J` is induced by
the projections from the inverse limit. -/
@[simp]
theorem coherentFormalModuleEquivSpecSelfInverseCompFiniteReductionIso_hom_app_reductionπ
    (J : Ideal R) [IsNoetherianRing R] [IsAdicComplete J R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ) (x : ((specSectionsTower J).obj M).lim) :
    dsimp% only [CategoryTheory.Functor.comp_obj, CategoryTheory.ObjectProperty.ι_obj,
      FGModuleCat.obj_carrier]
    (((coherentFormalModuleEquivSpecSelfInverseCompFiniteReductionIso J).hom.app M).hom.app
      (op n)).hom
      (TauCeti.ModuleTower.reductionπ J
        ((coherentFormalModuleEquivSpecSelf J).inverse.obj M).obj n x) =
      ((specSectionsTower J).obj M).limπ n x :=
  CoherentFormalModule.spfEquivFGModuleCatFunctorCompFiniteReductionIso_hom_app_reductionπ
    ⟨R, J, IsNoetherian.noetherian J⟩ ((CoherentFormalModule.pullback (specIso J).inv).obj M) n x

/-- **Coherent formal modules on `(Spec R)/V(J)` for a finitely generated ideal with Noetherian
quotient** (Stacks, Lemma 30.23.1): if `J` is finitely generated and `R ⧸ J` is Noetherian, then
`AdicCompletion J R` is Noetherian and coherent formal modules on `(Spec R)/V(J)` are equivalent to
finite modules over `AdicCompletion J R`. -/
-- `@[expose]` is forced by dependent typing: the inverse module must reduce to the limit in the
-- type of `coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso_hom_app_reductionπ`.
@[expose, stacks 087W]
def coherentFormalModuleEquivSpecOfFG (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)] :
    FGModuleCat.{u} (AdicCompletion J R) ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  letI := Ideal.isNoetherianRing_adicCompletion_of_fg J fg
  (CoherentFormalModule.spfEquivFGModuleCat (AdicRing.completion J fg)).symm.trans
    (CoherentFormalModule.pullbackEquiv (specIsoSpfCompletion J fg))

/-- `coherentFormalModuleEquivSpecOfFG J fg` preserves addition of morphisms. -/
instance (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)] :
    (coherentFormalModuleEquivSpecOfFG J fg).functor.Additive where
  map_add {X Y f g} := by
    have hfun : (@CoherentFormalModule.spfEquivFGModuleCat (AdicRing.completion J fg)
        (Ideal.isNoetherianRing_adicCompletion_of_fg J fg)).functor.Additive :=
      inferInstanceAs (@CoherentFormalModule.finiteSectionsLim (AdicCompletion J R) _
        (AdicRing.completion J fg).ideal
        (AdicCompletion.isAdicComplete_self J fg).toIsPrecomplete).Additive
    have hinv : (@CoherentFormalModule.spfEquivFGModuleCat (AdicRing.completion J fg)
        (Ideal.isNoetherianRing_adicCompletion_of_fg J fg)).inverse.Additive :=
      @Equivalence.inverse_additive _ _ _ _ _ _
        (@CoherentFormalModule.spfEquivFGModuleCat (AdicRing.completion J fg)
          (Ideal.isNoetherianRing_adicCompletion_of_fg J fg))
        hfun
    exact (congrArg (CoherentFormalModule.pullbackEquiv (specIsoSpfCompletion J fg)).functor.map
      (hinv.map_add (f := f) (g := g))).trans
      (Functor.map_add
        (F := (CoherentFormalModule.pullbackEquiv (specIsoSpfCompletion J fg)).functor))

/-- The inverse of `coherentFormalModuleEquivSpecOfFG J fg` transports along
`(specIsoSpfCompletion J fg).inv` and takes the inverse limit of levelwise global sections over
the completed ring. -/
@[simp]
theorem coherentFormalModuleEquivSpecOfFG_inverse (J : Ideal R) (fg : J.FG)
    [IsNoetherianRing (R ⧸ J)] :
    (coherentFormalModuleEquivSpecOfFG J fg).inverse =
      CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv ⋙
        @CoherentFormalModule.finiteSectionsLim _ _ (AdicRing.completion J fg).ideal
          (AdicCompletion.isAdicComplete_self J fg).toIsPrecomplete := by
  let := Ideal.isNoetherianRing_adicCompletion_of_fg J fg
  rw [coherentFormalModuleEquivSpecOfFG, Equivalence.trans_inverse, Equivalence.symm_inverse,
    CoherentFormalModule.spfEquivFGModuleCat_functor]
  exact congrArg (· ⋙ @CoherentFormalModule.finiteSectionsLim _ _
      (AdicRing.completion J fg).ideal (AdicCompletion.isAdicComplete_self J fg).toIsPrecomplete)
    (CoherentFormalModule.pullbackEquiv_inverse (specIsoSpfCompletion J fg))

/-- Under `coherentFormalModuleEquivSpecOfFG J fg`, transporting the coherent formal module
associated to a finite `AdicCompletion J R`-module `M` along `(specIsoSpfCompletion J fg).inv` has
global-sections tower naturally isomorphic to the reduction tower of `M` over the completed ring. -/
def coherentFormalModuleEquivSpecOfFGFunctorCompFiniteSectionsTowerIso (J : Ideal R) (fg : J.FG)
    [IsNoetherianRing (R ⧸ J)] :
    (coherentFormalModuleEquivSpecOfFG J fg).functor ⋙
        CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv ⋙
          CoherentFormalModule.finiteSectionsTower (AdicRing.completion J fg).ideal ≅
      TauCeti.ModuleTower.finiteReduction (AdicRing.completion J fg).ideal :=
  letI := Ideal.isNoetherianRing_adicCompletion_of_fg J fg
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight
          (eqToIso (CoherentFormalModule.pullbackEquiv_inverse (specIsoSpfCompletion J fg)).symm)
          _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (CoherentFormalModule.pullbackEquiv (specIsoSpfCompletion J fg)).unitIso.symm _ ≪≫
        Functor.leftUnitor _) ≪≫
    CoherentFormalModule.spfEquivFGModuleCatInverseCompFiniteSectionsTowerIso
      (AdicRing.completion J fg)

/-- Under `coherentFormalModuleEquivSpecOfFG J fg`, the reduction tower of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module on `(Spec R)/V(J)` is
naturally isomorphic to the global-sections tower over the completed ring. -/
def coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso (J : Ideal R) (fg : J.FG)
    [IsNoetherianRing (R ⧸ J)] :
    (coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
        TauCeti.ModuleTower.finiteReduction (AdicRing.completion J fg).ideal ≅
      CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv ⋙
        CoherentFormalModule.finiteSectionsTower (AdicRing.completion J fg).ideal :=
  letI := Ideal.isNoetherianRing_adicCompletion_of_fg J fg
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CoherentFormalModule.spfEquivFGModuleCatFunctorCompFiniteReductionIso
        (AdicRing.completion J fg)) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (CoherentFormalModule.pullbackEquiv_inverse (specIsoSpfCompletion J fg))) _

/-- The reductions-to-sections comparison for `coherentFormalModuleEquivSpecOfFG J fg` is induced
by the projections from the inverse limit over the completed ring. -/
@[simp]
theorem coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso_hom_app_reductionπ
    (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).lim) :
    dsimp% only [CategoryTheory.Functor.comp_obj, CategoryTheory.ObjectProperty.ι_obj,
      FGModuleCat.obj_carrier]
    (((coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso J fg).hom.app M).hom.app
      (op n)).hom
      (TauCeti.ModuleTower.reductionπ (AdicRing.completion J fg).ideal
        ((coherentFormalModuleEquivSpecOfFG J fg).inverse.obj M).obj n x) =
      ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n x := by
  let := Ideal.isNoetherianRing_adicCompletion_of_fg J fg
  exact CoherentFormalModule.spfEquivFGModuleCatFunctorCompFiniteReductionIso_hom_app_reductionπ
    (AdicRing.completion J fg)
    ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M) n x

private lemma moduleSpecΓFunctor_map_comp_apply {R₀ : CommRingCat.{u}}
    {M N P : (Spec R₀).Modules} (u : M ⟶ N) (v : N ⟶ P) (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map (u ≫ v) x =
      moduleSpecΓFunctor.map v (moduleSpecΓFunctor.map u x) := by
  rw [Functor.map_comp, ModuleCat.comp_apply]

private lemma moduleSpecΓFunctor_map_unit_pullbackCongr
    {R₀ S₀ : CommRingCat.{u}} {f g : Spec S₀ ⟶ Spec R₀} (h : f = g)
    (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr h).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          m) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) m := by
  subst h
  simp [Scheme.Modules.pullbackCongr]
  rfl

private lemma moduleSpecΓFunctor_map_pullbackComp_inv_unit
    {R₀ S₀ T₀ : CommRingCat.{u}} (f : Spec T₀ ⟶ Spec S₀) (g : Spec S₀ ⟶ Spec R₀)
    (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M)
          m) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M))
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
          m) := by
  have h := congrArg (fun k ↦ (moduleSpecΓFunctor (R := R₀)).map k m)
    (Scheme.Modules.unit_comp_pushforward_map_pullbackComp_inv_app f g M)
  simp only [Functor.map_comp, ModuleCat.comp_apply] at h
  exact h

private lemma moduleSpecΓFunctor_map_pullbackComp_hom_unit
    {R₀ S₀ T₀ : CommRingCat.{u}} (f : Spec T₀ ⟶ Spec S₀) (g : Spec S₀ ⟶ Spec R₀)
    (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
            m)) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M)
        m := by
  let z : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M) m
  have h2 := congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).hom.app M))
    (moduleSpecΓFunctor_map_pullbackComp_inv_unit f g M m).symm
  refine h2.trans ?_
  calc moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app M) z)
      = moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app M ≫
          (Scheme.Modules.pullbackComp f g).hom.app M) z :=
        (moduleSpecΓFunctor_map_comp_apply _ _ z).symm
    _ = z := by rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, ModuleCat.id_apply]

private lemma moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_unit
    {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    {t : Spec S₀ ⟶ Spec S₁} {l : Spec S₀ ⟶ Spec R₀}
    {r : Spec S₁ ⟶ Spec R₁} {b : Spec R₀ ⟶ Spec R₁}
    (sq : CommSq t l r b) (M : (Spec R₁).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoOfCommSq sq).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app
          ((Scheme.Modules.pullback r).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M)
            m)) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction l).unit.app
        ((Scheme.Modules.pullback b).obj M))
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M)
          m) := by
  rw [Scheme.Modules.pullbackCompIsoOfCommSq_hom_app]
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp l b).inv.app M)) ?_).trans
    (moduleSpecΓFunctor_map_pullbackComp_inv_unit l b M m)
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr sq.w).hom.app M))
    (moduleSpecΓFunctor_map_pullbackComp_hom_unit t r M m)).trans ?_
  exact moduleSpecΓFunctor_map_unit_pullbackCongr sq.w M m

private lemma moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_inv_unit
    {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    {t : Spec S₀ ⟶ Spec S₁} {l : Spec S₀ ⟶ Spec R₀}
    {r : Spec S₁ ⟶ Spec R₁} {b : Spec R₀ ⟶ Spec R₁}
    (sq : CommSq t l r b) (M : (Spec R₁).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction l).unit.app
          ((Scheme.Modules.pullback b).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M)
            m)) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app
        ((Scheme.Modules.pullback r).obj M))
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M)
          m) := by
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M))
    (moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_unit sq M m).symm).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).symm.trans ?_
  rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rfl

private lemma moduleSpecΓFunctor_map_pullbackCompIsoId_unit
    {R₀ S₀ : CommRingCat.{u}} {f : Spec R₀ ⟶ Spec S₀} {g : Spec S₀ ⟶ Spec R₀}
    (h : f ≫ g = 𝟙 (Spec R₀)) (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoId h).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
            m)) =
      m := by
  have h1 := congrArg (fun k ↦ (k.app ⊤).hom m)
    (Scheme.Modules.unit_comp_pushforwardCongr_hom_app_pushforwardId_hom_app
      (rfl : 𝟙 (Spec R₀) = 𝟙 (Spec R₀)) M)
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardId_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id] at h1
  have hid : moduleSpecΓFunctor.map ((Scheme.Modules.pullbackId (Spec R₀)).hom.app M)
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec R₀))).unit.app M) m) = m := by
    refine (congrArg (((Scheme.Modules.pullbackId (Spec R₀)).hom.app M).app ⊤) h1).trans ?_
    change (((Scheme.Modules.pullbackId (Spec R₀)).inv.app M ≫
      (Scheme.Modules.pullbackId (Spec R₀)).hom.app M).app ⊤).hom m = m
    rw [Iso.inv_hom_id_app]; rfl
  rw [Scheme.Modules.pullbackCompIsoId_hom_app]
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackId (Spec R₀)).hom.app M))
    ?_).trans hid
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr h).hom.app M))
    (moduleSpecΓFunctor_map_pullbackComp_hom_unit f g M m)).trans ?_
  exact moduleSpecΓFunctor_map_unit_pullbackCongr h M m

private lemma moduleSpecΓFunctor_map_unit_naturality
    {R₀ S₀ : CommRingCat.{u}} (f : Spec S₀ ⟶ Spec R₀) {M N : (Spec R₀).Modules}
    (u : M ⟶ N) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)
        (moduleSpecΓFunctor.map u m) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map u)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          m) := by
  let m' : Γ(M, ⊤) := m
  have h := congrArg (fun k ↦ (k.app ⊤).hom m')
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality u)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
  rw [Scheme.Modules.pushforward_map_app] at h
  change (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app ⊤).hom
      ((u.app ⊤).hom m') =
    (((Scheme.Modules.pullback f).map u).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom m')
  exact h

private lemma specIsoSpfCompletion_inv (J : Ideal R) (fg : J.FG) :
    (specIsoSpfCompletion J fg).inv = (Spf.completionIso J fg).hom ≫ (specIso J).inv := by
  ext n
  rw [← cancel_mono (toScheme _ _ n), AdicThickeningSystem.comp_app, Category.assoc,
    specIsoSpfCompletion_inv_app_toScheme, specIso_inv_app_toScheme]
  exact (congrArg (·.app n) (Spf.completionIso_hom_spfToSpec J fg)).symm

private lemma completionIso_hom_app (J : Ideal R) (fg : J.FG) (n : ℕ) :
    (Spf.completionIso J fg).hom.app n =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((AdicRing.completion J fg).ideal ^ (n + 1))
        (algebraMap R (AdicCompletion J R))
        ((Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans
          (Ideal.le_comap_pow _ (n + 1))))) := by
  rw [Spf.completionIso_hom, AdicThickeningSystem.spfMap_app]

private def pullbackCompletionIso (J : Ideal R) (fg : J.FG) :
    CoherentFormalModule.pullback (specIso J).inv ⋙
        CoherentFormalModule.pullback (Spf.completionIso J fg).hom ≅
      CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv :=
  CoherentFormalModule.pullbackComp (Spf.completionIso J fg).hom (specIso J).inv ≪≫
    CoherentFormalModule.pullbackCongr (specIsoSpfCompletion_inv J fg).symm

private def specSectionsTowerCompletionLevelHom (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (n : ℕ) :
    ((specSectionsTower J).obj M).obj (op n) ⟶
      (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).obj
        (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).obj (op n)) :=
  let φ := algebraMap R (AdicCompletion J R)
  let A := AdicRing.completion J fg
  let hH : J ^ (n + 1) ≤ (A.ideal ^ (n + 1)).comap φ :=
    (Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))
  let φₙ : CommRingCat.of (R ⧸ J ^ (n + 1)) ⟶ CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1)) :=
    CommRingCat.ofHom (Ideal.quotientMap (A.ideal ^ (n + 1)) φ hH)
  let eM :=
    (Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).hom.app
        (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n) ≫
      ((pullbackCompletionIso J fg).hom.app M).app n
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ (n + 1)))).map
      (CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) ≫
    (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk (J ^ (n + 1))) φₙ.hom
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ)
      (Ideal.quotientMap_comp_mk hH).symm _).inv ≫
    (ModuleCat.restrictScalarsComp'App φ (Ideal.Quotient.mk (A.ideal ^ (n + 1)))
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ) rfl _).hom

private lemma specSectionsTowerCompletionLevelHom_apply (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (n : ℕ)
    (m : ((specSectionsTower J).obj M).obj (op n)) :
    specSectionsTowerCompletionLevelHom J fg M n m =
      moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).hom.app n)).unit.app
            (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n))
          m) := by
  refine (CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply _ _ m).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  exact congrArg (moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app M).app n))
    (moduleSpecΓFunctor_map_unit_pullbackCongr (completionIso_hom_app J fg n).symm _ m)

private instance (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (n : ℕ) :
    IsIso (specSectionsTowerCompletionLevelHom J fg M n) := by
  let φ := algebraMap R (AdicCompletion J R)
  let A := AdicRing.completion J fg
  let hH : J ^ (n + 1) ≤ (A.ideal ^ (n + 1)).comap φ :=
    (Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))
  let φₙ : CommRingCat.of (R ⧸ J ^ (n + 1)) ⟶ CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1)) :=
    CommRingCat.ofHom (Ideal.quotientMap (A.ideal ^ (n + 1)) φ hH)
  have hbij := AdicCompletion.quotientMap_algebraMap_bijective fg (n + 1) (H := hH)
  have hker : RingHom.ker φₙ.hom = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 hbij.1
  let N : (Spec (CommRingCat.of (R ⧸ J ^ (n + 1)))).Modules :=
    ((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n
  have : N.IsFinitePresentation :=
    ((CoherentFormalModule.pullback (specIso J).inv).obj M).isFinitePresentation n
  have : N.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation N
  let eM :=
    (Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).hom.app N ≫
      ((pullbackCompletionIso J fg).hom.app M).app n
  have hsurj := CommRingCat.Hom.moduleSpecΓFunctor_map_unit_surjective (φ := φₙ) hbij.2 N
  have hker_unit : LinearMap.ker
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φₙ)).unit.app N)).hom = ⊥ := by
    rw [CommRingCat.Hom.ker_moduleSpecΓFunctor_map_unit (φ := φₙ) hbij.2 N, hker,
      Submodule.bot_smul]
  have hinj : Function.Injective
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φₙ)).unit.app N)) :=
    LinearMap.ker_eq_bot.1 hker_unit
  have h1 : IsIso ((Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).hom.app N) :=
    ((Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).app N).isIso_hom
  have h2 : IsIso (((pullbackCompletionIso J fg).hom.app M).app n) :=
    @CoherentFormalModule.isIso_app_of_isIso _ _ _ ((pullbackCompletionIso J fg).hom.app M)
      ((pullbackCompletionIso J fg).app M).isIso_hom n
  have h_eM : IsIso eM := @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  have h_map : IsIso (moduleSpecΓFunctor.map eM) :=
    @Functor.map_isIso _ _ _ _ _ _ moduleSpecΓFunctor eM h_eM
  have he_bij : Function.Bijective (moduleSpecΓFunctor.map eM) :=
    @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ (moduleSpecΓFunctor.map eM) h_map
  have : IsIso (CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    have hfun : ⇑(CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) =
        ⇑(moduleSpecΓFunctor.map eM) ∘
          ⇑(moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φₙ)).unit.app N)) := by
      ext m
      exact CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply φₙ eM m
    rw [hfun]
    exact he_bij.comp ⟨hinj, hsurj⟩
  change IsIso ((ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ (n + 1)))).map
      (CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) ≫
    (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk (J ^ (n + 1))) φₙ.hom
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ)
      (Ideal.quotientMap_comp_mk hH).symm _).inv ≫
    (ModuleCat.restrictScalarsComp'App φ (Ideal.Quotient.mk (A.ideal ^ (n + 1)))
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ) rfl _).hom)
  infer_instance

private lemma moduleSpecΓFunctor_map_square_transition
    {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    {t : Spec S₀ ⟶ Spec S₁} {l : Spec S₀ ⟶ Spec R₀}
    {r : Spec S₁ ⟶ Spec R₁} {b : Spec R₀ ⟶ Spec R₁}
    (sq : CommSq t l r b)
    {M₀_m : (Spec R₀).Modules} {M₀_m1 : (Spec R₁).Modules}
    {M₁_m : (Spec S₀).Modules} {M₁_m1 : (Spec S₁).Modules}
    (t₀ : (Scheme.Modules.pullback b).obj M₀_m1 ⟶ M₀_m)
    (t₁ : (Scheme.Modules.pullback t).obj M₁_m1 ⟶ M₁_m)
    (e₀ : (Scheme.Modules.pullback l).obj M₀_m ⟶ M₁_m)
    (e₁ : (Scheme.Modules.pullback r).obj M₀_m1 ⟶ M₁_m1)
    (hnat : (Scheme.Modules.pullback t).map e₁ ≫ t₁ =
      (Scheme.Modules.pullbackCompIsoOfCommSq sq).hom.app M₀_m1 ≫
        (Scheme.Modules.pullback l).map t₀ ≫ e₀)
    (x : moduleSpecΓFunctor.obj M₀_m1) :
    moduleSpecΓFunctor.map e₀
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction l).unit.app M₀_m)
          (moduleSpecΓFunctor.map t₀
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
              M₀_m1) x))) =
      moduleSpecΓFunctor.map t₁
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app M₁_m1)
          (moduleSpecΓFunctor.map e₁
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app
              M₀_m1) x))) := by
  have hnat' : (Scheme.Modules.pullback l).map t₀ ≫ e₀ =
      (Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M₀_m1 ≫
        (Scheme.Modules.pullback t).map e₁ ≫ t₁ :=
    Eq.symm <|
      (congrArg ((Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M₀_m1 ≫ ·) hnat).trans
        (Iso.inv_hom_id_app_assoc (Scheme.Modules.pullbackCompIsoOfCommSq sq) M₀_m1 _)
  refine (congrArg (moduleSpecΓFunctor.map e₀)
    (moduleSpecΓFunctor_map_unit_naturality l t₀ _)).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).symm.trans ?_
  refine (congrArg (fun k ↦ (moduleSpecΓFunctor.map k) _) hnat').trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (fun z ↦ moduleSpecΓFunctor.map t₁
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback t).map e₁) z))
    (moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_inv_unit sq M₀_m1 x)).trans ?_
  exact congrArg (moduleSpecΓFunctor.map t₁)
    (moduleSpecΓFunctor_map_unit_naturality t e₁ _).symm

private lemma specSectionsTowerCompletionLevelHom_succ (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (m : ℕ) :
    (((specSectionsTower J).obj M).map (homOfLE (Nat.le_succ m)).op) ≫
        specSectionsTowerCompletionLevelHom J fg M m =
      specSectionsTowerCompletionLevelHom J fg M (m + 1) ≫
        (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).map
          (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
            ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).map
            (homOfLE (Nat.le_succ m)).op) := by
  ext x
  let M₀ := (CoherentFormalModule.pullback (specIso J).inv).obj M
  let M₁ := (CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M
  let e := (pullbackCompletionIso J fg).hom.app M
  let F := (specSectionsTower J).obj M
  let G := (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj M₁
  have hL : (F.map (homOfLE (Nat.le_succ m)).op ≫
        specSectionsTowerCompletionLevelHom J fg M m) x =
      moduleSpecΓFunctor.map (e.app m)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          ((Spf.completionIso J fg).hom.app m)).unit.app (M₀.obj m))
          (moduleSpecΓFunctor.map (M₀.transitionIso m).hom
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
              ((spf J).ι m)).unit.app (M₀.obj (m + 1))) x))) := by
    refine (congrArg (specSectionsTowerCompletionLevelHom J fg M m)
      (LinearMap.congr_fun (TauCeti.ModuleTower.transition_def F m).symm x)).trans ?_
    refine (specSectionsTowerCompletionLevelHom_apply J fg M m (F.transition m x)).trans ?_
    exact congrArg (fun z ↦ moduleSpecΓFunctor.map (e.app m)
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        ((Spf.completionIso J fg).hom.app m)).unit.app (M₀.obj m)) z))
      (CoherentFormalModule.sectionsTower_obj_transition_apply J M₀ m x)
  have hR : (specSectionsTowerCompletionLevelHom J fg M (m + 1) ≫
        (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).map
          (G.map (homOfLE (Nat.le_succ m)).op)) x =
      moduleSpecΓFunctor.map (M₁.transitionIso m).hom
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          ((Spf (AdicRing.completion J fg)).ι m)).unit.app (M₁.obj (m + 1)))
          (moduleSpecΓFunctor.map (e.app (m + 1))
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
              ((Spf.completionIso J fg).hom.app (m + 1))).unit.app (M₀.obj (m + 1))) x))) := by
    refine (LinearMap.congr_fun (TauCeti.ModuleTower.transition_def G m).symm _).trans ?_
    refine (CoherentFormalModule.sectionsTower_obj_transition_apply
      (AdicRing.completion J fg).ideal M₁ m _).trans ?_
    exact congrArg (fun z ↦ moduleSpecΓFunctor.map (M₁.transitionIso m).hom
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        ((Spf (AdicRing.completion J fg)).ι m)).unit.app (M₁.obj (m + 1))) z))
      (specSectionsTowerCompletionLevelHom_apply J fg M (m + 1) x)
  exact hL.trans ((moduleSpecΓFunctor_map_square_transition
    ⟨(Spf.completionIso J fg).hom.naturality m⟩ (M₀.transitionIso m).hom
    (M₁.transitionIso m).hom (e.app m) (e.app (m + 1))
    ((e.naturality m).trans (Category.assoc _ _ _)) x).trans hR.symm)

private def specSectionsTowerIsoCompletion (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) :
    (specSectionsTower J).obj M ≅
      (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M) ⋙
        ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R)) := by
  refine NatIso.ofComponents (fun n ↦ asIso (specSectionsTowerCompletionLevelHom J fg M n.unop))
    ?_
  rintro ⟨m⟩ ⟨n⟩ ⟨h⟩
  have hle : n ≤ m := leOfHom h
  have heq : (⟨h⟩ : op m ⟶ op n) = (homOfLE hle).op := Subsingleton.elim _ _
  rw [heq]
  clear h heq
  induction m, hle using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hsucc : (homOfLE (hm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hm).op :=
      Subsingleton.elim _ _
    dsimp only [asIso_hom, Functor.comp_obj, Functor.comp_map] at ih ⊢
    rw [hsucc, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, ih, ← Category.assoc,
      specSectionsTowerCompletionLevelHom_succ J fg M m, Category.assoc,
      ← CategoryTheory.Functor.map_comp]

private lemma specSectionsTowerIsoCompletion_naturality (J : Ideal R) (fg : J.FG)
    {M N : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))} (f : M ⟶ N) :
    ((specSectionsTower J).map f) ≫ (specSectionsTowerIsoCompletion J fg N).hom =
      (specSectionsTowerIsoCompletion J fg M).hom ≫
        Functor.whiskerRight
          ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
            ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f))
          (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))) := by
  ext ⟨n⟩ x
  dsimp only [NatTrans.comp_app, specSectionsTowerIsoCompletion, NatIso.ofComponents_hom_app,
    asIso_hom, Functor.whiskerRight_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change specSectionsTowerCompletionLevelHom J fg N n (((specSectionsTower J).map f).app (op n) x) =
    ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)).app (op n)
        (specSectionsTowerCompletionLevelHom J fg M n x)
  rw [specSectionsTowerCompletionLevelHom_apply, specSectionsTowerCompletionLevelHom_apply]
  have hnatn := congrArg (·.app n) ((pullbackCompletionIso J fg).hom.naturality f)
  calc moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app N).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).hom.app n)).unit.app _)
          (moduleSpecΓFunctor.map (((CoherentFormalModule.pullback (specIso J).inv).map f).app n)
            x))
      = moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app N).app n)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullback ((Spf.completionIso J fg).hom.app n)).map
              (((CoherentFormalModule.pullback (specIso J).inv).map f).app n))
            (moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                ((Spf.completionIso J fg).hom.app n)).unit.app _) x)) :=
        congrArg (moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app N).app n))
          (moduleSpecΓFunctor_map_unit_naturality _ _ _)
    _ = moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback ((Spf.completionIso J fg).hom.app n)).map
              (((CoherentFormalModule.pullback (specIso J).inv).map f).app n) ≫
            ((pullbackCompletionIso J fg).hom.app N).app n)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              ((Spf.completionIso J fg).hom.app n)).unit.app _) x) :=
        (moduleSpecΓFunctor_map_comp_apply _ _ _).symm
    _ = moduleSpecΓFunctor.map
          (((pullbackCompletionIso J fg).hom.app M).app n ≫
            ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f).app n)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              ((Spf.completionIso J fg).hom.app n)).unit.app _) x) :=
        congrArg (fun k ↦ (moduleSpecΓFunctor.map k) _) hnatn
    _ = moduleSpecΓFunctor.map
          (((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f).app n)
          (moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app M).app n)
            (moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                ((Spf.completionIso J fg).hom.app n)).unit.app _) x)) :=
        moduleSpecΓFunctor_map_comp_apply _ _ _

private def limRestrictScalarsIso {R₀ S₀ : Type u} [Ring R₀] [Ring S₀] (φ : R₀ →+* S₀)
    (F : TauCeti.ModuleTower.{u} S₀) :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S₀ F.lim) ≅
      ModuleCat.of R₀ (TauCeti.ModuleTower.lim (F ⋙ ModuleCat.restrictScalars φ)) where
  hom := ModuleCat.ofHom (X := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S₀ F.lim))
    { toFun := fun (x : F.lim) ↦ ⟨x.val,
        (TauCeti.ModuleTower.mem_lim (F := F ⋙ ModuleCat.restrictScalars φ)).2 fun n ↦
          (LinearMap.congr_fun
            (TauCeti.ModuleTower.transition_def (F ⋙ ModuleCat.restrictScalars φ) n) _).trans
            ((LinearMap.congr_fun (TauCeti.ModuleTower.transition_def F n)
              (x.val (n + 1))).symm.trans ((TauCeti.ModuleTower.mem_lim (F := F)).1 x.property n))⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  inv := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S₀ F.lim))
    { toFun := fun (x : TauCeti.ModuleTower.lim (F ⋙ ModuleCat.restrictScalars φ)) ↦ ⟨x.val,
        (TauCeti.ModuleTower.mem_lim (F := F)).2 fun n ↦
          (LinearMap.congr_fun (TauCeti.ModuleTower.transition_def F n) _).trans
            ((LinearMap.congr_fun
              (TauCeti.ModuleTower.transition_def (F ⋙ ModuleCat.restrictScalars φ) n)
              (x.val (n + 1))).symm.trans
              ((TauCeti.ModuleTower.mem_lim
                (F := F ⋙ ModuleCat.restrictScalars φ)).1 x.property n))⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

private lemma limπ_limRestrictScalarsIso_hom {R₀ S₀ : Type u} [Ring R₀] [Ring S₀] (φ : R₀ →+* S₀)
    (F : TauCeti.ModuleTower.{u} S₀) (n : ℕ) (x : F.lim) :
    TauCeti.ModuleTower.limπ (F ⋙ ModuleCat.restrictScalars φ) n
        ((limRestrictScalarsIso φ F).hom x) =
      F.limπ n x :=
  (TauCeti.ModuleTower.limπ_apply _ n _).trans (TauCeti.ModuleTower.limπ_apply F n x).symm

private lemma limπ_limRestrictScalarsIso_inv {R₀ S₀ : Type u} [Ring R₀] [Ring S₀] (φ : R₀ →+* S₀)
    (F : TauCeti.ModuleTower.{u} S₀) (n : ℕ)
    (x : TauCeti.ModuleTower.lim (F ⋙ ModuleCat.restrictScalars φ)) :
    F.limπ n ((limRestrictScalarsIso φ F).inv x) =
      TauCeti.ModuleTower.limπ (F ⋙ ModuleCat.restrictScalars φ) n x :=
  (TauCeti.ModuleTower.limπ_apply F n _).trans (TauCeti.ModuleTower.limπ_apply _ n x).symm

/-- Under `coherentFormalModuleEquivSpecOfFG J fg`, the underlying `R`-module of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module `M` on `(Spec R)/V(J)` is
naturally isomorphic to the inverse limit `specSectionsLim J` of global sections on
`(Spec R)/V(J)`. -/
def coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso (J : Ideal R) (fg : J.FG)
    [IsNoetherianRing (R ⧸ J)] :
    (coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
        (ModuleCat.isFG (AdicCompletion J R)).ι ⋙
          ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R)) ≅
      specSectionsLim J :=
  NatIso.ofComponents
    (fun M ↦
      (limRestrictScalarsIso (algebraMap R (AdicCompletion J R))
        ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M))) ≪≫
      (TauCeti.ModuleTower.limEquivOfIso
        (specSectionsTowerIsoCompletion J fg M).symm).toModuleIso)
    fun {M N} f ↦ by
      ext x
      apply TauCeti.ModuleTower.lim_ext
      intro n
      let F_N := (specSectionsTower J).obj N
      let G_M := (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)
      let G_N := (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj N)
      let φ := algebraMap R (AdicCompletion J R)
      have h0 : (specSectionsTowerIsoCompletion J fg M).inv ≫ (specSectionsTower J).map f =
          Functor.whiskerRight
            ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
              ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f))
            (ModuleCat.restrictScalars φ) ≫
            (specSectionsTowerIsoCompletion J fg N).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc,
          ← specSectionsTowerIsoCompletion_naturality J fg f, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      have hval : (((specSectionsTower J).map f).app (op n)).hom
            (((specSectionsTowerIsoCompletion J fg M).inv.app (op n)).hom (G_M.limπ n x)) =
          ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom
            ((((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
              ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)).app
                (op n)).hom (G_M.limπ n x)) :=
        congrArg (fun k ↦ (k.app (op n)).hom (G_M.limπ n x)) h0
      have hL : F_N.limπ n
          ((((coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
            (ModuleCat.isFG (AdicCompletion J R)).ι ⋙ ModuleCat.restrictScalars φ).map f ≫
              (limRestrictScalarsIso φ G_N ≪≫
                (TauCeti.ModuleTower.limEquivOfIso
                  (specSectionsTowerIsoCompletion J fg N).symm).toModuleIso).hom) x) =
          ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom
            ((((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
              ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)).app
                (op n)).hom (G_M.limπ n x)) := by
        have heq :
            ((((coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
              (ModuleCat.isFG (AdicCompletion J R)).ι ⋙ ModuleCat.restrictScalars φ).map f ≫
                (limRestrictScalarsIso φ G_N ≪≫
                  (TauCeti.ModuleTower.limEquivOfIso
                    (specSectionsTowerIsoCompletion J fg N).symm).toModuleIso).hom) x) =
            TauCeti.ModuleTower.limMap (specSectionsTowerIsoCompletion J fg N).inv
              ((limRestrictScalarsIso φ G_N).hom
                (TauCeti.ModuleTower.limMap
                  ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
                    ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)) x)) :=
          TauCeti.ModuleTower.limEquivOfIso_apply (specSectionsTowerIsoCompletion J fg N).symm _
        refine (congrArg (F_N.limπ n) heq).trans ?_
        refine (LinearMap.congr_fun
          (TauCeti.ModuleTower.limπ_comp_limMap (specSectionsTowerIsoCompletion J fg N).inv n)
          _).trans ?_
        refine (congrArg (fun z ↦ ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom z)
          (limπ_limRestrictScalarsIso_hom φ G_N n _)).trans ?_
        exact congrArg (fun z ↦ ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom z)
          (LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap _ n) x)
      have hR : F_N.limπ n
          (((limRestrictScalarsIso φ G_M ≪≫
            (TauCeti.ModuleTower.limEquivOfIso
              (specSectionsTowerIsoCompletion J fg M).symm).toModuleIso).hom ≫
            (specSectionsLim J).map f) x) =
          (((specSectionsTower J).map f).app (op n)).hom
            (((specSectionsTowerIsoCompletion J fg M).inv.app (op n)).hom (G_M.limπ n x)) := by
        refine (LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap
          ((specSectionsTower J).map f) n) _).trans ?_
        refine congrArg (fun z ↦ (((specSectionsTower J).map f).app (op n)).hom z) ?_
        have heq :
            (limRestrictScalarsIso φ G_M ≪≫
              (TauCeti.ModuleTower.limEquivOfIso
                (specSectionsTowerIsoCompletion J fg M).symm).toModuleIso).hom x =
            TauCeti.ModuleTower.limMap (specSectionsTowerIsoCompletion J fg M).inv
              ((limRestrictScalarsIso φ G_M).hom x) :=
          TauCeti.ModuleTower.limEquivOfIso_apply
            (specSectionsTowerIsoCompletion J fg M).symm ((limRestrictScalarsIso φ G_M).hom x)
        refine (congrArg (TauCeti.ModuleTower.limπ ((specSectionsTower J).obj M) n) heq).trans ?_
        refine (LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap
          (specSectionsTowerIsoCompletion J fg M).inv n) _).trans ?_
        exact congrArg (fun z ↦ ((specSectionsTowerIsoCompletion J fg M).inv.app (op n)).hom z)
          (limπ_limRestrictScalarsIso_hom φ G_M n x)
      exact hL.trans (hval.symm.trans hR.symm)

/-- On level-`n` projections, the inverse of
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg` pulls a global section back
along `(Spf.completionIso J fg).hom.app n` and applies the pullback coherence isomorphism. -/
theorem coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ
    (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ) (y : ((specSectionsTower J).obj M).lim) :
    ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n
      ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).inv.app M y) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).hom
            (specIso J).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (by
              ext k
              rw [← cancel_mono (toScheme _ _ k), AdicThickeningSystem.comp_app, Category.assoc,
                specIsoSpfCompletion_inv_app_toScheme, specIso_inv_app_toScheme]
              exact congrArg (·.app k) (Spf.completionIso_hom_spfToSpec J fg))).hom.app
            M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).hom.app n)).unit.app
            (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n))
          (((specSectionsTower J).obj M).limπ n y)) := by
  refine Eq.trans ?_
    (specSectionsTowerCompletionLevelHom_apply J fg M n (((specSectionsTower J).obj M).limπ n y))
  have h1 : ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n
        ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).inv.app M y) =
      TauCeti.ModuleTower.limπ
        (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)) ⋙
            ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))) n
        ((TauCeti.ModuleTower.limEquivOfIso
          (specSectionsTowerIsoCompletion J fg M).symm).symm y) :=
    limπ_limRestrictScalarsIso_inv _ _ n _
  refine h1.trans ?_
  rw [TauCeti.ModuleTower.limEquivOfIso_symm_apply]
  exact LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap _ n) y

private lemma pullbackCompletionIso_comp_eq (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (h_eq : (Spf.completionIso J fg).inv ≫ (specIsoSpfCompletion J fg).inv = (specIso J).inv) :
    (CoherentFormalModule.pullback (Spf.completionIso J fg).inv).map
        ((pullbackCompletionIso J fg).hom.app M) ≫
      (CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (specIsoSpfCompletion J fg).inv).hom.app M ≫
        (CoherentFormalModule.pullbackCongr h_eq).hom.app M =
    (CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (Spf.completionIso J fg).hom).hom.app
        ((CoherentFormalModule.pullback (specIso J).inv).obj M) ≫
      (CoherentFormalModule.pullbackCongr (Spf.completionIso J fg).inv_hom_id).hom.app
        ((CoherentFormalModule.pullback (specIso J).inv).obj M) ≫
        (CoherentFormalModule.pullbackId _).hom.app
          ((CoherentFormalModule.pullback (specIso J).inv).obj M) := by
  let f := (Spf.completionIso J fg).inv
  let g := (Spf.completionIso J fg).hom
  let h := (specIso J).inv
  dsimp only [pullbackCompletionIso, Iso.trans_hom, NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have hcongr1 := congrArg (fun τ ↦ τ.app M)
    (CoherentFormalModule.pullbackComp_hom_comp_pullbackCongr_hom f
      (specIsoSpfCompletion_inv J fg).symm)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hcongr1
  rw [← Category.assoc ((CoherentFormalModule.pullback f).map
      ((CoherentFormalModule.pullbackCongr _).hom.app M)),
    hcongr1, Category.assoc]
  have htrans0 := congrArg (fun τ ↦ τ.hom.app M)
    (CoherentFormalModule.pullbackCongr_trans
      (congrArg (f ≫ ·) (specIsoSpfCompletion_inv J fg).symm) h_eq)
  dsimp only [Iso.trans_hom, NatTrans.comp_app] at htrans0
  rw [← htrans0, ← CoherentFormalModule.pullbackComp_assoc_app_assoc f g h M]
  have htrans := congrArg (fun τ ↦ τ.hom.app M)
    (CoherentFormalModule.pullbackCongr_trans (Category.assoc f g h)
      ((congrArg (f ≫ ·) (specIsoSpfCompletion_inv J fg).symm).trans h_eq))
  have htrans2 := congrArg (fun τ ↦ τ.hom.app M)
    (CoherentFormalModule.pullbackCongr_trans
      (congrArg (· ≫ h) (Spf.completionIso J fg).inv_hom_id) (Category.id_comp h))
  have hcongr := congrArg (fun τ ↦ τ.app M)
    (CoherentFormalModule.pullbackCongr_hom_whiskerLeft_pullbackComp_hom
      (Spf.completionIso J fg).inv_hom_id h)
  have hid := CoherentFormalModule.pullback_id_comp_app h M
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app] at htrans htrans2 hcongr
  rw [← htrans, htrans2, ← Category.assoc _ ((CoherentFormalModule.pullbackCongr _).hom.app _),
    ← hcongr, Category.assoc, hid]

private lemma completionIso_inv_hom_id_app (J : Ideal R) (fg : J.FG) (n : ℕ) :
    (Spf.completionIso J fg).inv.app n ≫ (Spf.completionIso J fg).hom.app n =
      𝟙 ((spf J).X n) := by
  rw [← AdicThickeningSystem.comp_app, (Spf.completionIso J fg).inv_hom_id,
    AdicThickeningSystem.id_app]

private lemma schemeModules_pullbackCompIsoId_factor {X Y : Scheme.{u}}
    {f : Y ⟶ X} {g : X ⟶ Y} {fg1 fg2 : Y ⟶ Y}
    (h1 : f ≫ g = fg1) (h2 : fg1 = fg2) (h3 : fg2 = 𝟙 Y) (M : Y.Modules) :
    ((Scheme.Modules.pullbackComp f g).hom.app M ≫
        (Scheme.Modules.pullbackCongr h1).hom.app M) ≫
      (Scheme.Modules.pullbackCongr h2).hom.app M ≫
        ((Scheme.Modules.pullbackCongr h3).hom.app M ≫
          (Scheme.Modules.pullbackId Y).hom.app M) =
      (Scheme.Modules.pullbackCompIsoId ((h1.trans h2).trans h3)).hom.app M := by
  subst h1 h2
  rw [Scheme.Modules.pullbackCompIsoId_hom_app]
  simp [Scheme.Modules.pullbackCongr]

private lemma coherentFormalModule_pullback_inv_hom_rhs
    {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : 𝔛 ≅ 𝔜) (N : CoherentFormalModule 𝔜) (n : ℕ) :
    ((CoherentFormalModule.pullbackComp e.inv e.hom).hom.app N).app n ≫
      ((CoherentFormalModule.pullbackCongr e.inv_hom_id).hom.app N).app n ≫
        ((CoherentFormalModule.pullbackId _).hom.app N).app n =
      (Scheme.Modules.pullbackCompIsoId (by rw [← AdicThickeningSystem.comp_app,
        e.inv_hom_id, AdicThickeningSystem.id_app] : e.inv.app n ≫ e.hom.app n = 𝟙 _)).hom.app
        (N.obj n) := by
  rw [CoherentFormalModule.pullbackComp_hom_app_app,
    CoherentFormalModule.pullbackCongr_hom_app_app,
    CoherentFormalModule.pullbackId_hom_app_app]
  exact schemeModules_pullbackCompIsoId_factor
    (AdicThickeningSystem.comp_app e.inv e.hom n).symm
    (congrArg (·.app n) e.inv_hom_id)
    (AdicThickeningSystem.id_app 𝔜 n)
    (N.obj n)

private lemma pullbackCompletionIso_comp_eq_app (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (h_eq : (Spf.completionIso J fg).inv ≫ (specIsoSpfCompletion J fg).inv = (specIso J).inv) :
    (Scheme.Modules.pullback ((Spf.completionIso J fg).inv.app n)).map
        (((pullbackCompletionIso J fg).hom.app M).app n) ≫
      ((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (specIsoSpfCompletion J fg).inv).hom.app M).app n ≫
        ((CoherentFormalModule.pullbackCongr h_eq).hom.app M).app n =
      (Scheme.Modules.pullbackCompIsoId (completionIso_inv_hom_id_app J fg n)).hom.app
        (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n) := by
  have hn := congrArg (·.app n) (pullbackCompletionIso_comp_eq J fg M h_eq)
  simp only [CoherentFormalModule.comp_app, CoherentFormalModule.pullback_map_app] at hn
  exact hn.trans (coherentFormalModule_pullback_inv_hom_rhs (Spf.completionIso J fg) _ n)

private lemma moduleSpecΓFunctor_map_inv_hom_cancel
    {R₀ S₀ : CommRingCat.{u}} {f : Spec R₀ ⟶ Spec S₀} {g : Spec S₀ ⟶ Spec R₀}
    (h : f ≫ g = 𝟙 (Spec R₀)) {M₀ : (Spec R₀).Modules} {N : (Spec S₀).Modules}
    (u : (Scheme.Modules.pullback g).obj M₀ ⟶ N)
    (v : (Scheme.Modules.pullback f).obj N ⟶ M₀)
    (huv : (Scheme.Modules.pullback f).map u ≫ v =
      (Scheme.Modules.pullbackCompIsoId h).hom.app M₀)
    (x : moduleSpecΓFunctor.obj N) (y : moduleSpecΓFunctor.obj M₀)
    (hy : moduleSpecΓFunctor.map u
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M₀) y) =
      x) :
    y = moduleSpecΓFunctor.map v
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) x) := by
  have h1 := congrArg (fun z ↦ moduleSpecΓFunctor.map v
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) z))
    hy.symm
  refine Eq.trans ?_ h1.symm
  refine (moduleSpecΓFunctor_map_pullbackCompIsoId_unit h M₀ y).symm.trans ?_
  refine (congrArg (fun k ↦ moduleSpecΓFunctor.map k _) huv.symm).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  exact congrArg (moduleSpecΓFunctor.map v) (moduleSpecΓFunctor_map_unit_naturality f u _).symm

/-- On level-`n` projections,
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg` pulls a global section back
along `(Spf.completionIso J fg).inv.app n` and applies the pullback coherence isomorphism. -/
theorem coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_hom_app_limπ
    (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).lim) :
    ((specSectionsTower J).obj M).limπ n
      ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).hom.app M x) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
            (specIsoSpfCompletion J fg).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (by
              ext k
              rw [← cancel_mono (toScheme _ _ k), AdicThickeningSystem.comp_app, Category.assoc,
                specIsoSpfCompletion_inv_app_toScheme, specIso_inv_app_toScheme]
              have hc := congrArg (·.app k) (Spf.completionIso_hom_spfToSpec J fg)
              rw [AdicThickeningSystem.comp_app, AdicThickeningSystem.comp_app,
                AdicThickeningSystem.ofScheme_map_app] at hc
              have hc' := congrArg ((Spf.completionIso J fg).inv.app k ≫ ·) hc.symm
              rw [← Category.assoc, ← AdicThickeningSystem.comp_app,
                (Spf.completionIso J fg).inv_hom_id, AdicThickeningSystem.id_app,
                Category.id_comp] at hc'
              exact hc')).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).inv.app n)).unit.app
            (((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M).obj n))
          (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
            ((CoherentFormalModule.pullback
              (specIsoSpfCompletion J fg).inv).obj M)).limπ n x)) := by
  have hx : (coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).inv.app M
      ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).hom.app M x) = x :=
    ConcreteCategory.congr_hom
      (Iso.hom_inv_id_app (coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg) M)
      x
  have hπ := congrArg
    (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n) hx
  have hπ' := coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ J fg M n
    ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).hom.app M x)
  have h_eq : (Spf.completionIso J fg).inv ≫ (specIsoSpfCompletion J fg).inv = (specIso J).inv := by
    rw [specIsoSpfCompletion_inv, Iso.inv_hom_id_assoc]
  exact moduleSpecΓFunctor_map_inv_hom_cancel (completionIso_inv_hom_id_app J fg n)
    (((pullbackCompletionIso J fg).hom.app M).app n)
    (((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (specIsoSpfCompletion J fg).inv).hom.app M).app n ≫
      ((CoherentFormalModule.pullbackCongr h_eq).hom.app M).app n)
    (pullbackCompletionIso_comp_eq_app J fg M n h_eq) _ _ (hπ'.symm.trans hπ)

/-- **Coherent formal modules on `(Spec R)/V(J)` over a Noetherian ring** (Stacks, Lemma 30.23.1):
for any ideal `J` of a Noetherian ring `R`, coherent formal modules on the formal completion of
`Spec R` along `V(J)` are equivalent to finite modules over the `J`-adic completion
`AdicCompletion J R`. -/
-- `@[expose]` is forced by dependent typing: the inverse module must reduce to the limit in the
-- type of `coherentFormalModuleEquivSpecInverseCompFiniteReductionIso_hom_app_reductionπ`.
@[expose, stacks 087W]
def coherentFormalModuleEquivSpec (J : Ideal R) [IsNoetherianRing R] :
    FGModuleCat.{u} (AdicCompletion J R) ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  coherentFormalModuleEquivSpecOfFG J (IsNoetherian.noetherian J)

/-- `coherentFormalModuleEquivSpec J` preserves addition of morphisms. -/
instance (J : Ideal R) [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).functor.Additive := by
  have fg : J.FG := IsNoetherian.noetherian J
  exact inferInstanceAs (coherentFormalModuleEquivSpecOfFG J fg).functor.Additive

/-- The inverse of `coherentFormalModuleEquivSpec J` transports along
`(specIsoSpfCompletion J _).inv` and takes the inverse limit of levelwise global sections over
the completed ring. -/
@[simp]
theorem coherentFormalModuleEquivSpec_inverse (J : Ideal R) [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).inverse =
      CoherentFormalModule.pullback (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv ⋙
        @CoherentFormalModule.finiteSectionsLim _ _
          (AdicRing.completion J (IsNoetherian.noetherian J)).ideal
          (AdicCompletion.isAdicComplete_self J (IsNoetherian.noetherian J)).toIsPrecomplete :=
  coherentFormalModuleEquivSpecOfFG_inverse J (IsNoetherian.noetherian J)

/-- Under `coherentFormalModuleEquivSpec J`, transporting the coherent formal module associated to
a finite `AdicCompletion J R`-module `M` along `(specIsoSpfCompletion J _).inv` has
global-sections tower naturally isomorphic to the reduction tower of `M` over the completed ring. -/
def coherentFormalModuleEquivSpecFunctorCompFiniteSectionsTowerIso (J : Ideal R)
    [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).functor ⋙
        CoherentFormalModule.pullback (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv ⋙
          CoherentFormalModule.finiteSectionsTower
            (AdicRing.completion J (IsNoetherian.noetherian J)).ideal ≅
      TauCeti.ModuleTower.finiteReduction
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal :=
  coherentFormalModuleEquivSpecOfFGFunctorCompFiniteSectionsTowerIso J (IsNoetherian.noetherian J)

/-- Under `coherentFormalModuleEquivSpec J`, the reduction tower of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module on `(Spec R)/V(J)` is
naturally isomorphic to the global-sections tower over the completed ring. -/
def coherentFormalModuleEquivSpecInverseCompFiniteReductionIso (J : Ideal R)
    [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).inverse ⋙
        TauCeti.ModuleTower.finiteReduction
          (AdicRing.completion J (IsNoetherian.noetherian J)).ideal ≅
      CoherentFormalModule.pullback (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv ⋙
        CoherentFormalModule.finiteSectionsTower
          (AdicRing.completion J (IsNoetherian.noetherian J)).ideal :=
  coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso J (IsNoetherian.noetherian J)

/-- The reductions-to-sections comparison for `coherentFormalModuleEquivSpec J` is induced by the
projections from the inverse limit over the completed ring. -/
@[simp]
theorem coherentFormalModuleEquivSpecInverseCompFiniteReductionIso_hom_app_reductionπ
    (J : Ideal R) [IsNoetherianRing R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower
      (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
      ((CoherentFormalModule.pullback
        (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).lim) :
    dsimp% only [CategoryTheory.Functor.comp_obj, CategoryTheory.ObjectProperty.ι_obj,
      FGModuleCat.obj_carrier]
    (((coherentFormalModuleEquivSpecInverseCompFiniteReductionIso J).hom.app M).hom.app
      (op n)).hom
      (TauCeti.ModuleTower.reductionπ
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal
        ((coherentFormalModuleEquivSpec J).inverse.obj M).obj n x) =
      ((CoherentFormalModule.sectionsTower
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
        ((CoherentFormalModule.pullback
          (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).limπ n x :=
  coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso_hom_app_reductionπ
    J (IsNoetherian.noetherian J) M n x

/-- Under `coherentFormalModuleEquivSpec J`, the underlying `R`-module of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module `M` on `(Spec R)/V(J)` is
naturally isomorphic to `specSectionsLim J`, derived from
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso`. -/
def coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso (J : Ideal R)
    [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).inverse ⋙
        (ModuleCat.isFG (AdicCompletion J R)).ι ⋙
          ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R)) ≅
      specSectionsLim J :=
  coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J (IsNoetherian.noetherian J)

/-- On level-`n` projections, the inverse of
`coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J` pulls a global section back along
`(Spf.completionIso J _).hom.app n` and applies the pullback coherence isomorphism. -/
theorem coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso_inv_app_limπ
    (J : Ideal R) [IsNoetherianRing R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ) (y : ((specSectionsTower J).obj M).lim) :
    ((CoherentFormalModule.sectionsTower
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
        ((CoherentFormalModule.pullback
          (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).limπ n
      ((coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J).inv.app M y) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp
            (Spf.completionIso J (IsNoetherian.noetherian J)).hom
            (specIso J).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (by
              ext k
              have hsp := specIsoSpfCompletion_inv_app_toScheme J (IsNoetherian.noetherian J) k
              rw [← cancel_mono (toScheme _ _ k), AdicThickeningSystem.comp_app, Category.assoc,
                hsp, specIso_inv_app_toScheme]
              exact congrArg (·.app k) (Spf.completionIso_hom_spfToSpec J
                (IsNoetherian.noetherian J)))).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J (IsNoetherian.noetherian J)).hom.app n)).unit.app
            (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n))
          (((specSectionsTower J).obj M).limπ n y)) :=
  coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ
    J (IsNoetherian.noetherian J) M n y

/-- On level-`n` projections, `coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J` pulls
a global section back along `(Spf.completionIso J _).inv.app n` and applies the pullback coherence
isomorphism. -/
theorem coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso_hom_app_limπ
    (J : Ideal R) [IsNoetherianRing R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower
      (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
      ((CoherentFormalModule.pullback
        (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).lim) :
    ((specSectionsTower J).obj M).limπ n
      ((coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J).hom.app M x) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp
            (Spf.completionIso J (IsNoetherian.noetherian J)).inv
            (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (by
              ext k
              have hsp := specIsoSpfCompletion_inv_app_toScheme J (IsNoetherian.noetherian J) k
              rw [← cancel_mono (toScheme _ _ k), AdicThickeningSystem.comp_app, Category.assoc,
                hsp, specIso_inv_app_toScheme]
              have hc := congrArg (·.app k) (Spf.completionIso_hom_spfToSpec J
                (IsNoetherian.noetherian J))
              rw [AdicThickeningSystem.comp_app, AdicThickeningSystem.comp_app,
                AdicThickeningSystem.ofScheme_map_app] at hc
              have hc' := congrArg ((Spf.completionIso J
                (IsNoetherian.noetherian J)).inv.app k ≫ ·) hc.symm
              rw [← Category.assoc, ← AdicThickeningSystem.comp_app,
                (Spf.completionIso J (IsNoetherian.noetherian J)).inv_hom_id,
                AdicThickeningSystem.id_app, Category.id_comp] at hc'
              exact hc')).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J (IsNoetherian.noetherian J)).inv.app n)).unit.app
            (((CoherentFormalModule.pullback
              (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M).obj n))
          (((CoherentFormalModule.sectionsTower
            (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
            ((CoherentFormalModule.pullback
              (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).limπ n x)) :=
  coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_hom_app_limπ
    J (IsNoetherian.noetherian J) M n x

end

end AlgebraicGeometry.Scheme.formalCompletion
