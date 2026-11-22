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

end

end AlgebraicGeometry.Scheme.formalCompletion
