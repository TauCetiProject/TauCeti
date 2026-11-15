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
* `specSectionsTower J` and `specFiniteSectionsTower J`: the additive, fully faithful global-section
  tower functors on `CoherentFormalModule ((Spec R).formalCompletion V(J))` for any commutative
  ring `R`, which form an equivalence when `R` is Noetherian
  (`isEquivalence_specFiniteSectionsTower`) and fail to be essentially surjective without
  Noetherianity even for `J = ⊥` (`not_essSurj_specFiniteSectionsTower_mvPolynomial`).
* `coherentFormalModuleEquivSpecSelf`: when `R` is Noetherian and `J`-adically complete, coherent
  formal modules on `(Spec R)/V(J)` are equivalent to finite `R`-modules (`FGModuleCat R`), with
  inverse functor `specFiniteSectionsLim J` taking the inverse limit of levelwise global sections.
* `coherentFormalModuleEquivSpecOfFG` and `coherentFormalModuleEquivSpec` (Stacks, Lemma 30.23.1):
  for any finitely generated ideal `J` with `R ⧸ J` Noetherian — and in particular for any ideal `J`
  of a Noetherian ring `R` — coherent formal modules on `(Spec R)/V(J)` are equivalent to finite
  modules over the `J`-adic completion `AdicCompletion J R`, combining
  `specIsoSpfCompletion J fg : (Spec R)/V(J) ≅ Spf R̂` with `Spf.coherentFormalModuleEquiv` and
  Noetherianity of `AdicCompletion J R` (`Ideal.isNoetherianRing_adicCompletion_of_fg`).

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

open CategoryTheory AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

noncomputable section

variable {R : Type u} [CommRing R]

/-- The tower of levelwise global sections of a coherent formal module on the formal completion of
`Spec R` along `V(J)`, obtained by transporting `CoherentFormalModule.sectionsTower J` across
`specIso J`. -/
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

/-- The global-sections tower of a coherent formal module on `(Spec R)/V(J)`, valued in `J`-adic
systems of `R`-modules with finite first term. -/
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

/-- Over a Noetherian ring `R`, taking levelwise global sections identifies coherent formal modules
on `(Spec R)/V(J)` with `J`-adic systems of `R`-modules having finite first term, without any
`J`-adic completeness assumption on `R`. -/
instance isEquivalence_specFiniteSectionsTower (J : Ideal R) [IsNoetherianRing R] :
    (specFiniteSectionsTower J).IsEquivalence :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsTower J).IsEquivalence

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
def specSectionsLim (J : Ideal R) :
    CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) ⥤
      ModuleCat.{u} R :=
  CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.sectionsLim J

instance (J : Ideal R) : (specSectionsLim J).Additive :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.sectionsLim J).Additive

/-- Over a `J`-adically precomplete ring `R`, the inverse limit of levelwise global sections of a
coherent formal module on `(Spec R)/V(J)` as a finite `R`-module. -/
def specFiniteSectionsLim (J : Ideal R) [IsPrecomplete J R] :
    CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) ⥤
      FGModuleCat.{u} R :=
  CoherentFormalModule.pullback (specIso J).inv ⋙ CoherentFormalModule.finiteSectionsLim J

instance (J : Ideal R) [IsPrecomplete J R] : (specFiniteSectionsLim J).Additive :=
  inferInstanceAs (CoherentFormalModule.pullback (specIso J).inv ⋙
    CoherentFormalModule.finiteSectionsLim J).Additive

/-- **Coherent formal modules on `(Spec R)/V(J)` over a complete Noetherian ring** (Stacks,
Lemma 30.23.1): when `R` is Noetherian and `J`-adically complete, coherent formal modules on the
formal completion of `Spec R` along `V(J)` are equivalent to finite `R`-modules. -/
@[stacks 087W]
def coherentFormalModuleEquivSpecSelf (J : Ideal R) [IsNoetherianRing R] [IsAdicComplete J R] :
    FGModuleCat.{u} R ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  (CoherentFormalModule.spfEquiv J).trans (CoherentFormalModule.pullbackEquiv (specIso J))

@[simp]
theorem coherentFormalModuleEquivSpecSelf_inverse (J : Ideal R) [IsNoetherianRing R]
    [IsAdicComplete J R] :
    (coherentFormalModuleEquivSpecSelf J).inverse = specFiniteSectionsLim J := by
  simp [coherentFormalModuleEquivSpecSelf, specFiniteSectionsLim]

/-- **Coherent formal modules on `(Spec R)/V(J)` for a finitely generated ideal with Noetherian
quotient** (Stacks, Lemma 30.23.1): if `J` is finitely generated and `R ⧸ J` is Noetherian, then
`AdicCompletion J R` is Noetherian and coherent formal modules on `(Spec R)/V(J)` are equivalent to
finite modules over `AdicCompletion J R`. -/
@[stacks 087W]
def coherentFormalModuleEquivSpecOfFG (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)] :
    FGModuleCat.{u} (AdicCompletion J R) ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  letI := Ideal.isNoetherianRing_adicCompletion_of_fg J fg
  (Spf.coherentFormalModuleEquiv (AdicRing.completion J fg)).trans
    (CoherentFormalModule.pullbackEquiv (specIsoSpfCompletion J fg))

/-- **Coherent formal modules on `(Spec R)/V(J)` over a Noetherian ring** (Stacks, Lemma 30.23.1):
for any ideal `J` of a Noetherian ring `R`, coherent formal modules on the formal completion of
`Spec R` along `V(J)` are equivalent to finite modules over the `J`-adic completion
`AdicCompletion J R`. -/
@[stacks 087W]
def coherentFormalModuleEquivSpec (J : Ideal R) [IsNoetherianRing R] :
    FGModuleCat.{u} (AdicCompletion J R) ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  coherentFormalModuleEquivSpecOfFG J (IsNoetherian.noetherian J)

end

end AlgebraicGeometry.Scheme.formalCompletion
