/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModelCategory.KInjective.ModelStructure
public import TauCeti.AlgebraicTopology.DGNerve.FullSubcategory
public import TauCeti.CategoryTheory.DG.CochainComplex.KInjective

import TauCeti.Algebra.Homology.ModelCategory.Grothendieck

/-!
# The fibrant injective DG model and replacement DG comparison

Let `C` be an `R`-linear abelian category. Alongside the full DG subcategory
`TauCeti.KInjectiveDGCategory C` of all K-injective cochain complexes, the complexes that are
fibrant in the injective model structure on `CochainComplex C ℤ` — namely, K-injective complexes
whose terms are injective objects of `C` — form the nested full DG subcategory
`TauCeti.FibrantInjectiveDGCategory C`.

Over any `R`-linear abelian category:
* any two K-injective replacements `i₁ : K ⟶ I₁` and `i₂ : K ⟶ I₂` of a complex `K` are linked by
  a homotopy equivalence `e : HomotopyEquiv I₁ I₂` with `i₁ ≫ e.hom` homotopic to `i₂` whose
  forward map represents an equivalence edge in `dgNerve R (KInjectiveDGCategory C)`
  (`TauCeti.KInjectiveDGCategory.exists_replacementDGComparison`) and induces homotopy equivalences
  on all `R`-linear Hom complexes via `TauCeti.linearHomComplexPostcompHomotopyEquiv` and
  `TauCeti.linearHomComplexPrecompHomotopyEquiv`;
* the full DG inclusion `TauCeti.FibrantInjectiveDGCategory.toKInjectiveDGCategory R C` is
  quasi-fully faithful, its dg nerve is fully faithful on right mapping spaces, and its degree-zero
  homotopy category embeds fully faithfully into `DerivedCategory C`.

When `C` is Grothendieck abelian (`IsGrothendieckAbelian.{w'} C`), functorial fibrant replacement
in `CochainComplex.modelCategoryInjective` embeds every K-injective complex quasi-isomorphically
into a fibrant complex, so `toKInjectiveDGCategory R C` is a quasi-equivalence of DG categories
(`TauCeti.FibrantInjectiveDGCategory.isQuasiEquivalence_toKInjectiveDGCategory`). Consequently
`(dgNerve R (FibrantInjectiveDGCategory C)).HomotopyCategory` is equivalent to `DerivedCategory C`
(`TauCeti.FibrantInjectiveDGCategory.dgNerveHomotopyCategoryEquiv`).

## References

* J. Lurie, *Higher Algebra*, Proposition 1.3.5.3, Definition 1.3.5.8, and Proposition 1.3.5.15.
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory

universe w' w v u

namespace TauCeti

variable (R : Type v) [CommRing R] (C : Type u) [Category.{v} C] [Abelian C]

namespace KInjectiveDGCategory

variable {C} [Linear R C]

/-- Any two K-injective replacements `i₁ : K ⟶ I₁` and `i₂ : K ⟶ I₂` of a cochain complex `K` are
linked by a homotopy equivalence `e : HomotopyEquiv I₁ I₂` with `i₁ ≫ e.hom` homotopic to `i₂`
whose forward chain map defines an equivalence edge in `dgNerve R (KInjectiveDGCategory C)`. -/
theorem exists_replacementDGComparison {K I₁ I₂ : CochainComplex C ℤ}
    [I₁.IsKInjective] [I₂.IsKInjective] (i₁ : K ⟶ I₁) (i₂ : K ⟶ I₂)
    [QuasiIso i₁] [QuasiIso i₂] :
    ∃ e : HomotopyEquiv I₁ I₂, Nonempty (Homotopy (i₁ ≫ e.hom) i₂) ∧
      (dgNerve.edgeMk R (KInjectiveDGCategory C)
        ⟨_, ofHom_mem_dgCycles R C e.hom⟩).IsEquivalence := by
  obtain ⟨e, he⟩ := CochainComplex.IsKInjective.exists_homotopyEquiv i₁ i₂
  have : QuasiIso e.hom := e.quasiIso_hom
  exact ⟨e, he, (isEquivalence_edgeMk_iff_quasiIso R C e.hom).2 inferInstance⟩

end KInjectiveDGCategory

/-- The full DG subcategory of `CochainComplex C ℤ` spanned by K-injective complexes whose terms
are injective objects of `C`, i.e. the fibrant objects for the injective model structure
`CochainComplex.modelCategoryInjective`. -/
abbrev FibrantInjectiveDGCategory :=
  DGFullSubcategory (fun K : CochainComplex C ℤ ↦
    (∀ n : ℤ, Injective (K.X n)) ∧ K.IsKInjective)

open scoped CochainComplex.modelCategoryInjective in
/-- A cochain complex belongs to `FibrantInjectiveDGCategory C` if and only if it is fibrant in
`CochainComplex.modelCategoryInjective`. -/
theorem mem_fibrantInjectiveDGCategory_iff_isFibrant {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) :
    ((∀ n : ℤ, Injective (K.X n)) ∧ K.IsKInjective) ↔ HomotopicalAlgebra.IsFibrant K :=
  (CochainComplex.modelCategoryInjective.isFibrant_iff K).symm

namespace FibrantInjectiveDGCategory

variable [Linear R C]

/-- The full DG inclusion from fibrant injective complexes into all K-injective complexes. -/
@[expose]
def toKInjectiveDGCategory :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
      (FibrantInjectiveDGCategory C) (KInjectiveDGCategory C) :=
  DGFullSubcategory.inclusionOfLE R fun _ h ↦ h.2

/-- `toKInjectiveDGCategory` forgets degreewise injectivity while retaining the complex. -/
@[simp]
theorem toKInjectiveDGCategory_obj (X : FibrantInjectiveDGCategory C) :
    (toKInjectiveDGCategory R C).obj X = ⟨X.obj, X.property.2⟩ :=
  DGFullSubcategory.inclusionOfLE_obj R _ X

/-- The inclusion of fibrant injective complexes into all K-injective complexes is quasi-fully
faithful. -/
theorem isQuasiFullyFaithful_toKInjectiveDGCategory :
    EnrichedFunctor.IsQuasiFullyFaithful (toKInjectiveDGCategory R C) :=
  DGFullSubcategory.isQuasiFullyFaithful_inclusionOfLE _

instance : (toKInjectiveDGCategory R C).mapDGHomotopyCategory.Full :=
  (isQuasiFullyFaithful_toKInjectiveDGCategory R C).full_mapDGHomotopyCategory

instance : (toKInjectiveDGCategory R C).mapDGHomotopyCategory.Faithful :=
  (isQuasiFullyFaithful_toKInjectiveDGCategory R C).faithful_mapDGHomotopyCategory

/-- On differential graded nerves, the inclusion of fibrant injective complexes into all
K-injective complexes is fully faithful on right mapping spaces. -/
instance : SSet.IsFullyFaithful (toKInjectiveDGCategory R C).mapDGNerve := by
  dsimp only [toKInjectiveDGCategory]
  infer_instance

/-- A chain map between fibrant injective complexes defines a closed degree-zero morphism in
`FibrantInjectiveDGCategory C`. -/
theorem ofHom_mem_dgCycles {K L : CochainComplex C ℤ}
    (hK : (∀ n : ℤ, Injective (K.X n)) ∧ K.IsKInjective)
    (hL : (∀ n : ℤ, Injective (L.X n)) ∧ L.IsKInjective) (f : K ⟶ L) :
    CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, hK⟩ : FibrantInjectiveDGCategory C) ⟨L, hL⟩ := by
  apply (mem_dgCycles R).2
  rw [DGFullSubcategory.dgDifferential_eq, dgDifferential_linearHomComplex]
  exact CochainComplex.HomComplex.δ_ofHom f

section DerivedCategory

variable [HasDerivedCategory.{w} C]

/-- The comparison functor from `H⁰(FibrantInjectiveDGCategory C)` to `DerivedCategory C`, defined
by composing the inclusion into `KInjectiveDGCategory C` with
`KInjectiveDGCategory.toDerivedCategory`. -/
@[expose]
def toDerivedCategory : DGHomotopyCategory R (FibrantInjectiveDGCategory C) ⥤ DerivedCategory C :=
  (toKInjectiveDGCategory R C).mapDGHomotopyCategory ⋙ KInjectiveDGCategory.toDerivedCategory R C

/-- `toDerivedCategory` sends a fibrant injective complex to `Qh` of its class in `K(C)`. -/
@[simp]
theorem toDerivedCategory_obj (X : DGHomotopyCategory R (FibrantInjectiveDGCategory C)) :
    (toDerivedCategory R C).obj X =
      Qh.obj ((HomotopyCategory.quotient C _).obj (DGHomotopyCategory.underlying R X).obj) :=
  (rfl)

/-- `toDerivedCategory` sends the class of `Cochain.ofHom f` to `Qh` of the homotopy class of
`f`. -/
@[simp]
theorem toDerivedCategory_map_homOf {K L : CochainComplex C ℤ}
    (hK : (∀ n : ℤ, Injective (K.X n)) ∧ K.IsKInjective)
    (hL : (∀ n : ℤ, Injective (L.X n)) ∧ L.IsKInjective) (f : K ⟶ L)
    (hf : CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, hK⟩ : FibrantInjectiveDGCategory C) ⟨L, hL⟩) :
    (toDerivedCategory R C).map (DGHomotopyCategory.homOf R _ hf) =
      Qh.map ((HomotopyCategory.quotient C _).map f) := by
  have : K.IsKInjective := hK.2
  have : L.IsKInjective := hL.2
  dsimp only [toDerivedCategory, Functor.comp_map, toKInjectiveDGCategory]
  rw [DGFullSubcategory.mapDGHomotopyCategory_inclusionOfLE_map_homOf, Functor.map_comp,
    Functor.map_comp, KInjectiveDGCategory.toDerivedCategory_map_homOf, eqToHom_map, eqToHom_map]
  exact ((conj_eqToHom_iff_heq' (C := DerivedCategory C) _ _ _ _).2 HEq.rfl).symm

instance : (toDerivedCategory R C).Full :=
  inferInstanceAs ((toKInjectiveDGCategory R C).mapDGHomotopyCategory ⋙
    KInjectiveDGCategory.toDerivedCategory R C).Full

instance : (toDerivedCategory R C).Faithful :=
  inferInstanceAs ((toKInjectiveDGCategory R C).mapDGHomotopyCategory ⋙
    KInjectiveDGCategory.toDerivedCategory R C).Faithful

/-- The comparison functor from `H⁰(FibrantInjectiveDGCategory C)` to `DerivedCategory C` is fully
faithful. -/
def fullyFaithfulToDerivedCategory : (toDerivedCategory R C).FullyFaithful :=
  .ofFullyFaithful _

omit [HasDerivedCategory.{w} C] in
/-- An edge represented by a chain map in `FibrantInjectiveDGCategory C` is an equivalence in the
differential graded nerve if and only if the chain map is a quasi-isomorphism. -/
theorem isEquivalence_edgeMk_iff_quasiIso {K L : CochainComplex C ℤ}
    (hK : (∀ n : ℤ, Injective (K.X n)) ∧ K.IsKInjective)
    (hL : (∀ n : ℤ, Injective (L.X n)) ∧ L.IsKInjective) (f : K ⟶ L)
    (hf : CochainComplex.HomComplex.Cochain.ofHom f ∈
      dgCycles R (⟨K, hK⟩ : FibrantInjectiveDGCategory C) ⟨L, hL⟩ :=
        ofHom_mem_dgCycles R C hK hL f) :
    (dgNerve.edgeMk R (FibrantInjectiveDGCategory C) ⟨_, hf⟩).IsEquivalence ↔ QuasiIso f := by
  let := HasDerivedCategory.standard C
  rw [dgNerve.isEquivalence_edgeMk_iff]
  refine (isIso_iff_of_reflects_iso _ (toDerivedCategory R C)).symm.trans ?_
  have h := congrArg (fun g ↦ IsIso g) (toDerivedCategory_map_homOf R C hK hL f hf)
  exact (Iff.of_eq h).trans ((DerivedCategory.isIso_Qh_map_iff _).trans
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).trans
      (HomologicalComplex.mem_quasiIso_iff f)))

end DerivedCategory

section Grothendieck

open CochainComplex.modelCategoryInjective

variable [IsGrothendieckAbelian.{w'} C]

/-- In a Grothendieck abelian category, the full DG inclusion of fibrant injective complexes into
all K-injective complexes is a quasi-equivalence of DG categories. -/
theorem isQuasiEquivalence_toKInjectiveDGCategory :
    EnrichedFunctor.IsQuasiEquivalence (toKInjectiveDGCategory R C) := by
  refine (DGFullSubcategory.isQuasiEquivalence_inclusionOfLE_iff _).2 fun Y ↦ ?_
  have : Y.obj.IsKInjective := Y.property
  let X := (fibrantReplacement.{w'} C).obj Y.obj
  let ι : Y.obj ⟶ X := (ιFibrantReplacement.{w'} C).app Y.obj
  have hX : (∀ n : ℤ, Injective (X.X n)) ∧ X.IsKInjective := ⟨inferInstance, inferInstance⟩
  let φ : DGHomotopyCategory.of R Y ⟶
      DGHomotopyCategory.of R (⟨X, hX.2⟩ : KInjectiveDGCategory C) :=
    DGHomotopyCategory.homOf R _ (KInjectiveDGCategory.ofHom_mem_dgCycles R C ι)
  have hφ : IsIso φ :=
    (dgNerve.isEquivalence_edgeMk_iff
      (f := ⟨_, KInjectiveDGCategory.ofHom_mem_dgCycles R C ι⟩)).1
      ((KInjectiveDGCategory.isEquivalence_edgeMk_iff_quasiIso R C ι).2 inferInstance)
  exact ⟨X, hX, ⟨(asIso φ).symm⟩⟩

instance : (toKInjectiveDGCategory R C).mapDGHomotopyCategory.IsEquivalence :=
  (isQuasiEquivalence_toKInjectiveDGCategory.{w'} R C).isEquivalence_mapDGHomotopyCategory

instance : (SSet.mapHomotopyCategory (toKInjectiveDGCategory R C).mapDGNerve).IsEquivalence :=
  (isQuasiEquivalence_toKInjectiveDGCategory.{w'} R C).isEquivalence_mapHomotopyCategory_mapDGNerve

instance [HasDerivedCategory.{w} C] : (toDerivedCategory R C).IsEquivalence :=
  inferInstanceAs ((toKInjectiveDGCategory R C).mapDGHomotopyCategory ⋙
    KInjectiveDGCategory.toDerivedCategory R C).IsEquivalence

/-- In a Grothendieck abelian category, the homotopy category of the differential graded nerve of
fibrant injective complexes is equivalent to the unbounded derived category `DerivedCategory C`. -/
def dgNerveHomotopyCategoryEquiv [HasDerivedCategory.{w} C] :
    (dgNerve R (FibrantInjectiveDGCategory C)).HomotopyCategory ≌ DerivedCategory C :=
  (dgNerve.homotopyCategoryEquiv R _).symm.trans (toDerivedCategory R C).asEquivalence

/-- The forward functor of `dgNerveHomotopyCategoryEquiv` factors through `H⁰` of
`FibrantInjectiveDGCategory C` followed by `toDerivedCategory`. -/
@[simp]
theorem dgNerveHomotopyCategoryEquiv_functor [HasDerivedCategory.{w} C] :
    (dgNerveHomotopyCategoryEquiv R C).functor =
      dgNerve.fromHomotopyCategory R (FibrantInjectiveDGCategory C) ⋙ toDerivedCategory R C := by
  simp [dgNerveHomotopyCategoryEquiv]

end Grothendieck

end FibrantInjectiveDGCategory

end TauCeti
