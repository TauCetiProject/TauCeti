/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic

import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# Normalized category chains and the homology long exact sequence

When `A` is abelian with coproducts of size `max u₁ v₁`, this file develops:
1. **Normalized category chains** (`TauCeti.normalizedCategoryChainComplexFunctor`,
   `TauCeti.normalizedCategoryChainComplex`) together with the Dold–Kan homotopy equivalence
   `TauCeti.normalizedCategoryChainComplexHomotopyEquiv`, homology isomorphism
   `TauCeti.normalizedCategoryHomologyIso`, and vanishing of degenerate simplices
   (`TauCeti.categoryChainComplex.ι_σ_toNormalized_f`,
   `TauCeti.categoryChainComplex.ι₁_id_toNormalized_f`).
2. **Long exact homology sequence**: under `AB4OfSize.{max u₁ v₁} A`,
   `CategoryTheory.ShortComplex.ShortExact.map_categoryChainComplex` shows exactness of
   `categoryChainComplexFunctor C A`, yielding connecting homomorphisms `TauCeti.categoryHomology.δ`
   and exactness lemmas `homology_exact₁`, `homology_exact₂`, `homology_exact₃`.

## References
* [Daniel Quillen, *Higher algebraic K-theory: I*][quillen1973], §1.
* [Charles A. Weibel, *The K-book*][weibel2013], Chapter IV, §3.5.
-/

public noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe v₁ u₁ v₂ u₂ v₃ u₃ v u w

namespace TauCeti

/-! ### Normalized category chain complex and Dold–Kan comparison -/

section Normalized

variable (C : Type u₁) [Category.{v₁} C] (A : Type u) [Category.{v} A]
  [Abelian A] [HasCoproducts.{max u₁ v₁} A]

/-- The additive functor sending `M : C ⥤ A` to the normalized Moore complex of
`categorySimplicialObject C M`. -/
@[expose, implicit_reducible]
def normalizedCategoryChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ AlgebraicTopology.normalizedMooreComplex A

variable {A}

/-- The normalized chain complex of a category `C` with coefficients in `M : C ⥤ A`. -/
abbrev normalizedCategoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (normalizedCategoryChainComplexFunctor C A).obj M

variable {C} in
/-- The chain map on normalized category chains induced by `α : M ⟶ N`. -/
abbrev normalizedCategoryChainComplexMap {M N : C ⥤ A} (α : M ⟶ N) :
    normalizedCategoryChainComplex C M ⟶ normalizedCategoryChainComplex C N :=
  (normalizedCategoryChainComplexFunctor C A).map α

/-- Split monomorphic inclusion of normalized into unnormalized category chains. -/
def inclusionNormalizedCategoryChainComplex (M : C ⥤ A) :
    normalizedCategoryChainComplex C M ⟶ categoryChainComplex C M :=
  AlgebraicTopology.inclusionOfMooreComplexMap (categorySimplicialObject C M)

instance (M : C ⥤ A) : IsSplitMono (inclusionNormalizedCategoryChainComplex C M) :=
  ⟨⟨AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap (categorySimplicialObject C M)⟩⟩

/-- Dold–Kan projection `PInfty` from unnormalized onto normalized category chains. -/
def toNormalizedCategoryChainComplex (M : C ⥤ A) :
    categoryChainComplex C M ⟶ normalizedCategoryChainComplex C M :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (categorySimplicialObject C M)

@[reassoc (attr := simp)]
lemma inclusionNormalized_comp_toNormalized (M : C ⥤ A) :
    inclusionNormalizedCategoryChainComplex C M ≫ toNormalizedCategoryChainComplex C M =
      𝟙 (normalizedCategoryChainComplex C M) :=
  (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap (categorySimplicialObject C M)).id

@[reassoc]
lemma toNormalized_comp_inclusionNormalized (M : C ⥤ A) :
    toNormalizedCategoryChainComplex C M ≫ inclusionNormalizedCategoryChainComplex C M =
      AlgebraicTopology.DoldKan.PInfty :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap _

variable {C} in
@[reassoc]
lemma inclusionNormalizedCategoryChainComplex_naturality {M N : C ⥤ A} (α : M ⟶ N) :
    normalizedCategoryChainComplexMap α ≫ inclusionNormalizedCategoryChainComplex C N =
      inclusionNormalizedCategoryChainComplex C M ≫ categoryChainComplexMap α :=
  (AlgebraicTopology.inclusionOfMooreComplex A).naturality
    ((categorySimplicialObjectFunctor C A).map α)

variable (A) in
instance : (normalizedCategoryChainComplexFunctor C A).Additive where
  map_add {_ N} _ _ := by
    rw [← cancel_mono (inclusionNormalizedCategoryChainComplex C N), Preadditive.add_comp,
      inclusionNormalizedCategoryChainComplex_naturality,
      inclusionNormalizedCategoryChainComplex_naturality,
      inclusionNormalizedCategoryChainComplex_naturality]
    dsimp [categoryChainComplexMap]; rw [Functor.map_add, Preadditive.comp_add]

variable {C} in
@[reassoc]
lemma toNormalizedCategoryChainComplex_naturality {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplexMap α ≫ toNormalizedCategoryChainComplex C N =
      toNormalizedCategoryChainComplex C M ≫ normalizedCategoryChainComplexMap α :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality
    ((categorySimplicialObjectFunctor C A).map α)

variable {C} in
/-- Every degenerate simplex `(nerve C).σ i τ` projects to zero in normalized category chains. -/
@[reassoc (attr := simp)]
lemma categoryChainComplex.ι_σ_toNormalized_f (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (τ : ComposableArrows C n) :
    categoryChainComplex.ι M ((nerve C).σ i τ) ≫
        (toNormalizedCategoryChainComplex C M).f (n + 1) = 0 := by
  rw [← cancel_mono ((inclusionNormalizedCategoryChainComplex C M).f (n + 1)),
    Category.assoc, zero_comp, ← HomologicalComplex.comp_f, toNormalized_comp_inclusionNormalized]
  exact (congrArg (· ≫ _) (categorySimplicialObject.ι_σ M i τ).symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (categorySimplicialObject.ι M τ ≫ ·)
      (AlgebraicTopology.DoldKan.σ_comp_PInfty (categorySimplicialObject C M) i)).trans comp_zero))

variable {C} in
/-- The `1`-chain summand indexed by `mk₁ (𝟙 x)` vanishes in normalized category chains. -/
@[reassoc (attr := simp)]
lemma categoryChainComplex.ι₁_id_toNormalized_f (M : C ⥤ A) (x : C) :
    categoryChainComplex.ι₁ M (𝟙 x) ≫ (toNormalizedCategoryChainComplex C M).f 1 = 0 := by
  have hι : categoryChainComplex.ι₁ M (𝟙 x) =
      categoryChainComplex.ι M ((nerve C).σ (0 : Fin 1) (ComposableArrows.mk₀ x)) :=
    (categoryChainComplex.ι_congr M (nerve.σ₀_mk₀_eq x).symm rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  exact (congrArg (· ≫ _) hι).trans
    (categoryChainComplex.ι_σ_toNormalized_f M (0 : Fin 1) (ComposableArrows.mk₀ x))

/-- Dold–Kan chain homotopy equivalence between normalized and unnormalized category chains. -/
def normalizedCategoryChainComplexHomotopyEquiv (M : C ⥤ A) :
    HomotopyEquiv (normalizedCategoryChainComplex C M) (categoryChainComplex C M) :=
  AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

@[simp]
lemma normalizedCategoryChainComplexHomotopyEquiv_hom (M : C ⥤ A) :
    (normalizedCategoryChainComplexHomotopyEquiv C M).hom =
      inclusionNormalizedCategoryChainComplex C M := by
  dsimp [normalizedCategoryChainComplexHomotopyEquiv, inclusionNormalizedCategoryChainComplex]; rfl

@[simp]
lemma normalizedCategoryChainComplexHomotopyEquiv_inv (M : C ⥤ A) :
    (normalizedCategoryChainComplexHomotopyEquiv C M).inv =
      toNormalizedCategoryChainComplex C M := by
  dsimp [normalizedCategoryChainComplexHomotopyEquiv, toNormalizedCategoryChainComplex]; rfl

instance (M : C ⥤ A) : QuasiIso (inclusionNormalizedCategoryChainComplex C M) := by
  rw [← normalizedCategoryChainComplexHomotopyEquiv_hom]; infer_instance

instance (M : C ⥤ A) : QuasiIso (toNormalizedCategoryChainComplex C M) := by
  rw [← normalizedCategoryChainComplexHomotopyEquiv_inv]; infer_instance

/-- Homology of normalized category chains is naturally isomorphic to `categoryHomology C M n`. -/
def normalizedCategoryHomologyIso (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryChainComplex C M).homology n ≅ categoryHomology C M n :=
  (normalizedCategoryChainComplexHomotopyEquiv C M).toHomologyIso n

@[simp]
lemma normalizedCategoryHomologyIso_hom (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyIso C M n).hom =
      HomologicalComplex.homologyMap (inclusionNormalizedCategoryChainComplex C M) n := by
  dsimp [normalizedCategoryHomologyIso, HomotopyEquiv.toHomologyIso]
  rw [normalizedCategoryChainComplexHomotopyEquiv_hom]

@[simp]
lemma normalizedCategoryHomologyIso_inv (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyIso C M n).inv =
      HomologicalComplex.homologyMap (toNormalizedCategoryChainComplex C M) n := by
  dsimp [normalizedCategoryHomologyIso, HomotopyEquiv.toHomologyIso]
  rw [normalizedCategoryChainComplexHomotopyEquiv_inv]

variable {C} in
@[reassoc]
lemma normalizedCategoryHomologyIso_naturality {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap (normalizedCategoryChainComplexMap α) n ≫
        (normalizedCategoryHomologyIso C N n).hom =
      (normalizedCategoryHomologyIso C M n).hom ≫ categoryHomologyMap α n := by
  simp only [normalizedCategoryHomologyIso_hom, categoryHomologyMap,
    ← HomologicalComplex.homologyMap_comp, inclusionNormalizedCategoryChainComplex_naturality]

section Precomp

variable {C}

/-- Pushforward of `normalizedCategoryChainComplex` along a functor `F : C ⥤ D`. -/
@[expose]
def normalizedCategoryChainComplexPrecomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    normalizedCategoryChainComplex C (F ⋙ M) ⟶ normalizedCategoryChainComplex D M :=
  (AlgebraicTopology.normalizedMooreComplex A).map (categorySimplicialObjectPrecomp F M)

@[reassoc]
lemma inclusionNormalizedCategoryChainComplex_precomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    normalizedCategoryChainComplexPrecomp F M ≫ inclusionNormalizedCategoryChainComplex D M =
      inclusionNormalizedCategoryChainComplex C (F ⋙ M) ≫ categoryChainComplexPrecomp F M :=
  (AlgebraicTopology.inclusionOfMooreComplex A).naturality (categorySimplicialObjectPrecomp F M)

@[reassoc]
lemma normalizedCategoryHomologyIso_precomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap (normalizedCategoryChainComplexPrecomp F M) n ≫
        (normalizedCategoryHomologyIso D M n).hom =
      (normalizedCategoryHomologyIso C (F ⋙ M) n).hom ≫ categoryHomologyPrecomp F M n := by
  simp only [normalizedCategoryHomologyIso_hom, categoryHomologyPrecomp,
    ← HomologicalComplex.homologyMap_comp, inclusionNormalizedCategoryChainComplex_precomp]

end Precomp

end Normalized

end TauCeti

/-! ### Exactness on short exact sequences and the homology long exact sequence -/

section HomologySequence

variable (C : Type u₁) [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [Abelian A] [HasCoproducts.{max u₁ v₁} A]

/-- Under `AB4OfSize.{max u₁ v₁}`, `categoryChainComplexFunctor C A` preserves short exactness. -/
lemma CategoryTheory.ShortComplex.ShortExact.map_categoryChainComplex
    [AB4OfSize.{max u₁ v₁} A] {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    (S.map (TauCeti.categoryChainComplexFunctor C A)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  let ev₀ : Discrete (ComposableArrows C n) ⥤ C := Discrete.functor fun σ ↦ σ.obj 0
  let W : (C ⥤ A) ⥤ (Discrete (ComposableArrows C n) ⥤ A) :=
    (Functor.whiskeringLeft (Discrete (ComposableArrows C n)) C A).obj ev₀
  let cc (M : C ⥤ A) : ColimitCocone (W.obj M) :=
    { cocone := { pt := (TauCeti.categoryChainComplex C M).X n
                  ι := Discrete.natTrans fun ⟨σ⟩ ↦ TauCeti.categoryChainComplex.ι M σ }
      isColimit :=
        { desc s := (TauCeti.categoryChainComplex.isColimitXCofan M n).desc
            (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩)
          fac s := fun ⟨σ⟩ ↦ (TauCeti.categoryChainComplex.isColimitXCofan M n).fac
            (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩) ⟨σ⟩
          uniq s m hm := (TauCeti.categoryChainComplex.isColimitXCofan M n).uniq
            (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩) m fun ⟨σ⟩ ↦ hm ⟨σ⟩ } }
  have hfg {M N : C ⥤ A} (α : M ⟶ N) :
      (colimit.isoColimitCocone (cc M)).hom ≫ (TauCeti.categoryChainComplexMap α).f n =
        colimMap (W.map α) ≫ (colimit.isoColimitCocone (cc N)).hom :=
    colimit.hom_ext fun ⟨σ⟩ ↦ by
      rw [colimit.isoColimitCocone_ι_hom_assoc, ι_colimMap_assoc, colimit.isoColimitCocone_ι_hom]
      exact TauCeti.categoryChainComplex.ι_map_f α σ
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (colimit.isoColimitCocone (cc S.X₁)) (colimit.isoColimitCocone (cc S.X₂))
      (colimit.isoColimitCocone (cc S.X₃)) (hfg S.f) (hfg S.g))
    ((hS.map_of_exact W).map_of_exact colim)

/-- Specialization of `ShortExact.map_categoryChainComplex` to `ModuleCat.{max u₁ v₁ w} R`. -/
lemma CategoryTheory.ShortComplex.ShortExact.map_categoryChainComplex_moduleCat
    {R : Type*} [Ring R] {S : ShortComplex (C ⥤ ModuleCat.{max u₁ v₁ w} R)} (hS : S.ShortExact) :
    (S.map (TauCeti.categoryChainComplexFunctor C (ModuleCat.{max u₁ v₁ w} R))).ShortExact := by
  have : AB4 (ModuleCat.{max u₁ v₁ w} R) := ⟨fun α ↦ HasExactColimitsOfShape.domain_of_functor
    (Discrete α) (forget₂ (ModuleCat.{max u₁ v₁ w} R) AddCommGrpCat.{max u₁ v₁ w})⟩
  have := AB4OfSize_shrink.{max u₁ v₁, w} (ModuleCat.{max u₁ v₁ w} R)
  exact hS.map_categoryChainComplex C

namespace TauCeti.categoryHomology

variable [AB4OfSize.{max u₁ v₁} A]

/-- Connecting homomorphism `Hᵢ(C, S.X₃) ⟶ Hⱼ(C, S.X₁)` (`j + 1 = i`) for short exact `S`. -/
def δ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ) (hij : j + 1 = i := by lia) :
    categoryHomology C S.X₃ i ⟶ categoryHomology C S.X₁ j :=
  (hS.map_categoryChainComplex C).δ i j (ComplexShape.down_mk i j hij)

@[reassoc (attr := simp)]
lemma δ_comp {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) :
    δ C hS i j hij ≫ categoryHomologyMap S.f j = 0 :=
  (hS.map_categoryChainComplex C).δ_comp i j (ComplexShape.down_mk i j hij)

@[reassoc (attr := simp)]
lemma comp_δ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) :
    categoryHomologyMap S.g i ≫ δ C hS i j hij = 0 :=
  (hS.map_categoryChainComplex C).comp_δ i j (ComplexShape.down_mk i j hij)

/-- Exactness of `Hᵢ(C, S.X₃) ⟶ Hⱼ(C, S.X₁) ⟶ Hⱼ(C, S.X₂)` in the category homology sequence. -/
lemma homology_exact₁ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) :
    (ShortComplex.mk _ _ (δ_comp C hS i j hij)).Exact :=
  (hS.map_categoryChainComplex C).homology_exact₁ i j (ComplexShape.down_mk i j hij)

/-- Exactness of `Hᵢ(C, S.X₁) ⟶ Hᵢ(C, S.X₂) ⟶ Hᵢ(C, S.X₃)` in the category homology sequence. -/
lemma homology_exact₂ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk (categoryHomologyMap S.f i) (categoryHomologyMap S.g i)
      (by rw [← categoryHomologyMap_comp, S.zero, categoryHomologyMap_zero])).Exact :=
  (hS.map_categoryChainComplex C).homology_exact₂ i

/-- Exactness of `Hᵢ(C, S.X₂) ⟶ Hᵢ(C, S.X₃) ⟶ Hⱼ(C, S.X₁)` in the category homology sequence. -/
lemma homology_exact₃ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) :
    (ShortComplex.mk _ _ (comp_δ C hS i j hij)).Exact :=
  (hS.map_categoryChainComplex C).homology_exact₃ i j (ComplexShape.down_mk i j hij)

/-- Naturality of `categoryHomology.δ` for morphisms of short exact sequences in `C ⥤ A`. -/
@[reassoc]
lemma δ_naturality {S₁ S₂ : ShortComplex (C ⥤ A)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (i j : ℕ) (hij : j + 1 = i := by lia) :
    δ C hS₁ i j hij ≫ categoryHomologyMap φ.τ₁ j =
      categoryHomologyMap φ.τ₃ i ≫ δ C hS₂ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((categoryChainComplexFunctor C A).mapShortComplex.map φ)
    (hS₁.map_categoryChainComplex C) (hS₂.map_categoryChainComplex C)
    i j (ComplexShape.down_mk i j hij)

/-- Compatibility of `categoryHomology.δ` with pushforward along `F : D ⥤ C`. -/
@[reassoc]
lemma δ_precomp {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    [AB4OfSize.{max u₂ v₂} A] (F : D ⥤ C) {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact)
    (i j : ℕ) (hij : j + 1 = i := by lia) :
    let hSF : (S.map ((Functor.whiskeringLeft D C A).obj F)).ShortExact :=
      hS.map_of_exact ((Functor.whiskeringLeft D C A).obj F)
    δ D hSF i j hij ≫ categoryHomologyPrecomp F S.X₁ j =
      categoryHomologyPrecomp F S.X₃ i ≫ δ C hS i j hij := by
  intro hSF
  exact HomologicalComplex.HomologySequence.δ_naturality
    ({ τ₁ := categoryChainComplexPrecomp F S.X₁, τ₂ := categoryChainComplexPrecomp F S.X₂
       τ₃ := categoryChainComplexPrecomp F S.X₃
       comm₁₂ := (categoryChainComplexPrecomp_naturality F S.f).symm
       comm₂₃ := (categoryChainComplexPrecomp_naturality F S.g).symm } :
      (S.map ((Functor.whiskeringLeft D C A).obj F)).map (categoryChainComplexFunctor D A) ⟶
        S.map (categoryChainComplexFunctor C A))
    (hSF.map_categoryChainComplex D) (hS.map_categoryChainComplex C)
    i j (ComplexShape.down_mk i j hij)

lemma mono_δ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) (hi : IsZero (categoryHomology C S.X₂ i)) :
    Mono (δ C hS i j hij) :=
  (hS.map_categoryChainComplex C).mono_δ i j (ComplexShape.down_mk i j hij) hi

lemma epi_δ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) (hj : IsZero (categoryHomology C S.X₂ j)) :
    Epi (δ C hS i j hij) :=
  (hS.map_categoryChainComplex C).epi_δ i j (ComplexShape.down_mk i j hij) hj

lemma isIso_δ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) (hi : IsZero (categoryHomology C S.X₂ i))
    (hj : IsZero (categoryHomology C S.X₂ j)) :
    IsIso (δ C hS i j hij) :=
  (hS.map_categoryChainComplex C).isIso_δ i j (ComplexShape.down_mk i j hij) hi hj

/-- When `Hᵢ(C, S.X₂)` and `Hⱼ(C, S.X₂)` vanish (`j + 1 = i`), `δ` gives an isomorphism. -/
def δIso {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (i j : ℕ)
    (hij : j + 1 = i := by lia) (hi : IsZero (categoryHomology C S.X₂ i))
    (hj : IsZero (categoryHomology C S.X₂ j)) :
    categoryHomology C S.X₃ i ≅ categoryHomology C S.X₁ j :=
  (hS.map_categoryChainComplex C).δIso i j (ComplexShape.down_mk i j hij) hi hj

end TauCeti.categoryHomology

end HomologySequence
