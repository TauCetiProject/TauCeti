/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The K-flat left derivability structure from functorial flat covers

When an abelian category `C` carries a functor `E : C ⥤ C` and a natural transformation
`p : E ⟶ 𝟭 C`, the cell-attachment construction `CochainComplex.kFlatResolution E.obj p.app` is
functorial in the complex: each morphism `g : K ⟶ L` induces morphisms on the initial
zero-differential cycle covers, on the pullbacks `CochainComplex.kFlatResolution.boundaryPairs`,
and on all iterated mapping cones and their sequential colimit. This defines the resolution functor
`CochainComplex.kFlatResolutionFunctor E p` together with the natural augmentation
`CochainComplex.kFlatResolutionNatTrans E p : kFlatResolutionFunctor E p ⟶ 𝟭 (CochainComplex C ℤ)`
whose component at `K` is `CochainComplex.kFlatResolution.π E.obj p.app K`.

Suppose `C` is also monoidal preadditive, countable coproducts and sequential colimits are exact and
commute with tensoring on the right, every `p.app X` is an epimorphism, and every `E.obj X` is flat.
Then `kFlatResolutionFunctor E p` lands in the full subcategory `CochainComplex.KFlat C` of K-flat
cochain complexes, and every component of `kFlatResolutionNatTrans E p` is a quasi-isomorphism.
Consequently, the inclusion localizer morphism `CochainComplex.KFlat.localizerMorphism C` is a
localized equivalence, admits left resolutions of arrows, has connected left-resolution categories,
and forms a left derivability structure.

## Main definitions

* `CochainComplex.kFlatResolutionFunctor`: the functorial K-flat resolution associated to a
  functor `E : C ⥤ C` and a natural transformation `p : E ⟶ 𝟭 C`.
* `CochainComplex.kFlatResolutionNatTrans`: the natural augmentation
  `kFlatResolutionFunctor E p ⟶ 𝟭 (CochainComplex C ℤ)`.
* `CochainComplex.kFlat`, `CochainComplex.KFlat`: the object property and full subcategory of
  K-flat cochain complexes in `C`.
* `CochainComplex.KFlat.quasiIso`, `CochainComplex.KFlat.localizerMorphism`: quasi-isomorphisms of
  K-flat complexes and the induced localizer morphism to `CochainComplex C ℤ`.

## Main results

* `CochainComplex.KFlat.isLocalizedEquivalence_localizerMorphism`,
  `CochainComplex.KFlat.hasLeftResolutions_arrow_localizerMorphism`,
  `CochainComplex.KFlat.isConnected_leftResolution_localizerMorphism`,
  `CochainComplex.KFlat.isLeftDerivabilityStructure_localizerMorphism`: under a functorial flat
  epimorphic cover, `CochainComplex.KFlat.localizerMorphism C` is a left derivability structure.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008),
  1286–1318.
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

section FunctorialResolution

variable {C : Type*} [Category* C] [Abelian C] (E : C ⥤ C) (p : E ⟶ 𝟭 C)

namespace kFlatResolution

open HomComplex

@[simps]
private def gradedMap {A B : ℤ → C} (α : ∀ n, A n ⟶ B n) :
    graded (.up ℤ) A ⟶ graded (.up ℤ) B where
  f := α
  comm' _ _ _ := by simp

private lemma gradedMap_fromGraded {A B : ℤ → C} {K L : CochainComplex C ℤ}
    (α : ∀ n, A n ⟶ B n) (e₁ : ∀ n, A n ⟶ K.cycles n) (e₂ : ∀ n, B n ⟶ L.cycles n) (g : K ⟶ L)
    (h : ∀ n, α n ≫ e₂ n = e₁ n ≫ cyclesMap g n) :
    gradedMap α ≫ L.fromGraded e₂ = K.fromGraded e₁ ≫ g := by
  ext n
  simp only [comp_f, gradedMap_f, reassoc_of% (h n), cyclesMap_i, Category.assoc]

private def boundaryPairsMap {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (u : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (hu : u ≫ f₂ = f₁ ≫ g) (n : ℤ) :
    boundaryPairs f₁ n ⟶ boundaryPairs f₂ n :=
  pullback.map (cyclesMap f₁ n) (K₁.toCycles (n - 1) n)
    (cyclesMap f₂ n) (K₂.toCycles (n - 1) n)
    (cyclesMap u n) (g.f (n - 1)) (cyclesMap g n)
    (by rw [← cyclesMap_comp, ← cyclesMap_comp, hu])
    (by simp [← cancel_mono (K₂.iCycles n)])

private lemma boundaryPairsMap_id {P K : CochainComplex C ℤ} (f : P ⟶ K) (n : ℤ) :
    boundaryPairsMap f f (𝟙 P) (𝟙 K) (by rw [Category.id_comp, Category.comp_id]) n = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [boundaryPairsMap]

private lemma boundaryPairsMap_comp {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (f₃ : P₃ ⟶ K₃)
    (u₁₂ : P₁ ⟶ P₂) (u₂₃ : P₂ ⟶ P₃) (g₁₂ : K₁ ⟶ K₂) (g₂₃ : K₂ ⟶ K₃)
    (hu₁₂ : u₁₂ ≫ f₂ = f₁ ≫ g₁₂) (hu₂₃ : u₂₃ ≫ f₃ = f₂ ≫ g₂₃) (n : ℤ) :
    boundaryPairsMap f₁ f₃ (u₁₂ ≫ u₂₃) (g₁₂ ≫ g₂₃)
        (by rw [Category.assoc, hu₂₃, ← Category.assoc, hu₁₂, Category.assoc]) n =
      boundaryPairsMap f₁ f₂ u₁₂ g₁₂ hu₁₂ n ≫ boundaryPairsMap f₂ f₃ u₂₃ g₂₃ hu₂₃ n := by
  apply pullback.hom_ext <;> simp [boundaryPairsMap, cyclesMap_comp]

private def stepCellMap {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (u : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (hu : u ≫ f₂ = f₁ ≫ g) :
    graded (.up ℤ) (fun n ↦ E.obj (boundaryPairs f₁ n)) ⟶
      graded (.up ℤ) (fun n ↦ E.obj (boundaryPairs f₂ n)) :=
  gradedMap fun n ↦ E.map (boundaryPairsMap f₁ f₂ u g hu n)

private lemma attachingMap_stepCellMap {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (u : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (hu : u ≫ f₂ = f₁ ≫ g) :
    attachingMap f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ u =
      stepCellMap E f₁ f₂ u g hu ≫ attachingMap f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) := by
  symm
  refine gradedMap_fromGraded _ _ _ u fun n ↦ ?_
  have hnat := p.naturality (boundaryPairsMap f₁ f₂ u g hu n)
  dsimp at hnat
  rw [← Category.assoc, hnat, Category.assoc, boundaryPairsMap, pullback.lift_fst, Category.assoc]

private def stepMap {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (u : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (hu : u ≫ f₂ = f₁ ≫ g) :
    mappingCone (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ⟶
      mappingCone (attachingMap f₂ fun n ↦ p.app (boundaryPairs f₂ n)) :=
  mappingCone.map _ _ (stepCellMap E f₁ f₂ u g hu) u (attachingMap_stepCellMap E p f₁ f₂ u g hu)

private lemma inr_stepMap {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (u : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (hu : u ≫ f₂ = f₁ ≫ g) :
    mappingCone.inr (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ≫
      stepMap E p f₁ f₂ u g hu =
      u ≫ mappingCone.inr (attachingMap f₂ fun n ↦ p.app (boundaryPairs f₂ n)) :=
  (mappingCone.triangleMap _ _ _ _ (attachingMap_stepCellMap E p f₁ f₂ u g hu)).comm₂

private lemma stepMap_attachDesc {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (u : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (hu : u ≫ f₂ = f₁ ≫ g) :
    stepMap E p f₁ f₂ u g hu ≫ attachDesc f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) =
      attachDesc f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ g := by
  ext j
  rw [mappingCone.ext_from_iff _ (j + 1) j rfl]
  refine ⟨?_, ?_⟩
  · simp only [stepMap, mappingCone.map, attachDesc, comp_f, mappingCone.inl_v_desc_f_assoc,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc, mappingCone.inl_v_desc_f,
      boundaryPrimitive, Cochain.mk_v]
    dsimp [stepCellMap, gradedMap]
    have hnat := p.naturality (boundaryPairsMap f₁ f₂ u g hu (j + 1))
    dsimp at hnat
    rw [reassoc_of% hnat, boundaryPairsMap, pullback.lift_snd_assoc, Category.assoc,
      XIsoOfEq_hom_naturality]
  · rw [← comp_f, reassoc_of% inr_stepMap, inr_attachDesc, hu, ← comp_f, inr_attachDesc_assoc]

private lemma stepMap_id {P K : CochainComplex C ℤ} (f : P ⟶ K) (u : P ⟶ P)
    (hu : u ≫ f = f ≫ 𝟙 K) (hu_id : u = 𝟙 P) :
    stepMap E p f f u (𝟙 K) hu = 𝟙 _ := by
  subst hu_id
  have hcell : stepCellMap E f f (𝟙 P) (𝟙 K) hu = 𝟙 _ := by
    ext n
    simp [stepCellMap, boundaryPairsMap_id]
  simpa only [stepMap, hcell] using
    mappingCone.map_id (attachingMap f fun n ↦ p.app (boundaryPairs f n))

private lemma stepMap_comp {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
    (f₁ : P₁ ⟶ K₁) (f₂ : P₂ ⟶ K₂) (f₃ : P₃ ⟶ K₃)
    (u₁₂ : P₁ ⟶ P₂) (u₂₃ : P₂ ⟶ P₃) (u₁₃ : P₁ ⟶ P₃)
    (g₁₂ : K₁ ⟶ K₂) (g₂₃ : K₂ ⟶ K₃)
    (hu₁₂ : u₁₂ ≫ f₂ = f₁ ≫ g₁₂) (hu₂₃ : u₂₃ ≫ f₃ = f₂ ≫ g₂₃)
    (hu₁₃ : u₁₃ ≫ f₃ = f₁ ≫ (g₁₂ ≫ g₂₃)) (hu : u₁₃ = u₁₂ ≫ u₂₃) :
    stepMap E p f₁ f₃ u₁₃ (g₁₂ ≫ g₂₃) hu₁₃ =
      stepMap E p f₁ f₂ u₁₂ g₁₂ hu₁₂ ≫ stepMap E p f₂ f₃ u₂₃ g₂₃ hu₂₃ := by
  subst hu
  have hcell : stepCellMap E f₁ f₃ (u₁₂ ≫ u₂₃) (g₁₂ ≫ g₂₃) hu₁₃ =
      stepCellMap E f₁ f₂ u₁₂ g₁₂ hu₁₂ ≫ stepCellMap E f₂ f₃ u₂₃ g₂₃ hu₂₃ := by
    ext n
    simp [stepCellMap, boundaryPairsMap_comp f₁ f₂ f₃ u₁₂ u₂₃ g₁₂ g₂₃ hu₁₂ hu₂₃]
  simpa only [stepMap, hcell] using mappingCone.map_comp _ _ _ _ _
    (attachingMap_stepCellMap E p f₁ f₂ u₁₂ g₁₂ hu₁₂) _ _
    (attachingMap_stepCellMap E p f₂ f₃ u₂₃ g₂₃ hu₂₃)

private def stageMap {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ∀ k : ℕ, { u : (stage E.obj p.app K k).1 ⟶ (stage E.obj p.app L k).1 //
      u ≫ (stage E.obj p.app L k).2 = (stage E.obj p.app K k).2 ≫ g }
  | 0 => ⟨gradedMap fun n ↦ E.map (cyclesMap g n),
      gradedMap_fromGraded _ _ _ g fun n ↦ p.naturality (cyclesMap g n)⟩
  | k + 1 => ⟨stepMap E p (stage E.obj p.app K k).2 (stage E.obj p.app L k).2
      (stageMap g k).1 g (stageMap g k).2,
      stepMap_attachDesc E p _ _ _ g (stageMap g k).2⟩

private lemma stageMap_id (K : CochainComplex C ℤ) :
    ∀ k : ℕ, (stageMap E p (𝟙 K) k).1 = 𝟙 _
  | 0 => by
    ext n
    simp [stageMap, stage]
  | k + 1 => stepMap_id E p _ _ (stageMap E p (𝟙 K) k).2 (stageMap_id K k)

private lemma stageMap_comp {K L M : CochainComplex C ℤ} (g : K ⟶ L) (h : L ⟶ M) :
    ∀ k : ℕ, (stageMap E p (g ≫ h) k).1 = (stageMap E p g k).1 ≫ (stageMap E p h k).1
  | 0 => by
    ext n
    simp [stageMap, stage, cyclesMap_comp]
  | k + 1 => stepMap_comp E p _ _ _ _ _ _ g h
      (stageMap E p g k).2 (stageMap E p h k).2 (stageMap E p (g ≫ h) k).2
      (stageMap_comp g h k)

private def sequenceMap {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    sequence E.obj p.app K ⟶ sequence E.obj p.app L :=
  NatTrans.ofSequence (fun k ↦ (stageMap E p g k).1) fun k ↦ by
    rw [sequence_map_succ, sequence_map_succ]
    exact inr_stepMap E p _ _ _ g (stageMap E p g k).2

private lemma sequenceMap_id (K : CochainComplex C ℤ) :
    sequenceMap E p (𝟙 K) = 𝟙 _ :=
  NatTrans.ext (funext fun k ↦ stageMap_id E p K k)

private lemma sequenceMap_comp {K L M : CochainComplex C ℤ} (g : K ⟶ L) (h : L ⟶ M) :
    sequenceMap E p (g ≫ h) = sequenceMap E p g ≫ sequenceMap E p h :=
  NatTrans.ext (funext fun k ↦ stageMap_comp E p g h k)

private lemma sequenceMap_toComplex_app {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    (sequenceMap E p g).app k ≫ (toComplex E.obj p.app L).app k =
      (toComplex E.obj p.app K).app k ≫ g :=
  (stageMap E p g k).2

/-- The morphism on K-flat resolutions induced by a morphism of complexes `g : K ⟶ L` when the
covering data `(E, p)` is functorial. -/
def map [HasColimitsOfShape ℕ C] {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    kFlatResolution E.obj p.app K ⟶ kFlatResolution E.obj p.app L :=
  colimMap (sequenceMap E p g)

@[simp]
lemma map_id [HasColimitsOfShape ℕ C] (K : CochainComplex C ℤ) :
    map E p (𝟙 K) = 𝟙 (kFlatResolution E.obj p.app K) :=
  colimit.hom_ext fun k ↦ by simp [map, sequenceMap_id]

@[reassoc, simp]
lemma map_comp [HasColimitsOfShape ℕ C] {K L M : CochainComplex C ℤ} (g : K ⟶ L) (h : L ⟶ M) :
    map E p (g ≫ h) = map E p g ≫ map E p h :=
  colimit.hom_ext fun k ↦ by simp [map, sequenceMap_comp]

@[reassoc (attr := simp)]
lemma map_π [HasColimitsOfShape ℕ C] {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    map E p g ≫ π E.obj p.app L = π E.obj p.app K ≫ g :=
  colimit.hom_ext fun k ↦ by simp [map, sequenceMap_toComplex_app]

end kFlatResolution

variable [HasColimitsOfShape ℕ C]

/-- The functorial cell-attachment resolution associated to a functor `E : C ⥤ C` and a natural
transformation `p : E ⟶ 𝟭 C`. Its value on a complex `K` is
`CochainComplex.kFlatResolution E.obj p.app K`. -/
@[expose]
def kFlatResolutionFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := kFlatResolution E.obj p.app K
  map g := kFlatResolution.map E p g

@[simp]
lemma kFlatResolutionFunctor_obj (K : CochainComplex C ℤ) :
    (kFlatResolutionFunctor E p).obj K = kFlatResolution E.obj p.app K := (rfl)

@[simp]
lemma kFlatResolutionFunctor_map {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (kFlatResolutionFunctor E p).map g = kFlatResolution.map E p g := (rfl)

/-- The natural augmentation from `kFlatResolutionFunctor E p` to the identity functor, whose
component at `K` is `kFlatResolution.π E.obj p.app K`. -/
def kFlatResolutionNatTrans : kFlatResolutionFunctor E p ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := kFlatResolution.π E.obj p.app K
  naturality _ _ g := kFlatResolution.map_π E p g

@[simp]
lemma kFlatResolutionNatTrans_app (K : CochainComplex C ℤ) :
    (kFlatResolutionNatTrans E p).app K = kFlatResolution.π E.obj p.app K := (rfl)

private lemma mem_quasiIso_kFlatResolutionNatTrans_app
    [HasExactColimitsOfShape ℕ C] [∀ X : C, Epi (p.app X)] (K : CochainComplex C ℤ) :
    HomologicalComplex.quasiIso C (.up ℤ) ((kFlatResolutionNatTrans E p).app K) :=
  (HomologicalComplex.mem_quasiIso_iff _).2 (kFlatResolution.quasiIso_π E.obj p.app K)

end FunctorialResolution

section KFlatSubcategory

variable (C : Type*) [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The object property on `CochainComplex C ℤ` selecting K-flat complexes. -/
protected def kFlat : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ K.IsKFlat

@[simp]
lemma kFlat_iff {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L] (K : CochainComplex C ℤ) :
    CochainComplex.kFlat C K ↔ K.IsKFlat := (Iff.rfl)

instance : (CochainComplex.kFlat C).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    have : IsKFlat _ := hK
    exact isKFlat_of_iso e

instance : (CochainComplex.kFlat C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    have : K.IsKFlat := hK
    exact inferInstanceAs (K⟦n⟧).IsKFlat⟩

/-- The full subcategory of `CochainComplex C ℤ` consisting of K-flat complexes. -/
abbrev KFlat := (CochainComplex.kFlat C).FullSubcategory

namespace KFlat

/-- Bundle a K-flat cochain complex as an object of `CochainComplex.KFlat C`. -/
def mk {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    (K : CochainComplex C ℤ) [hK : K.IsKFlat] : KFlat C :=
  ⟨K, hK⟩

@[simp]
lemma mk_obj {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    (K : CochainComplex C ℤ) [K.IsKFlat] :
    (mk K).obj = K := (rfl)

/-- The fully faithful inclusion of K-flat cochain complexes into all cochain complexes. -/
abbrev ι : KFlat C ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι (CochainComplex.kFlat C)

instance {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L] (K : KFlat C) : K.obj.IsKFlat :=
  K.property

/-- Quasi-isomorphisms in the full subcategory of K-flat cochain complexes. -/
def quasiIso : MorphismProperty (KFlat C) :=
  (HomologicalComplex.quasiIso C (.up ℤ)).inverseImage (ι C)

@[simp]
lemma quasiIso_iff {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [∀ K L : CochainComplex C ℤ, HasTensor K L]
    {K L : KFlat C} (f : K ⟶ L) :
    quasiIso C f ↔ QuasiIso f.hom := (Iff.rfl)

instance : (quasiIso C).ContainsIdentities := by
  dsimp [quasiIso]
  infer_instance

instance : (quasiIso C).IsMultiplicative := by
  dsimp [quasiIso]
  infer_instance

instance : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance

/-- The localizer morphism given by the inclusion `CochainComplex.KFlat C ⥤ CochainComplex C ℤ`
with respect to quasi-isomorphisms. -/
def localizerMorphism :
    LocalizerMorphism (quasiIso C) (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := ι C
  map _ _ _ h := h

@[simp]
lemma localizerMorphism_functor :
    (localizerMorphism C).functor = ι C := (rfl)

instance : (localizerMorphism C).IsInduced where
  inverseImage_eq := rfl

instance : (localizerMorphism C).functor.Full :=
  inferInstanceAs (ι C).Full

instance : (localizerMorphism C).functor.Faithful :=
  inferInstanceAs (ι C).Faithful

section DerivabilityStructure

variable {C}
variable (E : C ⥤ C) (p : E ⟶ 𝟭 C)
  [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
  [∀ X : C, Epi (p.app X)]
  [∀ X : C, PreservesFiniteLimits (tensorLeft (E.obj X))]
  [∀ X : C, PreservesFiniteColimits (tensorLeft (E.obj X))]

private def liftedResolutionFunctor : CochainComplex C ℤ ⥤ KFlat C :=
  (CochainComplex.kFlat C).lift (kFlatResolutionFunctor E p) fun _ ↦
    inferInstanceAs (kFlatResolution E.obj p.app _).IsKFlat

include E p

/-- Under a functorial flat epimorphic cover `(E, p)`, the K-flat localizer morphism admits left
resolutions in the category of arrows. -/
theorem hasLeftResolutions_arrow_localizerMorphism :
    (localizerMorphism C).arrow.HasLeftResolutions :=
  (localizerMorphism C).hasLeftResolutions_arrow_of_functorial_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (mem_quasiIso_kFlatResolutionNatTrans_app E p)

/-- Under a functorial flat epimorphic cover `(E, p)`, the inclusion of K-flat complexes induces an
equivalence on localized categories with respect to quasi-isomorphisms. -/
theorem isLocalizedEquivalence_localizerMorphism :
    (localizerMorphism C).IsLocalizedEquivalence :=
  (localizerMorphism C).isLocalizedEquivalence_of_functorial_left_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (mem_quasiIso_kFlatResolutionNatTrans_app E p) rfl

/-- Under a functorial flat epimorphic cover `(E, p)`, the category of K-flat left resolutions of
every cochain complex `K` is connected. -/
theorem isConnected_leftResolution_localizerMorphism (K : CochainComplex C ℤ) :
    IsConnected ((localizerMorphism C).LeftResolution K) :=
  (localizerMorphism C).isConnected_leftResolution_of_functorial_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (mem_quasiIso_kFlatResolutionNatTrans_app E p) K

/-- **The K-flat left derivability structure.** Under a functorial flat epimorphic cover `(E, p)`,
`CochainComplex.KFlat.localizerMorphism C` is a left derivability structure. -/
theorem isLeftDerivabilityStructure_localizerMorphism :
    (localizerMorphism C).IsLeftDerivabilityStructure :=
  (localizerMorphism C).isLeftDerivabilityStructure_of_functorial_resolutions
    (ρ := liftedResolutionFunctor E p) (kFlatResolutionNatTrans E p)
    (mem_quasiIso_kFlatResolutionNatTrans_app E p) rfl

end DerivabilityStructure

end KFlat

end KFlatSubcategory

end CochainComplex
