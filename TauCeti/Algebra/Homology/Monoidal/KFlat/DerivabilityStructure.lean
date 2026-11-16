/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import TauCeti.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Functorial K-flat resolutions and the K-flat left derivability structure

When the covers `p.app X : E.obj X ⟶ X` used in the cell-attachment construction
`CochainComplex.kFlatResolution` come from an endofunctor `E : C ⥤ C` and a natural
transformation `p : E ⟶ 𝟭 C`, the resolution itself is functorial in the cochain complex `K`,
and the augmentation `CochainComplex.kFlatResolution.π` is natural in `K`.

In an abelian monoidal category `C` where countable coproducts and sequential colimits are exact
and commute with tensoring by each object, if every `p.app X` is an epimorphism and every
`E.obj X` is flat, then this functorial K-flat resolution lifts to the full subcategory of K-flat
complexes. By the dual of Mathlib's functorial-resolutions constructor
(`CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`), the
inclusion of K-flat complexes into `CochainComplex C ℤ` is a left derivability structure with
respect to quasi-isomorphisms.

## Main definitions

* `CochainComplex.kFlatResolution.functor`: the functorial K-flat resolution associated to a
  functorial cover `p : E ⟶ 𝟭 C`.
* `CochainComplex.kFlatResolution.πNatTrans`: the natural augmentation from
  `kFlatResolution.functor E p` to the identity functor.
* `CochainComplex.isKFlatProperty`: the object property of K-flat cochain complexes.
* `CochainComplex.kFlatLocalizerMorphism`: the localizer morphism given by the inclusion of the
  full subcategory of K-flat cochain complexes with induced quasi-isomorphisms.

## Main results

* `CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism`: a functorial flat
  epimorphic cover makes `kFlatLocalizerMorphism C` a left derivability structure.
* `CochainComplex.hasLeftResolutions_arrow_kFlatLocalizerMorphism`: morphisms of cochain complexes
  admit left resolutions by morphisms of K-flat complexes.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

section Functorial

variable {C : Type*} [Category* C] [Abelian C]

namespace kFlatResolution

/-- A family of morphisms in each degree defines a chain map between complexes with zero
differentials. -/
private def gradedMap {E₁ E₂ : ℤ → C} (h : ∀ n, E₁ n ⟶ E₂ n) :
    graded (.up ℤ) E₁ ⟶ graded (.up ℤ) E₂ where
  f := h
  comm' _ _ _ := by simp

private lemma gradedMap_id (E : ℤ → C) :
    gradedMap (fun n ↦ 𝟙 (E n)) = 𝟙 (graded (.up ℤ) E) := by
  ext n
  rfl

private lemma gradedMap_comp {E₁ E₂ E₃ : ℤ → C}
    (h₁ : ∀ n, E₁ n ⟶ E₂ n) (h₂ : ∀ n, E₂ n ⟶ E₃ n) :
    gradedMap (fun n ↦ h₁ n ≫ h₂ n) = gradedMap h₁ ≫ gradedMap h₂ := by
  ext n
  rfl

/-- Functoriality of `boundaryPairs` on a commutative square of chain maps. -/
private def boundaryPairsMap {P₁ K₁ P₂ K₂ : CochainComplex C ℤ}
    {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} (u : P₁ ⟶ P₂) (v : K₁ ⟶ K₂)
    (sq : u ≫ f₂ = f₁ ≫ v) (n : ℤ) :
    boundaryPairs f₁ n ⟶ boundaryPairs f₂ n :=
  pullback.map (cyclesMap f₁ n) (K₁.toCycles (n - 1) n)
    (cyclesMap f₂ n) (K₂.toCycles (n - 1) n)
    (cyclesMap u n) (v.f (n - 1)) (cyclesMap v n)
    (by rw [← cyclesMap_comp, ← cyclesMap_comp, sq])
    (by
      rw [← cancel_mono (K₂.iCycles n), Category.assoc, Category.assoc,
        K₂.toCycles_i, cyclesMap_i, HomologicalComplex.toCycles_i_assoc, v.comm])

private lemma boundaryPairsMap_id {P K : CochainComplex C ℤ} (f : P ⟶ K) (n : ℤ) :
    boundaryPairsMap (𝟙 P) (𝟙 K) (by simp) n = 𝟙 (boundaryPairs f n) := by
  apply pullback.hom_ext
  · simp [boundaryPairsMap]
  · simp [boundaryPairsMap]

private lemma boundaryPairsMap_comp {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
    {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} {f₃ : P₃ ⟶ K₃}
    (u₁ : P₁ ⟶ P₂) (v₁ : K₁ ⟶ K₂) (sq₁ : u₁ ≫ f₂ = f₁ ≫ v₁)
    (u₂ : P₂ ⟶ P₃) (v₂ : K₂ ⟶ K₃) (sq₂ : u₂ ≫ f₃ = f₂ ≫ v₂) (n : ℤ) :
    boundaryPairsMap (u₁ ≫ u₂) (v₁ ≫ v₂) (by rw [Category.assoc, sq₂, reassoc_of% sq₁]) n =
      boundaryPairsMap u₁ v₁ sq₁ n ≫ boundaryPairsMap u₂ v₂ sq₂ n := by
  apply pullback.hom_ext
  · simp [boundaryPairsMap, cyclesMap_comp]
  · simp [boundaryPairsMap]

private lemma attachingMap_comm (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P₁ K₁ P₂ K₂ : CochainComplex C ℤ} {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂}
    (u : P₁ ⟶ P₂) (v : K₁ ⟶ K₂) (sq : u ≫ f₂ = f₁ ≫ v) :
    attachingMap f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ u =
      gradedMap (fun n ↦ E.map (boundaryPairsMap u v sq n)) ≫
        attachingMap f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) := by
  ext n
  dsimp [attachingMap, fromGraded, gradedMap]
  simp only [Category.assoc, p.naturality_assoc, ← cyclesMap_i u n]
  simp [boundaryPairsMap]

/-- Functoriality of one cell-attachment step on a commutative square of chain maps. -/
private def attachMap (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P₁ K₁ P₂ K₂ : CochainComplex C ℤ} {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂}
    (u : P₁ ⟶ P₂) (v : K₁ ⟶ K₂) (sq : u ≫ f₂ = f₁ ≫ v) :
    mappingCone (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ⟶
      mappingCone (attachingMap f₂ fun n ↦ p.app (boundaryPairs f₂ n)) :=
  mappingCone.map _ _
    (gradedMap fun n ↦ E.map (boundaryPairsMap u v sq n)) u
    (attachingMap_comm E p u v sq)

private lemma attachMap_congr (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P₁ K₁ P₂ K₂ : CochainComplex C ℤ} {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂}
    {u u' : P₁ ⟶ P₂} (v : K₁ ⟶ K₂) (h : u = u')
    (sq : u ≫ f₂ = f₁ ≫ v) (sq' : u' ≫ f₂ = f₁ ≫ v) :
    attachMap E p u v sq = attachMap E p u' v sq' := by
  subst h
  rfl

@[reassoc]
private lemma inr_attachMap (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P₁ K₁ P₂ K₂ : CochainComplex C ℤ} {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂}
    (u : P₁ ⟶ P₂) (v : K₁ ⟶ K₂) (sq : u ≫ f₂ = f₁ ≫ v) :
    mappingCone.inr (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ≫
      attachMap E p u v sq =
    u ≫ mappingCone.inr (attachingMap f₂ fun n ↦ p.app (boundaryPairs f₂ n)) := by
  simp [attachMap, mappingCone.map]

private lemma attachMap_comp_attachDesc (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P₁ K₁ P₂ K₂ : CochainComplex C ℤ} {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂}
    (u : P₁ ⟶ P₂) (v : K₁ ⟶ K₂) (sq : u ≫ f₂ = f₁ ≫ v) :
    attachMap E p u v sq ≫ attachDesc f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) =
      attachDesc f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ v := by
  ext q
  rw [mappingCone.ext_from_iff _ (q + 1) q rfl]
  constructor
  · dsimp only [attachMap, attachDesc, mappingCone.map]
    rw [comp_f, comp_f, mappingCone.inl_v_desc_f_assoc, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v, Category.assoc,
      mappingCone.inl_v_desc_f]
    dsimp [boundaryPrimitive, gradedMap]
    rw [p.naturality_assoc]
    simp only [boundaryPairsMap, Functor.id_map, pullback.map, pullback.lift_snd_assoc]
    have hEq : ∀ {a b : ℤ} (hab : a = b),
        v.f a ≫ (K₂.XIsoOfEq hab).hom = (K₁.XIsoOfEq hab).hom ≫ v.f b := by
      rintro a _ rfl
      simp
    simp only [Category.assoc, hEq]
  · have h : mappingCone.inr (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ≫
        attachMap E p u v sq ≫ attachDesc f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) =
        mappingCone.inr (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ≫
        attachDesc f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ v := by
      rw [inr_attachMap_assoc, inr_attachDesc, ← Category.assoc, inr_attachDesc, sq]
    simpa only [comp_f] using congrArg (fun φ : P₁ ⟶ K₂ ↦ φ.f q) h

private lemma attachMap_id (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P K : CochainComplex C ℤ} (f : P ⟶ K) :
    attachMap E p (f₁ := f) (f₂ := f) (𝟙 P) (𝟙 K) (by simp) = 𝟙 _ := by
  have hcell :
      gradedMap (fun n ↦ E.map (boundaryPairsMap (f₁ := f) (f₂ := f) (𝟙 P) (𝟙 K) (by simp) n)) =
        𝟙 _ := by
    ext n
    simp [gradedMap, boundaryPairsMap_id]
  dsimp only [attachMap]
  convert mappingCone.map_id (attachingMap f fun n ↦ p.app (boundaryPairs f n))

private lemma attachMap_comp (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
    {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} {f₃ : P₃ ⟶ K₃}
    (u₁ : P₁ ⟶ P₂) (v₁ : K₁ ⟶ K₂) (sq₁ : u₁ ≫ f₂ = f₁ ≫ v₁)
    (u₂ : P₂ ⟶ P₃) (v₂ : K₂ ⟶ K₃) (sq₂ : u₂ ≫ f₃ = f₂ ≫ v₂) :
    attachMap E p (u₁ ≫ u₂) (v₁ ≫ v₂) (by rw [Category.assoc, sq₂, reassoc_of% sq₁]) =
      attachMap E p u₁ v₁ sq₁ ≫ attachMap E p u₂ v₂ sq₂ := by
  have hcell :
      gradedMap (fun n ↦ E.map (boundaryPairsMap (u₁ ≫ u₂) (v₁ ≫ v₂)
        (by rw [Category.assoc, sq₂, reassoc_of% sq₁]) n)) =
      gradedMap (fun n ↦ E.map (boundaryPairsMap u₁ v₁ sq₁ n)) ≫
        gradedMap (fun n ↦ E.map (boundaryPairsMap u₂ v₂ sq₂ n)) := by
    ext n
    dsimp [gradedMap]
    rw [boundaryPairsMap_comp u₁ v₁ sq₁ u₂ v₂ sq₂ n, E.map_comp]
  dsimp only [attachMap]
  rw [← mappingCone.map_comp]
  congr 1

/-- The morphisms between stages of `kFlatResolution` induced by a chain map `g : K ⟶ L`,
bundled with their compatibility with the morphisms to `K` and `L`. -/
private def stageMapData (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ∀ k, { φ : (stage E.obj p.app K k).1 ⟶ (stage E.obj p.app L k).1 //
      φ ≫ (stage E.obj p.app L k).2 = (stage E.obj p.app K k).2 ≫ g }
  | 0 =>
    ⟨gradedMap fun n ↦ E.map (cyclesMap g n), by
      ext n
      dsimp [stage, fromGraded, gradedMap]
      rw [p.naturality_assoc]
      dsimp
      rw [Category.assoc, cyclesMap_i]⟩
  | k + 1 =>
    ⟨attachMap E p (stageMapData E p g k).1 g (stageMapData E p g k).2,
      attachMap_comp_attachDesc E p (stageMapData E p g k).1 g (stageMapData E p g k).2⟩

private lemma stageMapData_id (E : C ⥤ C) (p : E ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    ∀ k, (stageMapData E p (𝟙 K) k).1 = 𝟙 _
  | 0 => by
    ext n
    simp [stageMapData, gradedMap, cyclesMap_id]
    rfl
  | k + 1 =>
    (attachMap_congr E p (𝟙 K) (stageMapData_id E p K k) _ (by simp)).trans
      (attachMap_id E p (stage E.obj p.app K k).2)

private lemma stageMapData_comp (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {K L M : CochainComplex C ℤ} (g₁ : K ⟶ L) (g₂ : L ⟶ M) :
    ∀ k, (stageMapData E p (g₁ ≫ g₂) k).1 =
      (stageMapData E p g₁ k).1 ≫ (stageMapData E p g₂ k).1
  | 0 => by
    ext n
    simp [stageMapData, gradedMap, cyclesMap_comp]
    rfl
  | k + 1 =>
    (attachMap_congr E p (g₁ ≫ g₂) (stageMapData_comp E p g₁ g₂ k) _ _).trans
      (attachMap_comp E p (stageMapData E p g₁ k).1 g₁ (stageMapData E p g₁ k).2
        (stageMapData E p g₂ k).1 g₂ (stageMapData E p g₂ k).2)

/-- The natural transformation between resolution sequences induced by a chain map `g : K ⟶ L`. -/
def sequenceMap (E : C ⥤ C) (p : E ⟶ 𝟭 C) {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    sequence E.obj p.app K ⟶ sequence E.obj p.app L :=
  NatTrans.ofSequence (fun k ↦ (stageMapData E p g k).1) fun k ↦ by
    rw [sequence_map_succ, sequence_map_succ]
    exact inr_attachMap E p (stageMapData E p g k).1 g (stageMapData E p g k).2

@[simp]
lemma sequenceMap_id (E : C ⥤ C) (p : E ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    sequenceMap E p (𝟙 K) = 𝟙 (sequence E.obj p.app K) := by
  apply NatTrans.ext
  funext k
  exact stageMapData_id E p K k

@[simp]
lemma sequenceMap_comp (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {K L M : CochainComplex C ℤ} (g₁ : K ⟶ L) (g₂ : L ⟶ M) :
    sequenceMap E p (g₁ ≫ g₂) = sequenceMap E p g₁ ≫ sequenceMap E p g₂ := by
  apply NatTrans.ext
  funext k
  exact stageMapData_comp E p g₁ g₂ k

@[reassoc]
lemma sequenceMap_app_toComplex (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    (sequenceMap E p g).app k ≫ (toComplex E.obj p.app L).app k =
      (toComplex E.obj p.app K).app k ≫ g :=
  (stageMapData E p g k).2

variable [HasColimitsOfShape ℕ C]

/-- The morphism of K-flat resolutions induced by a chain map `g : K ⟶ L`. -/
def map (E : C ⥤ C) (p : E ⟶ 𝟭 C) {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    kFlatResolution E.obj p.app K ⟶ kFlatResolution E.obj p.app L :=
  colimMap (sequenceMap E p g)

@[reassoc (attr := simp)]
lemma ι_map (E : C ⥤ C) (p : E ⟶ 𝟭 C) {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    colimit.ι (sequence E.obj p.app K) k ≫ map E p g =
      (sequenceMap E p g).app k ≫ colimit.ι (sequence E.obj p.app L) k :=
  colimit.ι_map (sequenceMap E p g) k

@[simp]
lemma map_id (E : C ⥤ C) (p : E ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    map E p (𝟙 K) = 𝟙 (kFlatResolution E.obj p.app K) := by
  apply colimit.hom_ext
  intro k
  simp [map, sequenceMap_id]

@[simp]
lemma map_comp (E : C ⥤ C) (p : E ⟶ 𝟭 C) {K L M : CochainComplex C ℤ} (g₁ : K ⟶ L) (g₂ : L ⟶ M) :
    map E p (g₁ ≫ g₂) = map E p g₁ ≫ map E p g₂ := by
  apply colimit.hom_ext
  intro k
  simp [map, sequenceMap_comp]

@[reassoc (attr := simp)]
lemma map_π (E : C ⥤ C) (p : E ⟶ 𝟭 C) {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    map E p g ≫ π E.obj p.app L = π E.obj p.app K ≫ g := by
  apply colimit.hom_ext
  intro k
  simp only [ι_map_assoc, ι_π, ι_π_assoc, sequenceMap_app_toComplex]

/-- The functorial K-flat resolution associated to a functorial cover `p : E ⟶ 𝟭 C`. Its value on
`K` is `kFlatResolution E.obj p.app K`. -/
@[expose] def functor (E : C ⥤ C) (p : E ⟶ 𝟭 C) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := kFlatResolution E.obj p.app K
  map g := map E p g
  map_id := map_id E p
  map_comp := map_comp E p

@[simp]
lemma functor_obj (E : C ⥤ C) (p : E ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    (functor E p).obj K = kFlatResolution E.obj p.app K := (rfl)

@[simp]
lemma functor_map (E : C ⥤ C) (p : E ⟶ 𝟭 C) {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (functor E p).map g = map E p g := (rfl)

/-- The natural augmentation `kFlatResolution.functor E p ⟶ 𝟭 (CochainComplex C ℤ)` whose
component at `K` is `kFlatResolution.π E.obj p.app K`. -/
def πNatTrans (E : C ⥤ C) (p : E ⟶ 𝟭 C) :
    functor E p ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := π E.obj p.app K
  naturality _ _ g := map_π E p g

@[simp]
lemma πNatTrans_app (E : C ⥤ C) (p : E ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    (πNatTrans E p).app K = π E.obj p.app K := (rfl)

end kFlatResolution

end Functorial

section DerivabilityStructure

variable (C : Type*) [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The object property of K-flat cochain complexes in `C`. -/
def isKFlatProperty : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ K.IsKFlat

/-- Membership in `isKFlatProperty` is equivalent to `CochainComplex.IsKFlat`. -/
@[simp]
lemma isKFlatProperty_iff {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [∀ K L : CochainComplex C ℤ, HasTensor K L]
    (K : CochainComplex C ℤ) :
    isKFlatProperty C K ↔ K.IsKFlat :=
  Iff.rfl

instance : (isKFlatProperty C).IsClosedUnderIsomorphisms where
  of_iso {K _} e hK := have : K.IsKFlat := hK; isKFlat_of_iso e

instance (K : (isKFlatProperty C).FullSubcategory) : K.obj.IsKFlat :=
  K.property

/-- The localizer morphism given by the inclusion of the full subcategory of K-flat cochain
complexes into `CochainComplex C ℤ`, equipped with the induced class of quasi-isomorphisms. -/
abbrev kFlatLocalizerMorphism :
    LocalizerMorphism ((quasiIso C (.up ℤ)).inverseImage (isKFlatProperty C).ι)
      (quasiIso C (.up ℤ)) where
  functor := (isKFlatProperty C).ι
  map _ _ _ h := h

instance : (kFlatLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

variable {C}

/-- The functorial K-flat resolution lifted to the full subcategory of K-flat complexes. -/
@[expose] def kFlatResolution.liftFunctor [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] :
    CochainComplex C ℤ ⥤ (isKFlatProperty C).FullSubcategory :=
  ObjectProperty.lift (isKFlatProperty C) (kFlatResolution.functor E p)
    fun K ↦ (isKFlatProperty_iff _).2 (isKFlat_kFlatResolution E.obj p.app K)

/-- The underlying complex of `kFlatResolution.liftFunctor E p` on `K` is
`kFlatResolution E.obj p.app K`. -/
@[simp]
lemma kFlatResolution.liftFunctor_obj_obj [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] (K : CochainComplex C ℤ) :
    ((kFlatResolution.liftFunctor E p).obj K).obj = kFlatResolution E.obj p.app K := (rfl)

/-- The underlying morphism of `kFlatResolution.liftFunctor E p` on `g` is
`kFlatResolution.map E p g`. -/
@[simp]
lemma kFlatResolution.liftFunctor_map_hom [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))]
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ((kFlatResolution.liftFunctor E p).map g).hom = kFlatResolution.map E p g := (rfl)

/-- Composing `kFlatResolution.liftFunctor` with the inclusion of K-flat complexes recovers
`kFlatResolution.functor`. -/
@[simp]
lemma kFlatResolution.liftFunctor_comp_ι [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    (E : C ⥤ C) (p : E ⟶ 𝟭 C)
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] :
    kFlatResolution.liftFunctor E p ⋙ (isKFlatProperty C).ι = kFlatResolution.functor E p := (rfl)

/-- Morphisms of cochain complexes admit left resolutions by morphisms of K-flat complexes
whenever `C` admits a functorial flat epimorphic cover and exact countable coproducts and
sequential colimits commuting with tensor products. -/
theorem hasLeftResolutions_arrow_kFlatLocalizerMorphism
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    (E : C ⥤ C) (p : E ⟶ 𝟭 C) [∀ X, Epi (p.app X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] :
    (kFlatLocalizerMorphism C).arrow.HasLeftResolutions :=
  (kFlatLocalizerMorphism C).hasLeftResolutions_arrow_of_functorial_resolutions
    (ρ := kFlatResolution.liftFunctor E p) (kFlatResolution.πNatTrans E p)
    fun K ↦ (mem_quasiIso_iff _).2 (kFlatResolution.quasiIso_π E.obj p.app K)

/-- **The K-flat left derivability structure.** In an abelian monoidal category with exact
countable coproducts and sequential colimits commuting with tensor products, a functorial flat
epimorphic cover `p : E ⟶ 𝟭 C` makes the inclusion of K-flat complexes a left derivability
structure for quasi-isomorphisms. -/
theorem isLeftDerivabilityStructure_kFlatLocalizerMorphism
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    (E : C ⥤ C) (p : E ⟶ 𝟭 C) [∀ X, Epi (p.app X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] :
    (kFlatLocalizerMorphism C).IsLeftDerivabilityStructure :=
  (kFlatLocalizerMorphism C).isLeftDerivabilityStructure_of_functorial_resolutions
    (ρ := kFlatResolution.liftFunctor E p) (kFlatResolution.πNatTrans E p)
    (fun K ↦ (mem_quasiIso_iff _).2 (kFlatResolution.quasiIso_π E.obj p.app K)) rfl

end DerivabilityStructure

end CochainComplex
