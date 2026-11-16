/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Functorial K-flat resolutions and the K-flat left derivability structure

When the covers `p X : E X ⟶ X` used to construct `CochainComplex.kFlatResolution` come from an
endofunctor `E : C ⥤ C` and a natural transformation `p : E ⟶ 𝟭 C`, the cell-attachment
resolution becomes functorial in the complex `K`: each stage is functorial in morphisms of
complexes, compatibly with the transition inclusions into mapping cones and the projections to `K`.
Taking the sequential colimit gives a functor `CochainComplex.kFlatResolutionFunctor E p` together
with a natural transformation `CochainComplex.kFlatResolutionFunctorπ E p` to the identity functor.

In an abelian monoidal category `C` where every `p.app X` is an epimorphism from a flat object
`E.obj X` and countable coproducts and sequential colimits are exact and commute with tensoring,
this yields a functorial K-flat left resolution. Dualizing Mathlib's functorial-resolution
criterion via `LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`
shows that the inclusion of K-flat complexes into `CochainComplex C ℤ` is a left derivability
structure (`CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism`).

## Main definitions and results

* `CochainComplex.kFlatResolutionFunctor`: the functorial K-flat resolution associated to a
  natural transformation `p : E ⟶ 𝟭 C`.
* `CochainComplex.kFlatResolutionFunctorπ`: the natural transformation from
  `kFlatResolutionFunctor E p` to the identity functor.
* `CochainComplex.isKFlatProperty`: the `ObjectProperty` of K-flat cochain complexes.
* `CochainComplex.kFlatLocalizerMorphism`: the localizer morphism given by the inclusion of the
  full subcategory of K-flat complexes with respect to quasi-isomorphisms.
* `CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism`: the K-flat localizer
  morphism is a left derivability structure whenever `C` admits functorial flat covers and exact
  tensor-commuting countable coproducts and sequential colimits.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

section Functorial

variable {C : Type*} [Category* C] [Abelian C]

namespace kFlatResolution

/-- A commutative square of complexes induces a morphism between the pullbacks of boundary pairs. -/
private def boundaryPairsMap {P₁ P₂ K₁ K₂ : CochainComplex C ℤ}
    {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} (φ : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (h : φ ≫ f₂ = f₁ ≫ g) (n : ℤ) :
    boundaryPairs f₁ n ⟶ boundaryPairs f₂ n :=
  pullback.map _ _ _ _ (cyclesMap φ n) (g.f (n - 1)) (cyclesMap g n)
    (by rw [← cyclesMap_comp, ← cyclesMap_comp, h])
    (by
      rw [← cancel_mono (K₂.iCycles n), Category.assoc, Category.assoc, K₂.toCycles_i,
        cyclesMap_i, K₁.toCycles_i_assoc, g.comm])

@[reassoc (attr := simp)]
private lemma boundaryPairsMap_fst {P₁ P₂ K₁ K₂ : CochainComplex C ℤ}
    {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} (φ : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (h : φ ≫ f₂ = f₁ ≫ g) (n : ℤ) :
    boundaryPairsMap φ g h n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ cyclesMap φ n :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma boundaryPairsMap_snd {P₁ P₂ K₁ K₂ : CochainComplex C ℤ}
    {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} (φ : P₁ ⟶ P₂) (g : K₁ ⟶ K₂)
    (h : φ ≫ f₂ = f₁ ≫ g) (n : ℤ) :
    boundaryPairsMap φ g h n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g.f (n - 1) :=
  pullback.lift_snd _ _ _

/-- The induced morphism on graded zero-differential complexes from a family of morphisms. -/
private def gradedMap {F₁ F₂ : ℤ → C} (u : ∀ n, F₁ n ⟶ F₂ n) :
    graded (.up ℤ) F₁ ⟶ graded (.up ℤ) F₂ where
  f := u
  comm' _ _ _ := by simp

@[simp]
private lemma gradedMap_f {F₁ F₂ : ℤ → C} (u : ∀ n, F₁ n ⟶ F₂ n) (n : ℤ) :
    (gradedMap u).f n = u n := rfl

variable (E : C ⥤ C) (p : E ⟶ 𝟭 C)

/-- The morphism induced by `g : K ⟶ L` at stage `k` of the K-flat resolution, packaged with its
commutativity with the stage morphisms to `K` and `L`. -/
private def stageMapPair {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ∀ k : ℕ, { φ : (stage E.obj p.app K k).1 ⟶ (stage E.obj p.app L k).1 //
      φ ≫ (stage E.obj p.app L k).2 = (stage E.obj p.app K k).2 ≫ g }
  | 0 =>
    ⟨gradedMap fun n ↦ E.map (cyclesMap g n), by
      ext n
      dsimp [stage, gradedMap]
      rw [p.naturality_assoc, Functor.id_map, cyclesMap_i, Category.assoc]⟩
  | k + 1 =>
    let ih := stageMapPair g k
    let w (n : ℤ) := boundaryPairsMap ih.1 g ih.2 n
    let ψ := gradedMap fun n ↦ E.map (w n)
    have hsq : attachingMap (stage E.obj p.app K k).2 (fun n ↦ p.app _) ≫ ih.1 =
        ψ ≫ attachingMap (stage E.obj p.app L k).2 (fun n ↦ p.app _) := by
      ext n
      dsimp [stage, ψ, gradedMap]
      rw [Category.assoc, Category.assoc, Category.assoc, p.naturality_assoc, Functor.id_map,
        boundaryPairsMap_fst_assoc ih.1 g ih.2 n, cyclesMap_i]
    ⟨mappingCone.map _ _ ψ ih.1 hsq, by
      ext n
      refine mappingCone.ext_from _ (n + 1) n rfl ?_ ?_
      · simp only [stage, comp_f, mappingCone.inl_v_map_f_assoc, mappingCone.inl_v_desc_f,
          boundaryPrimitive, HomComplex.Cochain.mk_v, ψ, gradedMap_f]
        rw [p.naturality_assoc, Functor.id_map, boundaryPairsMap_snd_assoc ih.1 g ih.2 (n + 1),
          mappingCone.inl_v_desc_f_assoc]
        simp only [boundaryPrimitive, HomComplex.Cochain.mk_v, Category.assoc]
        congr 2
        have hEq : ∀ m (hm : m = n),
            g.f m ≫ (L.XIsoOfEq hm).hom = (K.XIsoOfEq hm).hom ≫ g.f n := by
          rintro _ rfl
          simp
        exact hEq _ (by omega)
      · simp only [stage, comp_f]
        rw [mappingCone.inr_f_map_f_assoc, mappingCone.inr_f_desc_f, mappingCone.inr_f_desc_f_assoc,
          ← comp_f, ← comp_f, ih.2]⟩

/-- The morphism induced by `g : K ⟶ L` on the `k`-th stage of the K-flat resolution. -/
private def stageMap {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    (stage E.obj p.app K k).1 ⟶ (stage E.obj p.app L k).1 :=
  (stageMapPair E p g k).1

private lemma stageMap_comm {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    stageMap E p g k ≫ (stage E.obj p.app L k).2 = (stage E.obj p.app K k).2 ≫ g :=
  (stageMapPair E p g k).2

private lemma stageMap_inr {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    mappingCone.inr (attachingMap (stage E.obj p.app K k).2 fun n ↦ p.app _) ≫
        stageMap E p g (k + 1) =
      stageMap E p g k ≫
        mappingCone.inr (attachingMap (stage E.obj p.app L k).2 fun n ↦ p.app _) := by
  ext n
  dsimp only [stageMap, stageMapPair, comp_f]
  exact mappingCone.inr_f_map_f _ _ _ _ _ n

private lemma stageMap_id (K : CochainComplex C ℤ) :
    ∀ k : ℕ, stageMap E p (𝟙 K) k = 𝟙 _
  | 0 => by
    ext n
    dsimp [stageMap, stageMapPair, gradedMap]
    rw [cyclesMap_id, E.map_id]
    rfl
  | k + 1 => by
    have ih := stageMap_id K k
    have hw (n : ℤ) :
        boundaryPairsMap (stageMap E p (𝟙 K) k) (𝟙 K) (stageMap_comm E p (𝟙 K) k) n = 𝟙 _ := by
      ext <;> simp [ih, cyclesMap_id]
    have hψ : gradedMap (fun n ↦ E.map (boundaryPairsMap (stageMap E p (𝟙 K) k) (𝟙 K)
        (stageMap_comm E p (𝟙 K) k) n)) = 𝟙 _ := by
      ext n
      dsimp [gradedMap]
      rw [hw n, E.map_id]
    dsimp only [stageMap, stageMapPair]
    have hEq : ∀ {X Y : CochainComplex C ℤ} {φ : X ⟶ Y}
        (a : X ⟶ X) (b : Y ⟶ Y), a = 𝟙 X → b = 𝟙 Y → ∀ (comm : φ ≫ b = a ≫ φ),
        mappingCone.map φ φ a b comm = 𝟙 (mappingCone φ) := by
      rintro _ _ _ _ _ rfl rfl _
      exact mappingCone.map_id _
    exact hEq _ _ hψ ih _

private lemma stageMap_comp {K L M : CochainComplex C ℤ} (g : K ⟶ L) (h : L ⟶ M) :
    ∀ k : ℕ, stageMap E p (g ≫ h) k = stageMap E p g k ≫ stageMap E p h k
  | 0 => by
    ext n
    dsimp [stageMap, stageMapPair, gradedMap]
    rw [cyclesMap_comp, E.map_comp]
    rfl
  | k + 1 => by
    have ih := stageMap_comp g h k
    have hw (n : ℤ) :
        boundaryPairsMap (stageMap E p (g ≫ h) k) (g ≫ h) (stageMap_comm E p (g ≫ h) k) n =
          boundaryPairsMap (stageMap E p g k) g (stageMap_comm E p g k) n ≫
            boundaryPairsMap (stageMap E p h k) h (stageMap_comm E p h k) n := by
      ext <;> simp [ih, cyclesMap_comp]
    have hψ : gradedMap (fun n ↦ E.map (boundaryPairsMap (stageMap E p (g ≫ h) k) (g ≫ h)
          (stageMap_comm E p (g ≫ h) k) n)) =
        gradedMap (fun n ↦ E.map (boundaryPairsMap (stageMap E p g k) g
          (stageMap_comm E p g k) n)) ≫
        gradedMap (fun n ↦ E.map (boundaryPairsMap (stageMap E p h k) h
          (stageMap_comm E p h k) n)) := by
      ext n
      dsimp [gradedMap]
      rw [hw n, E.map_comp]
    dsimp only [stageMap, stageMapPair]
    have hEq : ∀ {X₁ Y₁ X₂ Y₂ X₃ Y₃ : CochainComplex C ℤ}
        {φ₁ : X₁ ⟶ Y₁} {φ₂ : X₂ ⟶ Y₂} {φ₃ : X₃ ⟶ Y₃}
        (a₁ : X₁ ⟶ X₂) (b₁ : Y₁ ⟶ Y₂) (a₂ : X₂ ⟶ X₃) (b₂ : Y₂ ⟶ Y₃)
        (a₃ : X₁ ⟶ X₃) (b₃ : Y₁ ⟶ Y₃),
        a₃ = a₁ ≫ a₂ → b₃ = b₁ ≫ b₂ →
        ∀ (c₁ : φ₁ ≫ b₁ = a₁ ≫ φ₂) (c₂ : φ₂ ≫ b₂ = a₂ ≫ φ₃)
          (c₃ : φ₁ ≫ b₃ = a₃ ≫ φ₃),
        mappingCone.map φ₁ φ₃ a₃ b₃ c₃ =
          mappingCone.map φ₁ φ₂ a₁ b₁ c₁ ≫
            mappingCone.map φ₂ φ₃ a₂ b₂ c₂ := by
      rintro _ _ _ _ _ _ _ _ _ a₁ b₁ a₂ b₂ _ _ rfl rfl c₁ c₂ _
      exact mappingCone.map_comp _ _ _ a₁ b₁ c₁ a₂ b₂ c₂
    exact hEq _ _ _ _ _ _ hψ ih _ _ _

/-- The natural transformation of resolution sequences induced by a morphism `g : K ⟶ L`. -/
public def sequenceMap {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    sequence E.obj p.app K ⟶ sequence E.obj p.app L :=
  NatTrans.ofSequence (stageMap E p g) fun k ↦ by
    rw [sequence_map_succ, sequence_map_succ]
    exact stageMap_inr E p g k

/-- The induced map of resolution sequences on an identity morphism is the identity. -/
@[simp]
public lemma sequenceMap_id (K : CochainComplex C ℤ) :
    sequenceMap E p (𝟙 K) = 𝟙 (sequence E.obj p.app K) :=
  NatTrans.ext (funext fun k ↦ stageMap_id E p K k)

/-- The induced map of resolution sequences respects composition. -/
@[simp]
public lemma sequenceMap_comp {K L M : CochainComplex C ℤ} (g : K ⟶ L) (h : L ⟶ M) :
    sequenceMap E p (g ≫ h) = sequenceMap E p g ≫ sequenceMap E p h :=
  NatTrans.ext (funext fun k ↦ stageMap_comp E p g h k)

/-- At each stage `k`, `sequenceMap` commutes with the canonical maps `toComplex`. -/
@[reassoc (attr := simp)]
public lemma sequenceMap_app_comp_toComplex {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    (sequenceMap E p g).app k ≫ (toComplex E.obj p.app L).app k =
      (toComplex E.obj p.app K).app k ≫ g :=
  stageMap_comm E p g k

end kFlatResolution

section Functor

variable [HasColimitsOfShape ℕ C] (E : C ⥤ C) (p : E ⟶ 𝟭 C)

/-- The functorial K-flat resolution `K ↦ kFlatResolution E.obj p.app K` associated to a natural
transformation `p : E ⟶ 𝟭 C`. -/
@[expose] public def kFlatResolutionFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := kFlatResolution E.obj p.app K
  map g := colimMap (kFlatResolution.sequenceMap E p g)
  map_id K := by
    apply colimit.hom_ext
    intro k
    simp
  map_comp g h := by
    apply colimit.hom_ext
    intro k
    simp

/-- On objects, `kFlatResolutionFunctor E p` agrees with `kFlatResolution E.obj p.app`. -/
@[simp]
public lemma kFlatResolutionFunctor_obj (K : CochainComplex C ℤ) :
    (kFlatResolutionFunctor E p).obj K = kFlatResolution E.obj p.app K := rfl

/-- The natural projection from the functorial K-flat resolution to the identity functor. -/
@[expose] public def kFlatResolutionFunctorπ :
    kFlatResolutionFunctor E p ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := kFlatResolution.π E.obj p.app K
  naturality K L g := by
    apply colimit.hom_ext
    intro k
    simp only [kFlatResolutionFunctor, Functor.id_obj, Functor.id_map, ι_colimMap_assoc,
      kFlatResolution.ι_π, kFlatResolution.ι_π_assoc]
    exact kFlatResolution.sequenceMap_app_comp_toComplex E p g k

/-- On each complex `K`, the natural projection `kFlatResolutionFunctorπ` is
`kFlatResolution.π`. -/
@[simp]
public lemma kFlatResolutionFunctorπ_app (K : CochainComplex C ℤ) :
    (kFlatResolutionFunctorπ E p).app K = kFlatResolution.π E.obj p.app K := rfl

end Functor

end Functorial

section DerivabilityStructure

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

variable (C) in
/-- The `ObjectProperty` of K-flat cochain complexes in `C`. -/
@[expose] public def isKFlatProperty : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ K.IsKFlat

public instance (K : (isKFlatProperty C).FullSubcategory) : K.obj.IsKFlat :=
  K.property

variable (C) in
/-- The localizer morphism given by the inclusion of the full subcategory of K-flat complexes into
`CochainComplex C ℤ`, with quasi-isomorphisms as weak equivalences. -/
@[expose, implicit_reducible, simps]
public def kFlatLocalizerMorphism :
    LocalizerMorphism
      ((HomologicalComplex.quasiIso C (.up ℤ)).inverseImage (isKFlatProperty C).ι)
      (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := (isKFlatProperty C).ι
  map _ _ _ h := h

public instance : (kFlatLocalizerMorphism C).IsInduced where
  inverseImage_eq := rfl

public instance : (kFlatLocalizerMorphism C).functor.Full :=
  inferInstanceAs (isKFlatProperty C).ι.Full

public instance : (kFlatLocalizerMorphism C).functor.Faithful :=
  inferInstanceAs (isKFlatProperty C).ι.Faithful

/-- **The K-flat left derivability structure.** Let `C` be an abelian monoidal category with a
functorial cover `p : E ⟶ 𝟭 C` by flat objects, in which countable coproducts and sequential
colimits are exact and commute with tensoring by each object. Then the inclusion of K-flat
complexes into `CochainComplex C ℤ` is a left derivability structure for quasi-isomorphisms. -/
public theorem isLeftDerivabilityStructure_kFlatLocalizerMorphism
    (E : C ⥤ C) (p : E ⟶ 𝟭 C) [∀ X, Epi (p.app X)]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] :
    (kFlatLocalizerMorphism C).IsLeftDerivabilityStructure := by
  let ρ : CochainComplex C ℤ ⥤ (isKFlatProperty C).FullSubcategory :=
    (isKFlatProperty C).lift (kFlatResolutionFunctor E p) fun K ↦
      isKFlat_kFlatResolution E.obj p.app K
  let π : ρ ⋙ (kFlatLocalizerMorphism C).functor ⟶ 𝟭 (CochainComplex C ℤ) :=
    kFlatResolutionFunctorπ E p
  exact (kFlatLocalizerMorphism C).isLeftDerivabilityStructure_of_functorial_resolutions
    (ρ := ρ) π (fun K ↦ kFlatResolution.quasiIso_π E.obj p.app K) rfl

end DerivabilityStructure

end CochainComplex
