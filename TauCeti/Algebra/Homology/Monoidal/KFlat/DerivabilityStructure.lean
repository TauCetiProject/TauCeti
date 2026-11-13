/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
public import TauCeti.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Functorial K-flat resolutions and the K-flat left derivability structure

Let `C` be an abelian category equipped with a functor `E : C ⥤ C` and a natural transformation
`p : E ⟶ 𝟭 C`. Then the cell-attachment sequence `kFlatResolution.sequence E.obj p.app` and its
colimit `CochainComplex.kFlatResolution E.obj p.app` depend functorially on the cochain complex `K`
(`CochainComplex.kFlatResolution.sequenceFunctor` and `CochainComplex.kFlatResolution.functor`),
and the resolution morphisms `kFlatResolution.π` assemble into a natural transformation
`CochainComplex.kFlatResolution.πNatTrans`.

When `C` is monoidal preadditive, countable coproducts and sequential colimits are exact and
commute with tensoring, every `p.app X` is an epimorphism, and every `E.obj X` is flat, the
inclusion `CochainComplex.kFlatLocalizerMorphism C` of the full subcategory of K-flat cochain
complexes into `CochainComplex C ℤ` is a left derivability structure with respect to
quasi-isomorphisms (`CochainComplex.isLeftDerivabilityStructure_kFlatLocalizerMorphism`).

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

open HomComplex

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

namespace kFlatResolution

section StepMap

variable {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
  {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} {f₃ : P₃ ⟶ K₃}
  {u : P₁ ⟶ P₂} {v : K₁ ⟶ K₂}

/-- A commutative square `(u, v)` from `f₁ : P₁ ⟶ K₁` to `f₂ : P₂ ⟶ K₂` induces a morphism between
their objects of boundary pairs in each degree. -/
def boundaryPairsMap (huv : u ≫ f₂ = f₁ ≫ v) (n : ℤ) :
    boundaryPairs f₁ n ⟶ boundaryPairs f₂ n :=
  pullback.map (cyclesMap f₁ n) (K₁.toCycles (n - 1) n)
    (cyclesMap f₂ n) (K₂.toCycles (n - 1) n)
    (cyclesMap u n) (v.f (n - 1)) (cyclesMap v n)
    (by rw [← cyclesMap_comp, ← cyclesMap_comp, huv])
    (by rw [← cancel_mono (K₂.iCycles n), Category.assoc, cyclesMap_i,
      toCycles_i_assoc, Category.assoc, toCycles_i, v.comm])

/-- The first projection of `boundaryPairsMap` is `cyclesMap u`. -/
@[reassoc (attr := simp)]
lemma boundaryPairsMap_fst (huv : u ≫ f₂ = f₁ ≫ v) (n : ℤ) :
    boundaryPairsMap huv n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ cyclesMap u n :=
  pullback.lift_fst ..

/-- The second projection of `boundaryPairsMap` is the component of `v` in degree `n - 1`. -/
@[reassoc (attr := simp)]
lemma boundaryPairsMap_snd (huv : u ≫ f₂ = f₁ ≫ v) (n : ℤ) :
    boundaryPairsMap huv n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ v.f (n - 1) :=
  pullback.lift_snd ..

/-- Identity squares act by the identity on boundary pairs. -/
@[simp]
lemma boundaryPairsMap_id (f : P₁ ⟶ K₁) (n : ℤ) :
    boundaryPairsMap (u := 𝟙 P₁) (v := 𝟙 K₁) (by simp) n = 𝟙 (boundaryPairs f n) :=
  pullback.hom_ext (by simp) (by simp)

/-- Composition of commutative squares induces composition on boundary pairs. -/
lemma boundaryPairsMap_comp {u' : P₂ ⟶ P₃} {v' : K₂ ⟶ K₃}
    (huv : u ≫ f₂ = f₁ ≫ v) (huv' : u' ≫ f₃ = f₂ ≫ v') (n : ℤ) :
    boundaryPairsMap (u := u ≫ u') (v := v ≫ v')
        (by rw [Category.assoc, huv', ← Category.assoc, huv, Category.assoc]) n =
      boundaryPairsMap huv n ≫ boundaryPairsMap huv' n :=
  pullback.hom_ext (by simp [cyclesMap_comp]) (by simp)

private def cellComplexMap (E : C ⥤ C) (huv : u ≫ f₂ = f₁ ≫ v) :
    graded (.up ℤ) (fun n ↦ E.obj (boundaryPairs f₁ n)) ⟶
      graded (.up ℤ) (fun n ↦ E.obj (boundaryPairs f₂ n)) where
  f n := E.map (boundaryPairsMap huv n)
  comm' _ _ _ := by simp

private lemma attachingMap_comm (E : C ⥤ C) (p : E ⟶ 𝟭 C) (huv : u ≫ f₂ = f₁ ≫ v) :
    attachingMap f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ u =
      cellComplexMap E huv ≫ attachingMap f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) := by
  ext n
  dsimp [cellComplexMap]
  simp only [Category.assoc]
  rw [← cyclesMap_i, ← boundaryPairsMap_fst_assoc huv n, p.naturality_assoc, Functor.id_map]

private def attachStepMap (E : C ⥤ C) (p : E ⟶ 𝟭 C) (huv : u ≫ f₂ = f₁ ≫ v) :
    mappingCone (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ⟶
      mappingCone (attachingMap f₂ fun n ↦ p.app (boundaryPairs f₂ n)) :=
  mappingCone.map _ _ (cellComplexMap E huv) u (attachingMap_comm E p huv)

private lemma attachStepMap_congr (E : C ⥤ C) (p : E ⟶ 𝟭 C) {u' : P₁ ⟶ P₂} (hu : u = u')
    (huv : u ≫ f₂ = f₁ ≫ v) (huv' : u' ≫ f₂ = f₁ ≫ v) :
    attachStepMap E p huv = attachStepMap E p huv' := by subst hu; rfl

private lemma attachStepMap_comp_attachDesc (E : C ⥤ C) (p : E ⟶ 𝟭 C) (huv : u ≫ f₂ = f₁ ≫ v) :
    attachStepMap E p huv ≫ attachDesc f₂ (fun n ↦ p.app (boundaryPairs f₂ n)) =
      attachDesc f₁ (fun n ↦ p.app (boundaryPairs f₁ n)) ≫ v := by
  ext q
  apply mappingCone.ext_from _ (q + 1) q rfl
  · simp only [attachStepMap, comp_f, mappingCone.inl_v_map_f_assoc,
      mappingCone.inl_v_desc_f, mappingCone.inl_v_desc_f_assoc, cellComplexMap]
    dsimp [boundaryPrimitive]
    simp only [Category.assoc]
    rw [p.naturality_assoc, Functor.id_map, boundaryPairsMap_snd_assoc huv (q + 1),
      XIsoOfEq_hom_naturality]
  · simp only [attachStepMap, comp_f, mappingCone.inr_f_map_f_assoc]
    have h₁ := HomologicalComplex.congr_hom
      (inr_attachDesc f₂ fun n ↦ p.app (boundaryPairs f₂ n)) q
    have h₂ := HomologicalComplex.congr_hom
      (inr_attachDesc f₁ fun n ↦ p.app (boundaryPairs f₁ n)) q
    simp only [comp_f] at h₁ h₂
    rw [h₁, reassoc_of% h₂, ← comp_f, ← comp_f, huv]

private lemma inr_attachStepMap (E : C ⥤ C) (p : E ⟶ 𝟭 C) (huv : u ≫ f₂ = f₁ ≫ v) :
    mappingCone.inr (attachingMap f₁ fun n ↦ p.app (boundaryPairs f₁ n)) ≫
      attachStepMap E p huv =
        u ≫ mappingCone.inr (attachingMap f₂ fun n ↦ p.app (boundaryPairs f₂ n)) := by
  simp [attachStepMap, mappingCone.map]

private lemma attachStepMap_id (E : C ⥤ C) (p : E ⟶ 𝟭 C) (f : P₁ ⟶ K₁) :
    attachStepMap E p (u := 𝟙 P₁) (v := 𝟙 K₁) (by simp) =
      𝟙 (mappingCone (attachingMap f fun n ↦ p.app (boundaryPairs f n))) := by
  dsimp only [attachStepMap]
  rw [← mappingCone.map_id]
  congr 1; ext n; simp [cellComplexMap]

private lemma attachStepMap_comp (E : C ⥤ C) (p : E ⟶ 𝟭 C) {u' : P₂ ⟶ P₃} {v' : K₂ ⟶ K₃}
    (huv : u ≫ f₂ = f₁ ≫ v) (huv' : u' ≫ f₃ = f₂ ≫ v') :
    attachStepMap E p (u := u ≫ u') (v := v ≫ v')
        (by rw [Category.assoc, huv', ← Category.assoc, huv, Category.assoc]) =
      attachStepMap E p huv ≫ attachStepMap E p huv' := by
  dsimp only [attachStepMap]
  rw [← mappingCone.map_comp]
  congr 1; ext n; dsimp [cellComplexMap]
  rw [boundaryPairsMap_comp huv huv', E.map_comp]

end StepMap

section Functorial

variable (E : C ⥤ C) (p : E ⟶ 𝟭 C)

private def stageMapAux {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ∀ k : ℕ, { u : (stage E.obj p.app K k).1 ⟶ (stage E.obj p.app L k).1 //
      u ≫ (stage E.obj p.app L k).2 = (stage E.obj p.app K k).2 ≫ g }
  | 0 => ⟨{ f := fun n ↦ E.map (cyclesMap g n), comm' := fun _ _ _ ↦ by dsimp [stage]; simp }, by
      ext n; dsimp [stage]; rw [p.naturality_assoc, Functor.id_map, cyclesMap_i, Category.assoc]⟩
  | k + 1 => ⟨attachStepMap E p (stageMapAux g k).2,
      attachStepMap_comp_attachDesc E p (stageMapAux g k).2⟩

/-- The morphism induced on stage `k` of `kFlatResolution` by a chain map `g : K ⟶ L`. -/
def stageMap {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    (stage E.obj p.app K k).1 ⟶ (stage E.obj p.app L k).1 :=
  (stageMapAux E p g k).1

/-- The induced maps on the stages commute with the projections to `K` and `L`. -/
@[reassoc (attr := simp)]
lemma stageMap_comp_snd {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    stageMap E p g k ≫ (stage E.obj p.app L k).2 = (stage E.obj p.app K k).2 ≫ g :=
  (stageMapAux E p g k).2

/-- On the initial stage, `stageMap` applies `E` to the induced maps on cycles. -/
@[simp]
lemma stageMap_zero_f {K L : CochainComplex C ℤ} (g : K ⟶ L) (n : ℤ) :
    (stageMap E p g 0).f n = E.map (cyclesMap g n) := (rfl)

/-- On stage `k + 1`, `stageMap` acts on the attached cells in degree `m` by applying `E` to
`boundaryPairsMap`. -/
@[simp]
lemma inl_v_stageMap_f {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) (m q : ℤ)
    (hmq : m + -1 = q) :
    (mappingCone.inl (attachingMap (stage E.obj p.app K k).2
      fun n ↦ p.app (boundaryPairs (stage E.obj p.app K k).2 n))).v m q hmq ≫
        (stageMap E p g (k + 1)).f q =
      E.map (boundaryPairsMap (stageMap_comp_snd E p g k) m) ≫
        (mappingCone.inl (attachingMap (stage E.obj p.app L k).2
          fun n ↦ p.app (boundaryPairs (stage E.obj p.app L k).2 n))).v m q hmq :=
  mappingCone.inl_v_map_f _ _ (cellComplexMap E (stageMapAux E p g k).2)
    (stageMapAux E p g k).1 (attachingMap_comm E p (stageMapAux E p g k).2) m q hmq

-- State the right-associated `@[simp]` variants of `inl_v_stageMap_f`, `inr_stageMap`, and
-- `inr_f_stageMap_f` explicitly: `kFlatResolution.stage` is `semireducible`, so `@[reassoc]`
-- cannot apply `Category.assoc` at `implicit` transparency and leaves `(a ≫ b) ≫ h` unassociated.

/-- Reassociated form of `inl_v_stageMap_f`. -/
@[simp]
lemma inl_v_stageMap_f_assoc {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) (m q : ℤ)
    (hmq : m + -1 = q) {Z : C} (h : ((stage E.obj p.app L (k + 1)).1).X q ⟶ Z) :
    (mappingCone.inl (attachingMap (stage E.obj p.app K k).2
      fun n ↦ p.app (boundaryPairs (stage E.obj p.app K k).2 n))).v m q hmq ≫
        (stageMap E p g (k + 1)).f q ≫ h =
      E.map (boundaryPairsMap (stageMap_comp_snd E p g k) m) ≫
        (mappingCone.inl (attachingMap (stage E.obj p.app L k).2
          fun n ↦ p.app (boundaryPairs (stage E.obj p.app L k).2 n))).v m q hmq ≫ h :=
  (Category.assoc _ _ h).symm.trans
    ((congrArg (· ≫ h) (inl_v_stageMap_f E p g k m q hmq)).trans (Category.assoc _ _ h))

/-- The stage maps commute with the inclusions into the next stages. -/
@[simp]
lemma inr_stageMap {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    mappingCone.inr (attachingMap (stage E.obj p.app K k).2
      fun n ↦ p.app (boundaryPairs (stage E.obj p.app K k).2 n)) ≫
        stageMap E p g (k + 1) =
      stageMap E p g k ≫ mappingCone.inr (attachingMap (stage E.obj p.app L k).2
        fun n ↦ p.app (boundaryPairs (stage E.obj p.app L k).2 n)) :=
  inr_attachStepMap E p (stageMapAux E p g k).2

/-- Reassociated form of `inr_stageMap`. -/
@[simp]
lemma inr_stageMap_assoc {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ)
    {Z : CochainComplex C ℤ} (h : (stage E.obj p.app L (k + 1)).1 ⟶ Z) :
    mappingCone.inr (attachingMap (stage E.obj p.app K k).2
      fun n ↦ p.app (boundaryPairs (stage E.obj p.app K k).2 n)) ≫
        stageMap E p g (k + 1) ≫ h =
      stageMap E p g k ≫
        mappingCone.inr (attachingMap (stage E.obj p.app L k).2
          fun n ↦ p.app (boundaryPairs (stage E.obj p.app L k).2 n)) ≫ h :=
  (Category.assoc _ _ h).symm.trans
    ((congrArg (· ≫ h) (inr_stageMap E p g k)).trans (Category.assoc _ _ h))

/-- In each degree, the stage maps commute with the inclusions into the next stages. -/
@[simp]
lemma inr_f_stageMap_f {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) (q : ℤ) :
    (mappingCone.inr (attachingMap (stage E.obj p.app K k).2
      fun n ↦ p.app (boundaryPairs (stage E.obj p.app K k).2 n))).f q ≫
        (stageMap E p g (k + 1)).f q =
      (stageMap E p g k).f q ≫
        (mappingCone.inr (attachingMap (stage E.obj p.app L k).2
          fun n ↦ p.app (boundaryPairs (stage E.obj p.app L k).2 n))).f q :=
  HomologicalComplex.congr_hom (inr_stageMap E p g k) q

/-- Reassociated form of `inr_f_stageMap_f`. -/
@[simp]
lemma inr_f_stageMap_f_assoc {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) (q : ℤ)
    {Z : C} (h : ((stage E.obj p.app L (k + 1)).1).X q ⟶ Z) :
    (mappingCone.inr (attachingMap (stage E.obj p.app K k).2
      fun n ↦ p.app (boundaryPairs (stage E.obj p.app K k).2 n))).f q ≫
        (stageMap E p g (k + 1)).f q ≫ h =
      (stageMap E p g k).f q ≫
        (mappingCone.inr (attachingMap (stage E.obj p.app L k).2
          fun n ↦ p.app (boundaryPairs (stage E.obj p.app L k).2 n))).f q ≫ h :=
  (Category.assoc _ _ h).symm.trans
    ((congrArg (· ≫ h) (inr_f_stageMap_f E p g k q)).trans (Category.assoc _ _ h))

/-- Identity chain maps induce identity morphisms on every stage. -/
@[simp]
lemma stageMap_id (K : CochainComplex C ℤ) :
    ∀ k : ℕ, stageMap E p (𝟙 K) k = 𝟙 (stage E.obj p.app K k).1
  | 0 => by ext n; dsimp [stage, stageMap, stageMapAux]; simp
  | k + 1 => (attachStepMap_congr E p (stageMap_id K k) _ (by simp)).trans (attachStepMap_id E p _)

/-- Composition of chain maps induces composition on every stage. -/
@[simp]
lemma stageMap_comp {K L M : CochainComplex C ℤ} (g₁ : K ⟶ L) (g₂ : L ⟶ M) :
    ∀ k : ℕ, stageMap E p (g₁ ≫ g₂) k = stageMap E p g₁ k ≫ stageMap E p g₂ k
  | 0 => by ext n; dsimp [stage, stageMap, stageMapAux]; simp [cyclesMap_comp]
  | k + 1 =>
      (attachStepMap_congr E p (stageMap_comp g₁ g₂ k) _ _).trans
        (attachStepMap_comp E p (stageMapAux E p g₁ k).2 (stageMapAux E p g₂ k).2)

/-- The functor sending a cochain complex `K` to its cell-attachment sequence
`kFlatResolution.sequence E.obj p.app K`. -/
-- Expose and mark `implicit_reducible` so `(sequenceFunctor E p).obj K` unifies with `sequence`.
@[expose, implicit_reducible]
def sequenceFunctor : CochainComplex C ℤ ⥤ (ℕ ⥤ CochainComplex C ℤ) where
  obj K := sequence E.obj p.app K
  map g := NatTrans.ofSequence (stageMap E p g) fun k ↦ by
    rw [sequence_map_succ, sequence_map_succ]; exact inr_stageMap E p g k
  map_id K := NatTrans.ext <| funext <| stageMap_id E p K
  map_comp g₁ g₂ := NatTrans.ext <| funext <| stageMap_comp E p g₁ g₂

/-- On objects, `sequenceFunctor E p` is `kFlatResolution.sequence E.obj p.app`. -/
@[simp]
lemma sequenceFunctor_obj (K : CochainComplex C ℤ) :
    (sequenceFunctor E p).obj K = sequence E.obj p.app K := (rfl)

/-- At stage `k`, `(sequenceFunctor E p).map g` acts by `stageMap E p g k`. -/
@[simp]
lemma sequenceFunctor_map_app {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    ((sequenceFunctor E p).map g).app k = stageMap E p g k := (rfl)

section Colimit

variable [HasColimitsOfShape ℕ C]

/-- The functor `CochainComplex C ℤ ⥤ CochainComplex C ℤ` sending each complex `K` to the
cell-attachment colimit `kFlatResolution E.obj p.app K` associated to `E : C ⥤ C` and
`p : E ⟶ 𝟭 C`. When `C` is monoidal preadditive with exact countable coproducts and sequential
colimits commuting with tensoring and every `E.obj X` is flat, its values are K-flat; when
moreover each `p.app X` is an epimorphism and sequential colimits are exact, `πNatTrans E p` is a
componentwise quasi-isomorphism. -/
-- Expose and mark `implicit_reducible` so `(functor E p).obj K` unifies with `kFlatResolution`.
@[expose, implicit_reducible]
def functor : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  sequenceFunctor E p ⋙ colim

/-- On objects, `kFlatResolution.functor E p` agrees with `kFlatResolution E.obj p.app`. -/
@[simp]
lemma functor_obj (K : CochainComplex C ℤ) :
    (functor E p).obj K = kFlatResolution E.obj p.app K := (rfl)

/-- On morphisms, `kFlatResolution.functor E p` intertwines the colimit injections with
`stageMap`. -/
@[reassoc (attr := simp)]
lemma ι_functor_map {K L : CochainComplex C ℤ} (g : K ⟶ L) (k : ℕ) :
    colimit.ι (sequence E.obj p.app K) k ≫ (functor E p).map g =
      stageMap E p g k ≫ colimit.ι (sequence E.obj p.app L) k :=
  ι_colimMap ((sequenceFunctor E p).map g) k

/-- The comparison morphisms `kFlatResolution.π` assemble into a natural transformation
`kFlatResolution.functor E p ⟶ 𝟭 (CochainComplex C ℤ)`. -/
def πNatTrans : functor E p ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := π E.obj p.app K
  -- Use `erw` (`default` transparency) and `rfl` rather than `simp`: `kFlatResolution.sequence`
  -- and `kFlatResolution.toComplex` are `semireducible`, so `(sequence _ _ _).obj k =
  -- (stage _ _ _ k).1` and `(toComplex _ _ _).app k = (stage _ _ _ k).2` unify at `default`
  -- rather than `reducible`/`implicit` transparency.
  naturality {K _} g := colimit.hom_ext (F := sequence E.obj p.app K) fun k ↦ by
    erw [ι_functor_map_assoc, Category.assoc, ι_π, stageMap_comp_snd, ι_π_assoc]; rfl

/-- Each component of `πNatTrans E p` is `kFlatResolution.π E.obj p.app`. -/
@[simp]
lemma πNatTrans_app (K : CochainComplex C ℤ) : (πNatTrans E p).app K = π E.obj p.app K := (rfl)

/-- Naturality of `kFlatResolution.π` with respect to `kFlatResolution.functor E p`. -/
@[reassoc (attr := simp)]
lemma functor_map_π {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (functor E p).map g ≫ π E.obj p.app L = π E.obj p.app K ≫ g :=
  (πNatTrans E p).naturality g

/-- When sequential colimits in `C` are exact and every `p.app X` is an epimorphism, each component
of `kFlatResolution.πNatTrans E p` belongs to `quasiIso C (.up ℤ)`. -/
lemma mem_quasiIso_πNatTrans_app [HasExactColimitsOfShape ℕ C] [∀ X : C, Epi (p.app X)]
    (K : CochainComplex C ℤ) : quasiIso C (.up ℤ) ((πNatTrans E p).app K) :=
  (mem_quasiIso_iff _).2 (inferInstanceAs (QuasiIso (π E.obj p.app K)))

end Colimit

end Functorial

end kFlatResolution

end Abelian

section DerivabilityStructure

variable (C : Type*) [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The object property on `CochainComplex C ℤ` selecting K-flat cochain complexes. -/
abbrev kFlat : ObjectProperty (CochainComplex C ℤ) := fun K ↦ K.IsKFlat

/-- A cochain complex belongs to `CochainComplex.kFlat C` if and only if it is K-flat. -/
@[simp]
lemma mem_kFlat_iff (K : CochainComplex C ℤ) : kFlat C K ↔ K.IsKFlat := Iff.rfl

instance (P : (kFlat C).FullSubcategory) : P.obj.IsKFlat := P.property

/-- The localizer morphism given by the inclusion of the full subcategory of K-flat cochain
complexes into `CochainComplex C ℤ`, with respect to quasi-isomorphisms. -/
def kFlatLocalizerMorphism :
    LocalizerMorphism ((quasiIso C (.up ℤ)).inverseImage (kFlat C).ι) (quasiIso C (.up ℤ)) where
  functor := (kFlat C).ι
  map _ _ _ hf := hf

/-- The underlying functor of `kFlatLocalizerMorphism C` is the full subcategory inclusion
`(kFlat C).ι`. -/
@[simp]
lemma kFlatLocalizerMorphism_functor : (kFlatLocalizerMorphism C).functor = (kFlat C).ι := (rfl)

instance : (kFlatLocalizerMorphism C).IsInduced where inverseImage_eq := (rfl)
instance : (kFlatLocalizerMorphism C).functor.Full := inferInstanceAs (kFlat C).ι.Full
instance : (kFlatLocalizerMorphism C).functor.Faithful := inferInstanceAs (kFlat C).ι.Faithful

section WithCover

variable {C}
  [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
  (E : C ⥤ C) (p : E ⟶ 𝟭 C)
  [∀ X : C, PreservesFiniteLimits (tensorLeft (E.obj X))]
  [∀ X : C, PreservesFiniteColimits (tensorLeft (E.obj X))]

/-- Lifting `kFlatResolution.functor E p` to the full subcategory of K-flat cochain complexes. -/
-- Expose so `((liftFunctor E p).obj K).obj` computes to `kFlatResolution E.obj p.app K`.
@[expose]
def kFlatResolution.liftFunctor : CochainComplex C ℤ ⥤ (kFlat C).FullSubcategory :=
  (kFlat C).lift (kFlatResolution.functor E p) fun K ↦ by
    rw [mem_kFlat_iff, kFlatResolution.functor_obj]; infer_instance

/-- On objects, `kFlatResolution.liftFunctor E p` has underlying complex
`kFlatResolution E.obj p.app K`. -/
@[simp]
lemma kFlatResolution.liftFunctor_obj_obj (K : CochainComplex C ℤ) :
    ((kFlatResolution.liftFunctor E p).obj K).obj = kFlatResolution E.obj p.app K := (rfl)

/-- On morphisms, `kFlatResolution.liftFunctor E p` acts by `(kFlatResolution.functor E p).map`. -/
@[simp]
lemma kFlatResolution.liftFunctor_map_hom {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    ((kFlatResolution.liftFunctor E p).map g).hom = (kFlatResolution.functor E p).map g := (rfl)

variable [∀ X : C, Epi (p.app X)]

include E p

/-- In an abelian monoidal preadditive category with exact countable coproducts and sequential
colimits commuting with tensoring, a functorial flat epimorphic cover makes
`kFlatLocalizerMorphism C` a localized equivalence. -/
theorem isLocalizedEquivalence_kFlatLocalizerMorphism :
    (kFlatLocalizerMorphism C).IsLocalizedEquivalence :=
  (kFlatLocalizerMorphism C).isLocalizedEquivalence_of_functorial_left_resolutions
    (ρ := kFlatResolution.liftFunctor E p)
    (kFlatResolution.πNatTrans E p) (kFlatResolution.mem_quasiIso_πNatTrans_app E p) rfl

/-- In an abelian monoidal preadditive category with exact countable coproducts and sequential
colimits commuting with tensoring, a functorial flat epimorphic cover gives every morphism in
`CochainComplex C ℤ` a left resolution by a morphism of K-flat complexes. -/
theorem hasLeftResolutions_arrow_kFlatLocalizerMorphism :
    (kFlatLocalizerMorphism C).arrow.HasLeftResolutions :=
  (kFlatLocalizerMorphism C).hasLeftResolutions_arrow_of_functorial_resolutions
    (ρ := kFlatResolution.liftFunctor E p)
    (kFlatResolution.πNatTrans E p) (kFlatResolution.mem_quasiIso_πNatTrans_app E p)

/-- In an abelian monoidal preadditive category with exact countable coproducts and sequential
colimits commuting with tensoring, a functorial flat epimorphic cover makes the category of K-flat
left resolutions of any cochain complex `K` connected. -/
theorem isConnected_leftResolution_kFlatLocalizerMorphism (K : CochainComplex C ℤ) :
    IsConnected ((kFlatLocalizerMorphism C).LeftResolution K) :=
  (kFlatLocalizerMorphism C).isConnected_leftResolution_of_functorial_resolutions
    (ρ := kFlatResolution.liftFunctor E p)
    (kFlatResolution.πNatTrans E p) (kFlatResolution.mem_quasiIso_πNatTrans_app E p) rfl K

/-- **The K-flat left derivability structure.** Let `C` be an abelian monoidal preadditive
category in which countable coproducts and sequential colimits are exact and commute with
tensoring, equipped with a functor `E : C ⥤ C` and an epimorphic natural transformation
`p : E ⟶ 𝟭 C` such that every `E.obj X` is flat. Then the inclusion
`kFlatLocalizerMorphism C` of K-flat complexes into `CochainComplex C ℤ` is a left derivability
structure with respect to quasi-isomorphisms. -/
theorem isLeftDerivabilityStructure_kFlatLocalizerMorphism :
    (kFlatLocalizerMorphism C).IsLeftDerivabilityStructure :=
  (kFlatLocalizerMorphism C).isLeftDerivabilityStructure_of_functorial_resolutions
    (ρ := kFlatResolution.liftFunctor E p)
    (kFlatResolution.πNatTrans E p) (kFlatResolution.mem_quasiIso_πNatTrans_app E p) rfl

end WithCover

end DerivabilityStructure

end CochainComplex
