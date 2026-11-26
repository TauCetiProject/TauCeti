/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Ext
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Embedding.MapExtend
public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Morphisms out of an extended chain complex

For a chain complex `X` in a `k`-linear abelian category and an object `Y`, the cochain complex
`Hom(X, Y)` (Mathlib's `ChainComplex.linearYonedaObj`) is computed degreewise. Extending `X` along
an embedding `e` of complex shapes (`HomologicalComplex.extend`) puts zero objects in the degrees
outside the image of `e`, and morphisms out of a zero object form the zero module. So
`Hom(X.extend e, Y)` is the extension of `Hom(X, Y)` along the opposite embedding
(`ChainComplex.linearYonedaObjExtendIso`). In a degree `e.f i` the isomorphism is the identity of
the module of morphisms `X.X i ⟶ Y`, up to the identifications of the terms of both extensions
(`ChainComplex.linearYonedaObjExtendIso_hom_f`, `ChainComplex.linearYonedaObjExtendIso_inv_f`), and
it is natural in `X` (`ChainComplex.linearYonedaObjExtendIso_hom_naturality`).

In particular, placing a chain complex indexed by `ℕ` `n` degrees higher
(`ComplexShape.embeddingDownNatAdd n`) places its cochain complex of morphisms into `Y` `n`
degrees higher too, so that the cohomology of `Hom(X.extend e, Y)` in degree `q + n` is the
cohomology of `Hom(X, Y)` in degree `q` (`ChainComplex.linearYonedaObjExtendHomologyIso`). This is
how a chain-level identification of one complex with a shift of another, such as the cap product
of a Thom isomorphism, computes cohomology with values in any `Y`.

## Main definitions

* `ChainComplex.linearYonedaObjExtendIso`: the isomorphism
  `Hom(X.extend e, Y) ≅ Hom(X, Y).extend e.op`.
* `ChainComplex.linearYonedaObjExtendHomologyIso`: for the embedding `i ↦ i + n` of
  `ComplexShape.down ℕ` (`ComplexShape.embeddingDownNatAdd n`), the isomorphism
  `H^{q + n}(Hom(X.extend e, Y)) ≅ H^q(Hom(X, Y))`, natural in `X`
  (`ChainComplex.linearYonedaObjExtendHomologyIso_hom_naturality`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {k : Type*} [Ring k] [Linear k C] (Y : C)
  {α β : Type*} [AddRightCancelSemigroup α] [One α] [AddRightCancelSemigroup β] [One β]

/-- **Morphisms out of an extended chain complex.** For an embedding `e` of complex shapes, the
cochain complex of morphisms from the extension `X.extend e` into `Y` is the extension of the
cochain complex of morphisms from `X` into `Y` along the opposite embedding: both are zero outside
the image of `e`. -/
def linearYonedaObjExtendIso (X : ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down β)) :
    ChainComplex.linearYonedaObj (X.extend e) k Y ≅ (X.linearYonedaObj k Y).extend e.op :=
  -- `Hom(-, Y)` is the image under the additive functor `Hom(-, Y)ᵒᵖ` followed by `unop`; the
  -- functor commutes with the extension, and so does `unop`, through Mathlib's `extendOpIso`
  (HomologicalComplex.unopFunctor _ _).mapIso
      (HomologicalComplex.mapExtendIso ((linearYoneda k C).obj Y).rightOp X e).symm.op ≪≫
    (HomologicalComplex.unopFunctor _ _).mapIso
      ((X.linearYonedaObj k Y).extendOpIso e.op).symm.op

/-- In a degree `e.f i`, the component of `linearYonedaObjExtendIso` is the identity of the module
of morphisms `X.X i ⟶ Y`, up to the identifications `HomologicalComplex.extendXIso` of the terms of
both extensions. -/
lemma linearYonedaObjExtendIso_hom_f (X : ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down β)) {i : α} {i' : β} (h : e.f i = i') :
    (linearYonedaObjExtendIso Y X e).hom.f i' =
      ((linearYoneda k C).obj Y).map (X.extendXIso e h).inv.op ≫
        ((X.linearYonedaObj k Y).extendXIso e.op h).inv := by
  -- `Hom(-, Y)` commutes with the extension by the identity in the degrees of the image of `e`
  have h₁ : (HomologicalComplex.mapExtendIso ((linearYoneda k C).obj Y).rightOp X e).inv.f i' =
      (((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).obj X).extendXIso e h).hom ≫
        ((linearYoneda k C).obj Y).rightOp.map (X.extendXIso e h).inv := by
    rw [← cancel_epi ((HomologicalComplex.mapExtendIso _ X e).hom.f i'),
      ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
      HomologicalComplex.mapExtendIso_hom_f _ X e h, Category.assoc, Iso.inv_hom_id_assoc,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  -- and so does the passage to the opposite category, through Mathlib's `extendOpIso`
  have h₂ : ((X.linearYonedaObj k Y).extendOpIso e.op).inv.f i' =
      ((X.linearYonedaObj k Y).extendXIso e.op h).inv.op ≫
        ((X.linearYonedaObj k Y).op.extendXIso e.op.op h).inv := by
    have key : ∀ (o : Option α) (ho : o = some i),
        (HomologicalComplex.extend.XOpIso (X.linearYonedaObj k Y) o).inv =
          (HomologicalComplex.extend.XIso (X.linearYonedaObj k Y) ho).inv.op ≫
            (HomologicalComplex.extend.XIso (X.linearYonedaObj k Y).op ho).inv := by
      rintro _ rfl
      exact (Category.comp_id _).symm
    exact key _ (e.r_eq_some h)
  -- by definition, the component is that of the two isomorphisms, read through `unop`
  have h₃ : (linearYonedaObjExtendIso Y X e).hom.f i' =
      ((HomologicalComplex.mapExtendIso ((linearYoneda k C).obj Y).rightOp X e).inv.f i').unop ≫
        (((X.linearYonedaObj k Y).extendOpIso e.op).inv.f i').unop := rfl
  -- the two identifications in the middle are the same, as `(Hom(X, Y)).op` is `Hom(X, Y)` read in
  -- the opposite category
  have h₄ : ((X.linearYonedaObj k Y).op.extendXIso e.op.op h).inv ≫
      (((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).obj X).extendXIso e h).hom =
        𝟙 _ :=
    (((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).obj X).extendXIso e h).inv_hom_id
  rw [h₃, h₁, h₂, unop_comp, unop_comp, Quiver.Hom.unop_op]
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ?_))
  exact (congrArg (· ≫ _) (unop_comp.symm.trans
    ((congrArg Quiver.Hom.unop h₄).trans unop_id))).trans (Category.id_comp _)

/-- In a degree `e.f i`, `linearYonedaObjExtendIso` sends a morphism `g` out of the term of
`X.extend e` to its precomposition with `X.X i ≅ (X.extend e).X (e.f i)`. -/
lemma linearYonedaObjExtendIso_hom_f_hom_apply (X : ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down β)) {i : α} {i' : β} (h : e.f i = i')
    (g : (X.extend e).X i' ⟶ Y) :
    ConcreteCategory.hom (X := (ChainComplex.linearYonedaObj (X.extend e) k Y).X i')
        (Y := ((X.linearYonedaObj k Y).extend e.op).X i')
        ((linearYonedaObjExtendIso Y X e).hom.f i') g =
      ConcreteCategory.hom (X := (X.linearYonedaObj k Y).X i)
        (Y := ((X.linearYonedaObj k Y).extend e.op).X i')
        ((X.linearYonedaObj k Y).extendXIso e.op h).inv ((X.extendXIso e h).inv ≫ g) := by
  rw [linearYonedaObjExtendIso_hom_f Y X e h]
  rfl

/-- In a degree `e.f i`, the inverse of `linearYonedaObjExtendIso` is the identity of the module of
morphisms `X.X i ⟶ Y`, up to the identifications `HomologicalComplex.extendXIso` of the terms of
both extensions. -/
lemma linearYonedaObjExtendIso_inv_f (X : ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down β)) {i : α} {i' : β} (h : e.f i = i') :
    (linearYonedaObjExtendIso Y X e).inv.f i' =
      ((X.linearYonedaObj k Y).extendXIso e.op h).hom ≫
        ((linearYoneda k C).obj Y).map (X.extendXIso e h).hom.op := by
  refine Iso.inv_ext (f := HomologicalComplex.Hom.isoApp (linearYonedaObjExtendIso Y X e) i') ?_
  ext (g : (X.extend e).X i' ⟶ Y)
  -- `g` goes to `(X.extendXIso e h).inv ≫ g` and back to `g`
  change ConcreteCategory.hom (((linearYoneda k C).obj Y).map (X.extendXIso e h).hom.op)
      (ConcreteCategory.hom ((X.linearYonedaObj k Y).extendXIso e.op h).hom
        (ConcreteCategory.hom ((linearYonedaObjExtendIso Y X e).hom.f i') g)) = g
  rw [linearYonedaObjExtendIso_hom_f_hom_apply Y X e h g]
  exact (congrArg (ConcreteCategory.hom (((linearYoneda k C).obj Y).map (X.extendXIso e h).hom.op))
    (Iso.inv_hom_id_apply (C := ModuleCat k) ((X.linearYonedaObj k Y).extendXIso e.op h)
      ((X.extendXIso e h).inv ≫ g : X.X i ⟶ Y))).trans (Iso.hom_inv_id_assoc _ g)

/-- **Naturality of `linearYonedaObjExtendIso` in the chain complex.** For a chain map
`φ : X ⟶ X'`, precomposition with the extension of `φ` corresponds to the extension of
precomposition with `φ`. -/
@[reassoc]
lemma linearYonedaObjExtendIso_hom_naturality {X X' : ChainComplex C α} (φ : X ⟶ X')
    (e : (ComplexShape.down α).Embedding (ComplexShape.down β)) :
    (TauCeti.ChainComplex.linearYonedaFunctor k Y).map (HomologicalComplex.extendMap φ e).op ≫
        (linearYonedaObjExtendIso Y X e).hom =
      (linearYonedaObjExtendIso Y X' e).hom ≫
        HomologicalComplex.extendMap ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op)
          e.op := by
  ext i' : 1
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    ext (g : (X'.extend e).X i' ⟶ Y)
    -- by definition, the components of `Hom(-, Y)` of a chain map are precomposition
    change ConcreteCategory.hom ((linearYonedaObjExtendIso Y X e).hom.f i')
        ((HomologicalComplex.extendMap φ e).f i' ≫ g) =
      ConcreteCategory.hom ((HomologicalComplex.extendMap
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) e.op).f i')
        (ConcreteCategory.hom ((linearYonedaObjExtendIso Y X' e).hom.f i') g)
    rw [linearYonedaObjExtendIso_hom_f_hom_apply Y X e hi,
      linearYonedaObjExtendIso_hom_f_hom_apply Y X' e hi, HomologicalComplex.extendMap_f _ e.op hi,
      HomologicalComplex.extendMap_f _ e hi]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    -- on the right, the identifications of `Hom(X', Y)` cancel, and precomposition with `φ` remains
    exact congrArg (ConcreteCategory.hom ((X.linearYonedaObj k Y).extendXIso e.op hi).inv)
      (congrArg
        (ConcreteCategory.hom (((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op).f i))
        (Iso.inv_hom_id_apply (C := ModuleCat k) ((X'.linearYonedaObj k Y).extendXIso e.op hi)
          ((X'.extendXIso e hi).inv ≫ g : X'.X i ⟶ Y))).symm
  · exact (HomologicalComplex.isZero_extend_X (X.linearYonedaObj k Y) e.op i'
      fun i h ↦ hi ⟨i, h⟩).eq_of_tgt _ _

/-- **Cohomology of morphisms out of a shifted chain complex.** If a chain complex `X` indexed by
`ℕ` is placed `n` degrees higher, the cohomology in degree `q + n` of the complex of morphisms
from it into `Y` is the cohomology in degree `q` of the complex of morphisms from `X` into `Y`. -/
def linearYonedaObjExtendHomologyIso (X : ChainComplex C ℕ) (n q : ℕ) :
    (ChainComplex.linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd n)) k Y).homology
      (q + n) ≅
      (X.linearYonedaObj k Y).homology q :=
  (HomologicalComplex.homologyFunctor _ _ (q + n)).mapIso
      (linearYonedaObjExtendIso Y X (ComplexShape.embeddingDownNatAdd n)) ≪≫
    (X.linearYonedaObj k Y).extendHomologyIso (ComplexShape.embeddingDownNatAdd n).op
      (j := q) (ComplexShape.embeddingDownNatAdd_f n q)

/-- `linearYonedaObjExtendHomologyIso` is the map in cohomology of `linearYonedaObjExtendIso`,
followed by Mathlib's identification `HomologicalComplex.extendHomologyIso` of the cohomology of an
extension. -/
lemma linearYonedaObjExtendHomologyIso_hom (X : ChainComplex C ℕ) (n q : ℕ) :
    (linearYonedaObjExtendHomologyIso (k := k) Y X n q).hom =
      HomologicalComplex.homologyMap
          (linearYonedaObjExtendIso Y X (ComplexShape.embeddingDownNatAdd n)).hom (q + n) ≫
        ((X.linearYonedaObj k Y).extendHomologyIso (ComplexShape.embeddingDownNatAdd n).op
          (j := q) (ComplexShape.embeddingDownNatAdd_f n q)).hom := (rfl)

/-- **Naturality of `linearYonedaObjExtendHomologyIso` in the chain complex.** For a chain map
`φ : X ⟶ X'`, the map in cohomology of precomposition with the shifted `φ` corresponds to the map
in cohomology of precomposition with `φ`. -/
@[reassoc]
lemma linearYonedaObjExtendHomologyIso_hom_naturality {X X' : ChainComplex C ℕ} (φ : X ⟶ X')
    (n q : ℕ) :
    HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
        (HomologicalComplex.extendMap φ (ComplexShape.embeddingDownNatAdd n)).op) (q + n) ≫
        (linearYonedaObjExtendHomologyIso Y X n q).hom =
      (linearYonedaObjExtendHomologyIso Y X' n q).hom ≫
        HomologicalComplex.homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op)
          q := by
  -- the map in cohomology of `linearYonedaObjExtendIso_hom_naturality`
  have h := (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · (q + n))
      (linearYonedaObjExtendIso_hom_naturality (k := k) Y φ
        (ComplexShape.embeddingDownNatAdd n))).trans (HomologicalComplex.homologyMap_comp _ _ _))
  rw [linearYonedaObjExtendHomologyIso_hom, linearYonedaObjExtendHomologyIso_hom]
  -- followed by the naturality of Mathlib's `extendHomologyIso`
  exact (Category.assoc _ _ _).symm.trans ((h =≫ _).trans ((Category.assoc _ _ _).trans
    (_ ≫= HomologicalComplex.extendHomologyIso_hom_naturality _ _ _)))

end ChainComplex
