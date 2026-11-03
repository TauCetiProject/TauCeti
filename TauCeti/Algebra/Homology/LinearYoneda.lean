/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Morphisms from a chain complex into an object

For a chain complex `X` in a `k`-linear abelian category `C` and an object `Y : C`, Mathlib's
`ChainComplex.linearYonedaObj` is the cochain complex of `k`-modules which in degree `i` is the
module of morphisms `X.X i ⟶ Y`, with differential given by precomposition with the differential
of `X`.  This file makes the construction a contravariant functor of `X`, shows that it takes a
chain homotopy to a cochain homotopy, and shows that it takes a short exact sequence of chain
complexes which is split in each degree to a short exact sequence of cochain complexes.  It also
records elementwise descriptions of the differential, cocycles, coboundaries and cohomology classes
of `Hom(X, Y)`, and of the maps between them induced by chain maps. Postcomposition
with coefficient morphisms is provided by `ChainComplex.linearYonedaObjMap`; it commutes with the
maps induced by chain maps (`ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map`).
It makes `Hom(X, -)` a functor of the coefficient object (`ChainComplex.linearYonedaObjFunctor`),
which is exact when every term of `X` is projective: it takes short exact sequences of
coefficients to short exact sequences of cochain complexes. For singular chains this gives the long
exact cohomology sequence of a short exact sequence of coefficients.

It also sends coproducts of chain complexes to products of cochain complexes, with smallness
measured in the universe of morphisms of the coefficient category. This uses Mathlib's
`whiskering_linearYoneda` comparison with the Yoneda embedding (Kim Morrison) and the transfer
of limit preservation across opposite categories (Markus Himmel).

The functor and its action on homotopies require only a preadditive `k`-linear category.
Preservation of degreewise split short exact sequences additionally uses kernels,
cokernels and balancedness. The elementwise API uses Mathlib's
`ChainComplex.linearYonedaObj`, which is defined for abelian categories.

The functor `Hom(-, Y)` is only left exact, so the splitting hypothesis cannot be dropped.  It
holds for the singular chains of a pair of spaces, which is how the long exact sequence in
singular cohomology is obtained from the one of chain complexes.

## Main declarations

* `TauCeti.ChainComplex.linearYonedaFunctor`: the functor `X ↦ Hom(X, Y)` from chain complexes to
  cochain complexes of `k`-modules.
* `TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor`: `Hom(-, Y)` preserves short
  exactness of degreewise split sequences.
* `Homotopy.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy to a cochain homotopy.
* `HomotopyEquiv.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy
  equivalence to a cochain homotopy equivalence in the opposite direction.
* `ChainComplex.linearYonedaObjFunctor`: the functor `Y ↦ Hom(X, Y)` of the coefficients, with
  `ChainComplex.linearYonedaObjFunctorMap` the natural transformation induced by a chain map.
* `ChainComplex.shortExact_map_linearYonedaObjFunctor`: for `X` with projective terms, `Hom(X, -)`
  preserves short exact sequences.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti.ChainComplex

variable {C : Type u} [Category.{v} C] {α : Type*} [AddRightCancelSemigroup α] [One α]
  (k : Type*) [Ring k]

section Preadditive

variable [Preadditive C] [Linear k C] (Y : C)

/-- The contravariant functor sending a chain complex `X` to the cochain complex of `k`-modules
`Hom(X, Y)`, which in degree `i` is the module of morphisms `X.X i ⟶ Y`. -/
-- `@[expose]` is mandated by the module system: exported statements downstream (the singular
-- cochain maps, typed between `ChainComplex.linearYonedaObj` complexes) need
-- `(linearYonedaFunctor k Y).obj X` to unfold to `X.unop.linearYonedaObj k Y`, and an exported
-- statement may unfold only exposed definitions.
@[expose]
noncomputable def linearYonedaFunctor : (ChainComplex C α)ᵒᵖ ⥤ CochainComplex (ModuleCat k) α :=
  (((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
    HomologicalComplex.unopFunctor _ _

instance : (linearYonedaFunctor (α := α) k Y).Additive :=
  inferInstanceAs ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
    HomologicalComplex.unopFunctor _ _).Additive

/-- The contravariant chain-to-cochain functor `Hom(-, Y)` preserves products in the opposite
category of chain complexes, equivalently it sends coproducts of chains to products of cochains.
The index type is small in the universe of the morphisms of `C`. -/
instance linearYonedaFunctor_preservesLimitsOfShape_discrete {ι : Type w} [Small.{v} ι]
    [HasColimitsOfShape (Discrete ι) C] :
    PreservesLimitsOfShape (Discrete ι) (linearYonedaFunctor (α := α) k Y) := by
  let _ : PreservesLimitsOfShape (Discrete ι)ᵒᵖ ((linearYoneda k C).obj Y) := by
    have hforget : (linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k) = yoneda.obj Y :=
      Functor.congr_obj (whiskering_linearYoneda k C) Y
    let _ : PreservesLimitsOfShape (Discrete (Shrink.{v} ι))ᵒᵖ
        ((linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k)) :=
      hforget ▸ inferInstance
    -- The forgetful functor reflects limits of small shape. Shrinking the index type makes
    -- that reflection available without identifying the index and morphism universes.
    let _ : PreservesLimitsOfShape (Discrete (Shrink.{v} ι))ᵒᵖ ((linearYoneda k C).obj Y) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (forget (ModuleCat.{v} k))
    exact preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{v} ι)).symm.op _
  let _ : PreservesColimitsOfShape (Discrete ι) ((linearYoneda k C).obj Y).rightOp :=
    preservesColimitsOfShape_rightOp _ _
  let _ : PreservesColimitsOfShape (Discrete ι)
      (((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down α)) :=
    inferInstance
  let _ : PreservesLimitsOfShape (Discrete ι)
      (((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down α)).op :=
    preservesLimitsOfShape_op _ _
  exact inferInstanceAs (PreservesLimitsOfShape (Discrete ι)
    ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
      HomologicalComplex.unopFunctor _ _))

/-- `Hom(-, Y)` takes a chain homotopy between two chain maps `φ, ψ : X ⟶ X'` to a cochain
homotopy between the two maps `Hom(X', Y) ⟶ Hom(X, Y)` obtained by precomposition. -/
noncomputable def _root_.Homotopy.linearYonedaFunctorMap {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) :
    Homotopy ((linearYonedaFunctor k Y).map φ.op) ((linearYonedaFunctor k Y).map ψ.op) :=
  (((linearYoneda k C).obj Y).rightOp.mapHomotopy h).unop

/-- `Hom(-, Y)` takes a chain homotopy equivalence to a cochain homotopy equivalence in
the opposite direction, with maps given by precomposition. -/
noncomputable def _root_.HomotopyEquiv.linearYonedaFunctorMap
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    _root_.HomotopyEquiv ((linearYonedaFunctor k Y).obj (op X'))
      ((linearYonedaFunctor k Y).obj (op X)) where
  hom := (linearYonedaFunctor k Y).map h.hom.op
  inv := (linearYonedaFunctor k Y).map h.inv.op
  homotopyHomInvId := by
    simpa only [← Functor.map_comp, ← op_comp] using
      (h.homotopyInvHomId.linearYonedaFunctorMap k Y).trans
        (Homotopy.ofEq ((linearYonedaFunctor k Y).map_id _))
  homotopyInvHomId := by
    simpa only [← Functor.map_comp, ← op_comp] using
      (h.homotopyHomInvId.linearYonedaFunctorMap k Y).trans
        (Homotopy.ofEq ((linearYonedaFunctor k Y).map_id _))

/-- The forward map of the induced homotopy equivalence is precomposition with `h.hom`. -/
@[simp]
lemma _root_.HomotopyEquiv.linearYonedaFunctorMap_hom
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    (h.linearYonedaFunctorMap k Y).hom =
      (linearYonedaFunctor k Y).map h.hom.op := (rfl)

/-- The inverse map of the induced homotopy equivalence is precomposition with `h.inv`. -/
@[simp]
lemma _root_.HomotopyEquiv.linearYonedaFunctorMap_inv
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    (h.linearYonedaFunctorMap k Y).inv =
      (linearYonedaFunctor k Y).map h.inv.op := (rfl)

/-- The functor `Hom(-, Y)` takes a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of chain
complexes which is split in each degree to a short exact sequence
`0 ⟶ Hom(X₃, Y) ⟶ Hom(X₂, Y) ⟶ Hom(X₁, Y) ⟶ 0` of cochain complexes. -/
lemma shortExact_map_linearYonedaFunctor
    [HasKernels C] [HasCokernels C] [Balanced C] {S : ShortComplex (ChainComplex C α)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)] :
    (S.op.map (linearYonedaFunctor k Y)).ShortExact := by
  let := Preadditive.hasEqualizers_of_hasKernels (C := C)
  let := Preadditive.hasCoequalizers_of_hasCokernels (C := C)
  have := hS.exact.hasZeroObject
  have := hS.epi_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  let : (HomologicalComplex.eval C (ComplexShape.down α) i).PreservesHomology := {}
  have hi := hS.exact.map (HomologicalComplex.eval C _ i)
  have := hi.hasZeroObject
  exact ((ShortComplex.Splitting.ofExactOfRetraction _ hi (retraction (S.f.f i))
    (IsSplitMono.id (S.f.f i))
    (inferInstance : Epi ((HomologicalComplex.eval C _ i).map S.g))).op.map
      ((linearYoneda k C).obj Y)).shortExact

end Preadditive

section Abelian

variable [Abelian C] [Linear k C] (Y : C)

@[simp]
lemma linearYonedaFunctor_obj (X : (ChainComplex C α)ᵒᵖ) :
    (linearYonedaFunctor k Y).obj X = X.unop.linearYonedaObj k Y := rfl

/-- The map `Hom(X', Y) ⟶ Hom(X, Y)` induced by a chain map `X ⟶ X'` is precomposition. -/
@[simp]
lemma linearYonedaFunctor_map_f_hom_apply {X X' : (ChainComplex C α)ᵒᵖ} (φ : X ⟶ X') (i : α)
    (g : (X.unop.linearYonedaObj k Y).X i) :
    ConcreteCategory.hom (X := (X.unop.linearYonedaObj k Y).X i)
      (Y := (X'.unop.linearYonedaObj k Y).X i) (((linearYonedaFunctor k Y).map φ).f i) g =
        φ.unop.f i ≫ g := rfl

/-- The cochain homotopy induced by a chain homotopy `h` is precomposition with `h`. -/
@[simp]
lemma _root_.Homotopy.linearYonedaFunctorMap_hom_apply {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) (i j : α) (g : (X'.linearYonedaObj k Y).X i) :
    ConcreteCategory.hom (X := (X'.linearYonedaObj k Y).X i) (Y := (X.linearYonedaObj k Y).X j)
      ((h.linearYonedaFunctorMap k Y).hom i j) g = h.hom j i ≫ g := (rfl)

/-- Postcomposition with a coefficient morphism induces a map of cochain complexes
`Hom(X, Y) ⟶ Hom(X, Z)`. -/
noncomputable def _root_.ChainComplex.linearYonedaObjMap (X : ChainComplex C α)
    {Y Z : C} (g : Y ⟶ Z) : X.linearYonedaObj k Y ⟶ X.linearYonedaObj k Z :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda k C).map g).rightOp.mapHomologicalComplex _).app X).op

/-- The coefficient map on cochains is postcomposition. -/
@[simp↓]
lemma _root_.ChainComplex.linearYonedaObjMap_f_hom_apply (X : ChainComplex C α)
    {Y Z : C} (g : Y ⟶ Z) (i : α) (a : X.X i ⟶ Y) :
    (X.linearYonedaObjMap k g).f i a = a ≫ g := (rfl)

/-- Identity coefficient maps induce identity maps of cochain complexes. -/
@[simp]
lemma _root_.ChainComplex.linearYonedaObjMap_id (X : ChainComplex C α) (Y : C) :
    X.linearYonedaObjMap k (𝟙 Y) = 𝟙 (X.linearYonedaObj k Y) := by
  ext i (a : X.X i ⟶ Y)
  simp only [ChainComplex.linearYonedaObjMap_f_hom_apply, Category.comp_id]
  rfl

/-- Coefficient maps on cochain complexes preserve composition. -/
@[simp]
lemma _root_.ChainComplex.linearYonedaObjMap_comp (X : ChainComplex C α)
    {Y Z T : C} (g : Y ⟶ Z) (h : Z ⟶ T) :
    X.linearYonedaObjMap k (g ≫ h) = X.linearYonedaObjMap k g ≫ X.linearYonedaObjMap k h := by
  simp only [ChainComplex.linearYonedaObjMap, Functor.map_comp, NatTrans.rightOp_comp,
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, op_comp]
  rfl

/-- Coefficient maps commute with the maps induced by chain maps: postcomposing with `g : Y ⟶ Z`
and precomposing with `β : X ⟶ X'` can be done in either order. -/
@[reassoc]
lemma _root_.ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map {X X' : ChainComplex C α}
    (β : X ⟶ X') {Y Z : C} (g : Y ⟶ Z) :
    X'.linearYonedaObjMap k g ≫ (linearYonedaFunctor k Z).map β.op =
      (linearYonedaFunctor k Y).map β.op ≫ X.linearYonedaObjMap k g := by
  ext i (a : X'.X i ⟶ Y)
  -- Both components send `a` to `β ≫ a ≫ g`. They are precomposition and postcomposition by
  -- definition (`linearYonedaFunctor_map_f_hom_apply`, `linearYonedaObjMap_f_hom_apply`), but
  -- `simp` cannot split the composite: its components live in `X.linearYonedaObj k Z` and in
  -- `(linearYonedaFunctor k Z).obj (op X)`, which agree only by unfolding.
  exact (Category.assoc (β.f i) a g).symm

/-- The coefficient map sends the class of a cocycle to the class of its image. -/
@[simp]
lemma _root_.ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply
    (X : ChainComplex C α) {Y Z : C} (g : Y ⟶ Z) (i : α)
    (a : (X.linearYonedaObj k Y).cycles i) :
    HomologicalComplex.homologyMap (X.linearYonedaObjMap k g) i
        ((X.linearYonedaObj k Y).homologyπ i a) =
      (X.linearYonedaObj k Z).homologyπ i
        (HomologicalComplex.cyclesMap (X.linearYonedaObjMap k g) i a) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality _ i) a

/-- The coefficient map on cocycles is postcomposition. -/
@[simp↓]
lemma _root_.ChainComplex.iCycles_cyclesMap_linearYonedaObjMap_apply
    (X : ChainComplex C α) {Y Z : C} (g : Y ⟶ Z) (i : α)
    (a : (X.linearYonedaObj k Y).cycles i) :
    (X.linearYonedaObj k Z).iCycles i
        (HomologicalComplex.cyclesMap (X.linearYonedaObjMap k g) i a) =
      (X.linearYonedaObj k Y).iCycles i a ≫ g := by
  exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ i) a).trans
    (X.linearYonedaObjMap_f_hom_apply k g i _)

section Elementwise

variable {k Y} {X : ChainComplex C α}

/-- The differential of `Hom(X, Y)` is precomposition with the differential of `X`. -/
lemma linearYonedaObj_d_apply (i j : α) (g : (X.linearYonedaObj k Y).X i) :
    (X.linearYonedaObj k Y).d i j g = X.d j i ≫ g :=
  rfl

/-- A cocycle `a` of `Hom(X, Y)` vanishes on boundaries: `a ∘ d` is the zero of the module
`(X.linearYonedaObj k Y).X j`. -/
lemma d_comp_linearYonedaObj_iCycles (i j : α) (a : (X.linearYonedaObj k Y).cycles i) :
    X.d j i ≫ (X.linearYonedaObj k Y).iCycles i a = (0 : (X.linearYonedaObj k Y).X j) :=
  ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).iCycles_d i j) a

/-- The coboundary of a cochain `g` of `Hom(X, Y)` is `g ∘ d`. -/
lemma linearYonedaObj_iCycles_toCycles_apply (i j : α) (g : (X.linearYonedaObj k Y).X i) :
    (X.linearYonedaObj k Y).iCycles j ((X.linearYonedaObj k Y).toCycles i j g) = X.d j i ≫ g :=
  ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).toCycles_i i j) g

/-- A coboundary of `Hom(X, Y)` has zero cohomology class. -/
lemma linearYonedaObj_homologyπ_toCycles_apply (i j : α) (g : (X.linearYonedaObj k Y).X i) :
    (X.linearYonedaObj k Y).homologyπ j ((X.linearYonedaObj k Y).toCycles i j g) = 0 :=
  ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).toCycles_comp_homologyπ i j) g

/-- The map on cohomology `H(Hom(X, Y)) ⟶ H(Hom(X', Y))` induced by a chain map `f : X' ⟶ X`
sends the class of a cocycle to the class of its image in the cocycles of `Hom(X', Y)`. -/
lemma homologyMap_linearYonedaFunctor_map_homologyπ_apply {X' : ChainComplex C α} (f : X' ⟶ X)
    (i : α) (a : (X.linearYonedaObj k Y).cycles i) :
    HomologicalComplex.homologyMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
        ((linearYonedaFunctor k Y).map f.op) i ((X.linearYonedaObj k Y).homologyπ i a) =
      (X'.linearYonedaObj k Y).homologyπ i
        (HomologicalComplex.cyclesMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
          ((linearYonedaFunctor k Y).map f.op) i a) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality _ i) a

/-- The map on cocycles `Z(Hom(X, Y)) ⟶ Z(Hom(X', Y))` induced by a chain map `f : X' ⟶ X` is
precomposition with `f`. -/
lemma iCycles_cyclesMap_linearYonedaFunctor_map_apply {X' : ChainComplex C α} (f : X' ⟶ X)
    (i : α) (a : (X.linearYonedaObj k Y).cycles i) :
    (X'.linearYonedaObj k Y).iCycles i
        (HomologicalComplex.cyclesMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
          ((linearYonedaFunctor k Y).map f.op) i a) =
      f.f i ≫ (X.linearYonedaObj k Y).iCycles i a :=
  ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i _ i) a

end Elementwise

section CoefficientSequence

/-- For a chain complex `X`, the covariant functor `Y ↦ Hom(X, Y)` from the coefficient category to
cochain complexes of `k`-modules. Its action on morphisms is postcomposition. -/
-- `@[expose]` is mandated by the module system, as for `linearYonedaFunctor`: without it `map`
-- cannot be characterised at all, since `linearYonedaObjFunctorMap_app` and the `simps` lemmas only
-- typecheck once `obj` unfolds to `X.linearYonedaObj k Y`, and an exported statement may unfold
-- only exposed definitions. Downstream, the terms of `S.map (X.linearYonedaObjFunctor k)` must be
-- the singular cochain complexes with coefficients in the terms of `S`, for the same reason.
@[expose, simps]
noncomputable def _root_.ChainComplex.linearYonedaObjFunctor (X : ChainComplex C α) :
    C ⥤ CochainComplex (ModuleCat k) α where
  obj Y := X.linearYonedaObj k Y
  map g := X.linearYonedaObjMap k g
  map_id Y := X.linearYonedaObjMap_id k Y
  map_comp g h := X.linearYonedaObjMap_comp k g h

instance _root_.ChainComplex.linearYonedaObjFunctor_additive (X : ChainComplex C α) :
    (X.linearYonedaObjFunctor k).Additive where
  map_add {Y Z g h} := by
    ext i (a : X.X i ⟶ Y)
    -- The components of both sides send `a` to `a ≫ (g + h)` and `a ≫ g + a ≫ h`: the maps are
    -- postcomposition by definition (`linearYonedaObjMap_f_hom_apply`), and sums of cochain maps
    -- are computed degreewise and pointwise. `simp` cannot use the former, whose statement is
    -- typed in `X.linearYonedaObj k Y` rather than in the image of the functor.
    exact Preadditive.comp_add _ _ _ a g h

/-- A chain map `β : X ⟶ X'` induces, by precomposition, a natural transformation from
`Hom(X', -)` to `Hom(X, -)`. -/
noncomputable def _root_.ChainComplex.linearYonedaObjFunctorMap {X X' : ChainComplex C α}
    (β : X ⟶ X') : X'.linearYonedaObjFunctor k ⟶ X.linearYonedaObjFunctor k where
  app Y := (linearYonedaFunctor k Y).map β.op
  naturality _ _ g := X.linearYonedaObjMap_comp_linearYonedaFunctor_map k β g

@[simp]
lemma _root_.ChainComplex.linearYonedaObjFunctorMap_app {X X' : ChainComplex C α} (β : X ⟶ X')
    (Y : C) :
    (ChainComplex.linearYonedaObjFunctorMap k β).app Y = (linearYonedaFunctor k Y).map β.op :=
  (rfl)

/-- If every term of the chain complex `X` is projective, then `Hom(X, -)` takes a short exact
sequence `0 ⟶ Y₁ ⟶ Y₂ ⟶ Y₃ ⟶ 0` of coefficients to a short exact sequence of cochain complexes
`0 ⟶ Hom(X, Y₁) ⟶ Hom(X, Y₂) ⟶ Hom(X, Y₃) ⟶ 0`. -/
lemma _root_.ChainComplex.shortExact_map_linearYonedaObjFunctor (X : ChainComplex C α)
    [∀ i, Projective (X.X i)] {S : ShortComplex C} (hS : S.ShortExact) :
    (S.map (X.linearYonedaObjFunctor k)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro (a : X.X i ⟶ S.X₂) (ha : a ≫ S.g = 0)
    exact ⟨hS.exact.lift a ha, hS.exact.lift_f a ha⟩
  · rw [ModuleCat.mono_iff_injective]
    intro (a : X.X i ⟶ S.X₁) (b : X.X i ⟶ S.X₁) (h : a ≫ S.f = b ≫ S.f)
    exact (cancel_mono S.f).1 h
  · rw [ModuleCat.epi_iff_surjective]
    intro (a : X.X i ⟶ S.X₃)
    exact ⟨Projective.factorThru a S.g, Projective.factorThru_comp a S.g⟩

end CoefficientSequence

end Abelian

end TauCeti.ChainComplex
