/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Ext

/-!
# Morphisms from a chain complex into an object

For a chain complex `X` in a `k`-linear abelian category `C` and an object `Y : C`, Mathlib's
`ChainComplex.linearYonedaObj` is the cochain complex of `k`-modules which in degree `i` is the
module of morphisms `X.X i ⟶ Y`, with differential given by precomposition with the differential
of `X`.  This file makes the construction a contravariant functor of `X`, shows that it takes a
chain homotopy to a cochain homotopy, and shows that it takes a short exact sequence of chain
complexes which is split in each degree to a short exact sequence of cochain complexes.

The functor `Hom(-, Y)` is only left exact, so the splitting hypothesis cannot be dropped.  It
holds for the singular chains of a pair of spaces, which is how the long exact sequence in
singular cohomology is obtained from the one of chain complexes.

## Main declarations

* `TauCeti.ChainComplex.linearYonedaFunctor`: the functor `X ↦ Hom(X, Y)` from chain complexes to
  cochain complexes of `k`-modules.
* `TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor`: `Hom(-, Y)` preserves short
  exactness of degreewise split sequences.
* `Homotopy.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy to a cochain homotopy.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {α : Type*} [AddRightCancelSemigroup α] [One α]
  (k : Type*) [Ring k] [Linear k C] (Y : C)

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

instance : (linearYonedaFunctor (α := α) k Y).Additive :=
  inferInstanceAs ((((linearYoneda k C).obj Y).rightOp.mapHomologicalComplex _).op ⋙
    HomologicalComplex.unopFunctor _ _).Additive

/-- `Hom(-, Y)` takes a chain homotopy between two chain maps `φ, ψ : X ⟶ X'` to a cochain
homotopy between the two maps `Hom(X', Y) ⟶ Hom(X, Y)` obtained by precomposition. -/
-- `@[expose]` is mandated by the module system: the characteristic lemma
-- `Homotopy.linearYonedaFunctorMap_hom_apply` below reads off the components of this homotopy,
-- and an exported statement may unfold only exposed definitions.
@[expose]
noncomputable def _root_.Homotopy.linearYonedaFunctorMap {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) :
    Homotopy ((linearYonedaFunctor k Y).map φ.op) ((linearYonedaFunctor k Y).map ψ.op) :=
  (((linearYoneda k C).obj Y).rightOp.mapHomotopy h).unop

/-- The cochain homotopy induced by a chain homotopy `h` is precomposition with `h`. -/
@[simp]
lemma _root_.Homotopy.linearYonedaFunctorMap_hom_apply {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) (i j : α) (g : (X'.linearYonedaObj k Y).X i) :
    ConcreteCategory.hom ((h.linearYonedaFunctorMap k Y).hom i j) g = h.hom j i ≫ g := rfl

/-- The functor `Hom(-, Y)` takes a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of chain
complexes which is split in each degree to a short exact sequence
`0 ⟶ Hom(X₃, Y) ⟶ Hom(X₂, Y) ⟶ Hom(X₁, Y) ⟶ 0` of cochain complexes. -/
lemma shortExact_map_linearYonedaFunctor {S : ShortComplex (ChainComplex C α)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)] :
    (S.op.map (linearYonedaFunctor k Y)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  have hi := hS.map_of_exact (HomologicalComplex.eval C _ i)
  exact ((ShortComplex.Splitting.ofExactOfRetraction _ hi.exact (retraction (S.f.f i))
    (IsSplitMono.id (S.f.f i)) hi.epi_g).op.map ((linearYoneda k C).obj Y)).shortExact

end TauCeti.ChainComplex
