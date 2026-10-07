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
complexes which is split in each degree to a short exact sequence of cochain complexes.  It also
records elementwise descriptions of the differential, cocycles, coboundaries and cohomology classes
of `Hom(X, Y)`, and of the maps between them induced by chain maps.

The functor `Hom(-, Y)` is only left exact, so the splitting hypothesis cannot be dropped.  It
holds for the singular chains of a pair of spaces, which is how the long exact sequence in
singular cohomology is obtained from the one of chain complexes.

## Main declarations

* `TauCeti.ChainComplex.linearYonedaFunctor`: the functor `X ↦ Hom(X, Y)` from chain complexes to
  cochain complexes of `k`-modules.
* `TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor`: `Hom(-, Y)` preserves short
  exactness of degreewise split sequences.
* `Homotopy.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy to a cochain homotopy.
* `TauCeti.HomotopyEquiv.linearYonedaFunctorMap`: `Hom(-, Y)` takes a chain homotopy
  equivalence to a cochain homotopy equivalence in the opposite direction.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] {α : Type*} [AddRightCancelSemigroup α] [One α]
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

/-- `Hom(-, Y)` takes a chain homotopy between two chain maps `φ, ψ : X ⟶ X'` to a cochain
homotopy between the two maps `Hom(X', Y) ⟶ Hom(X, Y)` obtained by precomposition. -/
noncomputable def _root_.Homotopy.linearYonedaFunctorMap {X X' : ChainComplex C α} {φ ψ : X ⟶ X'}
    (h : Homotopy φ ψ) :
    Homotopy ((linearYonedaFunctor k Y).map φ.op) ((linearYonedaFunctor k Y).map ψ.op) :=
  (((linearYoneda k C).obj Y).rightOp.mapHomotopy h).unop

/-- `Hom(-, Y)` takes a chain homotopy equivalence to a cochain homotopy equivalence in
the opposite direction, with maps given by precomposition. -/
noncomputable def _root_.TauCeti.HomotopyEquiv.linearYonedaFunctorMap
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
lemma _root_.TauCeti.HomotopyEquiv.linearYonedaFunctorMap_hom
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    (TauCeti.HomotopyEquiv.linearYonedaFunctorMap k Y h).hom =
      (linearYonedaFunctor k Y).map h.hom.op := (rfl)

/-- The inverse map of the induced homotopy equivalence is precomposition with `h.inv`. -/
@[simp]
lemma _root_.TauCeti.HomotopyEquiv.linearYonedaFunctorMap_inv
    {X X' : ChainComplex C α} (h : _root_.HomotopyEquiv X X') :
    (TauCeti.HomotopyEquiv.linearYonedaFunctorMap k Y h).inv =
      (linearYonedaFunctor k Y).map h.inv.op := (rfl)

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

end Abelian

end TauCeti.ChainComplex
