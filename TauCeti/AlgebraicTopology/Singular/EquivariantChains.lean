/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Invariant relative chains of a pair of `G`-spaces with coefficients in a `G`-object

Let a monoid `G` act on a topological pair `(X, A)`, as a functor `P : SingleObj G ⥤ TopPair`
(for instance `TopPair.ofSubsetActionFunctor`), and on a coefficient object `L` of a preadditive
category `C` with coproducts, as a functor `L : SingleObj G ⥤ C`. The relative singular chains
`C(X, A; L)` then carry the *diagonal* action of `G`: an element `g` acts on a chain `σ ⊗ ℓ`, a
singular simplex `σ` of `X` with coefficient `ℓ ∈ L`, by `(g ∘ σ) ⊗ (g ℓ)`. This is the functor
`TopPair.diagonalChainAction L P : SingleObj G ⥤ ChainComplex C ℕ`, the relative singular chain
bifunctor `TopPair.singularChainComplexFunctor C` evaluated on the pairing `L.prod' P` of the two
actions. The two actions commute because
the chain bifunctor is natural in both variables.

Its limit is the complex of `G`-invariant relative chains `C(X, A; L)^G`, and an equivariant map
of pairs, a natural transformation `τ : P ⟶ P'`, induces an equivariant chain map
(`TopPair.diagonalChainActionMap L τ`), functorially (`TopPair.diagonalChainActionFunctor L`),
hence a chain map of invariants `lim.map (TopPair.diagonalChainActionMap L τ)`.

With `L` the dual orientation line of an obstruction representation, these invariant chains on the
deformation spaces of an implicit atlas are the partial virtual complexes of Pardon's construction
of virtual fundamental classes (`TauCeti.Topology.ImplicitAtlas.PartialComplex.Basic`).

## Main definitions

* `TopPair.diagonalChainAction L P`: the diagonal action of `G` on the relative singular chains of
  `P` with coefficients in `L`.
* `TopPair.diagonalChainActionMap L τ`: the equivariant chain map induced by an equivariant map
  `τ : P ⟶ P'` of pairs.
* `TopPair.diagonalChainActionFunctor L`: the two together, as a functor of the action on the pair.

## Main results

* `TopPair.diagonalChainActionMap_app_comp_eqToHom`: on the underlying relative chain complexes,
  the induced chain map is the chain map of the map of pairs.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.2.5 (invariant
  relative chains with coefficients in the dual orientation line).
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] {G : Type*}
  [Monoid G] (L : SingleObj G ⥤ C)

-- The body is exposed so that the values and maps of the action are definitionally the relative
-- chain complexes and the chain maps of the bifunctor: the statements of
-- `diagonalChainAction_map` and `diagonalChainActionMap_app`, maps between values, typecheck only
-- then.
/-- **The diagonal action on relative chains.** For an action `P` of a monoid `G` on a topological
pair `(X, A)` and an action `L` of `G` on a coefficient object, `g` acts on the relative singular
chains `C(X, A; L)` by the map induced by `g` on the pair together with the action of `g` on the
coefficients. -/
@[expose]
def diagonalChainAction (P : SingleObj G ⥤ TopPair.{w}) : SingleObj G ⥤ ChainComplex C ℕ :=
  L.prod' P ⋙ Functor.uncurry.obj (singularChainComplexFunctor C)

variable (P : SingleObj G ⥤ TopPair.{w})

/-- The underlying complex of the diagonal action is the relative singular chain complex of the
pair with coefficients in `L`. -/
@[simp]
lemma diagonalChainAction_obj (Y : SingleObj G) :
    (diagonalChainAction L P).obj Y =
      ((singularChainComplexFunctor C).obj (L.obj Y)).obj (P.obj Y) :=
  (rfl)

/-- An element of `G` acts on relative chains by its action on the coefficients, followed by the
map induced by its action on the pair. -/
lemma diagonalChainAction_map {Y Y' : SingleObj G} (g : Y ⟶ Y') :
    (diagonalChainAction L P).map g =
      ((singularChainComplexFunctor C).map (L.map g)).app (P.obj Y) ≫
        ((singularChainComplexFunctor C).obj (L.obj Y')).map (P.map g) :=
  (rfl)

variable {P} {P' P'' : SingleObj G ⥤ TopPair.{w}}

/-- **Equivariant maps of pairs induce equivariant chain maps.** A natural transformation
`τ : P ⟶ P'`, a map of pairs commuting with the two actions of `G`, induces a map of the diagonal
actions on relative chains, by the chain map of `τ` with the identity on coefficients. -/
def diagonalChainActionMap (τ : P ⟶ P') : diagonalChainAction L P ⟶ diagonalChainAction L P' :=
  Functor.whiskerRight (NatTrans.prod' (𝟙 L) τ)
    (Functor.uncurry.obj (singularChainComplexFunctor C))

/-- The component of the chain map induced by an equivariant map of pairs is the chain map of the
map of pairs. -/
@[simp]
lemma diagonalChainActionMap_app (τ : P ⟶ P') (Y : SingleObj G) :
    (diagonalChainActionMap L τ).app Y =
      ((singularChainComplexFunctor C).obj (L.obj Y)).map (τ.app Y) := by
  -- By `Functor.uncurry`, the component is the identity on coefficients followed by `τ.app Y`.
  change ((singularChainComplexFunctor C).map (𝟙 (L.obj Y))).app (P.obj Y) ≫
    ((singularChainComplexFunctor C).obj (L.obj Y)).map (τ.app Y) = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- Read in the relative singular chain complexes, the component of the chain map induced by an
equivariant map of pairs is the chain map `TopPair.singularChainComplexMap` of the map of pairs. -/
@[reassoc]
lemma diagonalChainActionMap_app_comp_eqToHom (τ : P ⟶ P') (Y : SingleObj G) :
    (diagonalChainActionMap L τ).app Y ≫
        eqToHom (singularChainComplexFunctor_obj_obj (C := C) (P'.obj Y) (L.obj Y)) =
      eqToHom (singularChainComplexFunctor_obj_obj (C := C) (P.obj Y) (L.obj Y)) ≫
        singularChainComplexMap (τ.app Y) (L.obj Y) := by
  rw [diagonalChainActionMap_app]
  exact singularChainComplexFunctor_obj_map_comp_eqToHom _ _

@[simp]
lemma diagonalChainActionMap_id : diagonalChainActionMap L (𝟙 P) = 𝟙 _ := by
  ext Y : 2
  rw [diagonalChainActionMap_app, NatTrans.id_app]
  exact ((singularChainComplexFunctor C).obj (L.obj Y)).map_id (P.obj Y)

@[simp, reassoc]
lemma diagonalChainActionMap_comp (τ : P ⟶ P') (τ' : P' ⟶ P'') :
    diagonalChainActionMap L (τ ≫ τ') =
      diagonalChainActionMap L τ ≫ diagonalChainActionMap L τ' := by
  ext Y : 2
  simp only [NatTrans.comp_app, diagonalChainActionMap_app]
  exact Functor.map_comp _ _ _

/-- **The diagonal action on relative chains, as a functor of the action on the pair**: an action
`P` of `G` on a pair goes to the diagonal action `diagonalChainAction L P` on its relative chains,
and an equivariant map `τ` of pairs to the equivariant chain map `diagonalChainActionMap L τ`. -/
-- The body is exposed so that its values and maps are definitionally the diagonal actions and the
-- equivariant chain maps (`diagonalChainActionFunctor_obj`, `diagonalChainActionFunctor_map`).
@[expose, simps]
def diagonalChainActionFunctor :
    (SingleObj G ⥤ TopPair.{w}) ⥤ (SingleObj G ⥤ ChainComplex C ℕ) where
  obj := diagonalChainAction L
  map := diagonalChainActionMap L

end TopPair
