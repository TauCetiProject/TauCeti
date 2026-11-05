/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex
public import TauCeti.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Weakly contractible simplicial sets

A simplicial set `K` is *weakly contractible* (`SSet.IsWeaklyContractible`) when, for every Kan
complex `Z`, the inclusion `SSet.constMaps K Z : Z ⟶ Fun(K, Z)` of the constant maps into the
internal hom is a simplicial homotopy equivalence. This is the mapping-space formulation used to
define final maps of quasicategories: a map `K ⟶ L` is final when its fibre products with the
coslices of `L` are weakly contractible.

A simplicial set with a homotopy from a constant map to its identity, such as a standard simplex
(`SSet.stdSimplex.contraction`), is weakly contractible: evaluation at the vertex is a homotopy
inverse. Conversely, a weakly contractible simplicial set is nonempty, since `Fun(K, Z)` has a
vertex when `K` is empty, while the empty simplicial set is a Kan complex without vertices. Every
map from it to a Kan complex is homotopic to a constant map, and testing this against its map to
the discrete simplicial set on its connected components shows that it is connected.

Weak contractibility is equivalent to `K ⟶ Δ[0]` being a weak homotopy equivalence in the
mapping-space sense of Kerodon (`SSet.isWeaklyContractible_iff_isWeakHomotopyEquivalence` in
`TauCeti/AlgebraicTopology/SimplicialSet/WeakHomotopyEquivalence.lean`). The comparison with the
realization-based weak equivalences of
`TauCeti/AlgebraicTopology/SimplicialSet/WeakEquivalence.lean` needs the homotopy theory of the
Kan–Quillen model structure and is not proved here.

## Main declarations

* `SSet.constMaps K Z`: the constant maps `Z ⟶ Fun(K, Z)`, and `SSet.evalAt x Z`, evaluation at a
  vertex `x`, which is a retraction of it (`SSet.constMaps_evalAt`); `SSet.curry_evalAt`
  evaluates curried maps, and `SSet.ihomObj₀Equiv_constMaps_app` identifies the vertices of the
  constant maps.
* `SSet.IsWeaklyContractible`: weakly contractible simplicial sets.
* `SSet.IsWeaklyContractible.of_homotopy`: contractible simplicial sets are weakly contractible;
  in particular every standard simplex `Δ[n]` is.
* `SSet.IsWeaklyContractible.of_iso`: invariance under isomorphism.
* `SSet.IsWeaklyContractible.nonempty`: the empty simplicial set is not weakly contractible.
* `SSet.IsWeaklyContractible.exists_homotopy_const`: maps to Kan complexes are homotopic to
  constant maps.
* `SSet.IsWeaklyContractible.isConnected`: weakly contractible simplicial sets are connected.

## References

* J. Lurie, *Higher Topos Theory*, Definition 4.1.1.1 and Proposition 4.1.1.3.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Opposite

open scoped Simplicial

universe u

namespace SSet

variable (K : SSet.{u})

/-- The inclusion `Z ⟶ Fun(K, Z)` of the constant maps, adjoint to the projection
`K ⊗ Z ⟶ Z`. -/
noncomputable def constMaps (Z : SSet.{u}) : Z ⟶ (ihom K).obj Z :=
  curry (snd K Z)

variable {K} in
/-- Evaluation `Fun(K, Z) ⟶ Z` at a vertex `x` of `K`. -/
noncomputable def evalAt (x : K _⦋0⦌) (Z : SSet.{u}) : (ihom K).obj Z ⟶ Z :=
  lift (const x) (𝟙 _) ≫ (ihom.ev K).app Z

variable {K} in
/-- Evaluation at `x` evaluates `Fun(K, Z)` on the constant map at `x`. -/
lemma evalAt_eq (x : K _⦋0⦌) (Z : SSet.{u}) :
    evalAt x Z = lift (const x) (𝟙 _) ≫ (ihom.ev K).app Z :=
  (rfl)

variable {K} in
/-- Evaluating a curried map at a vertex `x` of `K` restricts it to `x` on the first factor. -/
@[reassoc (attr := simp)]
lemma curry_evalAt {Y Z : SSet.{u}} (x : K _⦋0⦌) (f : K ⊗ Y ⟶ Z) :
    curry f ≫ evalAt x Z = lift (const x) (𝟙 Y) ≫ f := by
  simpa [evalAt, comp_lift_assoc] using lift_curry_ihom_ev_app (const x) (𝟙 Y) f

/-- Evaluating a constant map at a vertex returns its value. -/
@[reassoc (attr := simp)]
lemma constMaps_evalAt (x : K _⦋0⦌) (Z : SSet.{u}) : constMaps K Z ≫ evalAt x Z = 𝟙 Z := by
  simp [constMaps]

/-- The vertex of `Fun(K, Z)` given by the constant maps at a vertex `z` of `Z` corresponds to
the constant map `K ⟶ Z` at `z`. -/
@[simp]
lemma ihomObj₀Equiv_constMaps_app {Z : SSet.{u}} (z : Z _⦋0⦌) :
    ihomObj₀Equiv K Z ((constMaps K Z).app _ z) = const z := by
  rw [ihomObj₀Equiv_apply, ← const_comp, constMaps, lift_curry_ihom_ev_app, lift_snd]

/-- Precomposition with a map `f : K ⟶ L` sends constant maps out of `L` to constant maps out
of `K`. -/
@[reassoc (attr := simp)]
lemma constMaps_pre {L : SSet.{u}} (f : K ⟶ L) (Z : SSet.{u}) :
    constMaps L Z ≫ (pre f).app Z = constMaps K Z := by
  rw [constMaps, constMaps, curry_pre_app, whiskerRight_snd]

/-- A simplicial set `K` is *weakly contractible* when, for every Kan complex `Z`, the inclusion
of the constant maps `Z ⟶ Fun(K, Z)` is a simplicial homotopy equivalence. -/
class IsWeaklyContractible : Prop where
  exists_homotopyInverse (Z : SSet.{u}) [KanComplex Z] :
    ∃ g : (ihom K).obj Z ⟶ Z, Nonempty (Homotopy (constMaps K Z ≫ g) (𝟙 Z)) ∧
      Nonempty (Homotopy (g ≫ constMaps K Z) (𝟙 _))

variable {K}

/-- Evaluating at `x` and then taking the constant map is adjoint to evaluation at `x` on the
second factor of `K ⊗ Fun(K, Z)`. -/
lemma evalAt_constMaps (x : K _⦋0⦌) (Z : SSet.{u}) :
    evalAt x Z ≫ constMaps K Z = curry (snd K _ ≫ evalAt x Z) := by
  rw [constMaps, ← curry_natural_left, whiskerLeft_snd]

section

variable (h : K ⊗ Δ[1] ⟶ K) (Z : SSet.{u})

/-- The map `Fun(K, Z) ⊗ Δ[1] ⟶ Fun(K, Z)` precomposing with a map `h : K ⊗ Δ[1] ⟶ K`. -/
private noncomputable def contractingMap : (ihom K).obj Z ⊗ Δ[1] ⟶ (ihom K).obj Z :=
  curry (lift (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ h) (snd _ _ ≫ fst _ _) ≫ (ihom.ev K).app Z)

/-- Over a vertex `i` of `Δ[1]`, `contractingMap h Z` precomposes with the restriction of `h`
to `i`. -/
private lemma lift_const_contractingMap (i : Δ[1] _⦋0⦌) :
    lift (𝟙 _) (const i) ≫ contractingMap h Z =
      curry (lift (fst _ _ ≫ lift (𝟙 K) (const i) ≫ h) (snd _ _) ≫ (ihom.ev K).app Z) := by
  have hi : K ◁ lift (𝟙 ((ihom K).obj Z)) (const i) ≫ lift (fst _ _) (snd _ _ ≫ snd _ _) =
      fst _ _ ≫ lift (𝟙 K) (const i) := by
    ext : 1 <;> simp
  rw [contractingMap, ← curry_natural_left]
  simp [comp_lift_assoc, reassoc_of% hi]

private lemma ι₀_contractingMap {x : K _⦋0⦌} (h₀ : ι₀ ≫ h = const x) :
    ι₀ ≫ contractingMap h Z = evalAt x Z ≫ constMaps K Z := by
  rw [ι₀, lift_const_contractingMap, ← ι₀, h₀, evalAt_constMaps, evalAt, comp_lift_assoc]
  simp

private lemma ι₁_contractingMap (h₁ : ι₁ ≫ h = 𝟙 K) : ι₁ ≫ contractingMap h Z = 𝟙 _ := by
  rw [ι₁, lift_const_contractingMap, ← ι₁, h₁]
  simp [← uncurry_id_eq_ev]

end

/-- A homotopy from a constant map to the identity of `K` contracts the mapping spaces out of `K`
onto their values at the vertex. -/
noncomputable def homotopyEvalAtConstMaps {x : K _⦋0⦌} (H : Homotopy (const x) (𝟙 K))
    (Z : SSet.{u}) : Homotopy (evalAt x Z ≫ constMaps K Z) (𝟙 _) where
  h := contractingMap H.h Z
  h₀ := ι₀_contractingMap H.h Z H.h₀
  h₁ := ι₁_contractingMap H.h Z H.h₁
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

namespace IsWeaklyContractible

/-- A simplicial set with a homotopy from a constant map to its identity is weakly
contractible. -/
lemma of_homotopy {x : K _⦋0⦌} (H : Homotopy (const x) (𝟙 K)) : IsWeaklyContractible K where
  exists_homotopyInverse Z _ :=
    ⟨evalAt x Z, ⟨.ofEq (congrArg _ (constMaps_evalAt K x Z))⟩, ⟨homotopyEvalAtConstMaps H Z⟩⟩

instance (n : ℕ) : IsWeaklyContractible Δ[n] :=
  of_homotopy (stdSimplex.contraction n)

/-- Weak contractibility is invariant under isomorphism. -/
lemma of_iso {L : SSet.{u}} (e : K ≅ L) [IsWeaklyContractible K] : IsWeaklyContractible L where
  exists_homotopyInverse Z _ := by
    obtain ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ := exists_homotopyInverse (K := K) Z
    have hPQ : (pre e.hom).app Z ≫ (pre e.inv).app Z = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id, NatTrans.id_app]
    have H := (H₂.precomp ((pre e.hom).app Z)).postcomp ((pre e.inv).app Z)
    rw [Category.assoc, Category.assoc, constMaps_pre, Category.comp_id, hPQ] at H
    exact ⟨(pre e.hom).app Z ≫ g, ⟨by rwa [constMaps_pre_assoc]⟩, ⟨H⟩⟩

variable [IsWeaklyContractible K]

/-- A weakly contractible simplicial set is nonempty: otherwise `Fun(K, ∅)` would be a point
admitting no map to the empty Kan complex. -/
lemma nonempty : K.Nonempty := by
  by_contra hK
  let E : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  have : KanComplex E := by
    rw [KanComplex.iff]
    intro n i f _
    exact ((f _ (i.succAbove_ne 0)).app _ (stdSimplex.obj₀Equiv.symm 0)).2.elim
  obtain ⟨g, -⟩ := exists_homotopyInverse (K := K) E
  exact ((curry (fst K Δ[0] ≫ (isInitialOfNotNonempty hK).to E) ≫ g).app _
    (stdSimplex.obj₀Equiv.symm 0)).2.elim

/-- Every map from a weakly contractible simplicial set to a Kan complex is homotopic to a
constant map. -/
lemma exists_homotopy_const {Z : SSet.{u}} [KanComplex Z] (f : K ⟶ Z) :
    ∃ z : Z _⦋0⦌, Nonempty (Homotopy (const z) f) := by
  obtain ⟨g, -, ⟨H⟩⟩ := exists_homotopyInverse (K := K) Z
  -- The homotopy `H` traces an edge of `Fun(K, Z)` from the constant maps at the value of `g` at
  -- the vertex `f` to that vertex, which is a homotopy from a constant map to `f`.
  let v := (ihomObj₀Equiv K Z).symm f
  refine ⟨g.app _ v, ⟨ihomEdgeEquiv _ _
    ((Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy v).ofEq ?_ rfl)⟩⟩
  rw [Equiv.eq_symm_apply, NatTrans.comp_app, types_comp_apply, ihomObj₀Equiv_constMaps_app]

/-- A weakly contractible simplicial set is connected. -/
instance isConnected : K.IsConnected where
  nonempty := nonempty
  allEq := π₀.rec fun x ↦ π₀.rec fun y ↦ by
    obtain ⟨z, ⟨H⟩⟩ := exists_homotopy_const (toπ₀ K)
    -- The homotopy induces equal maps on connected components, and the connected components of
    -- the discrete target are its vertices.
    suffices key : ∀ x : K _⦋0⦌, π₀.mk x = z from (key x).trans (key y).symm
    intro x
    have := congrArg (constπ₀Equiv _) (congrFun H.mapπ₀_eq (π₀.mk x))
    simpa [mapπ₀_mk, toπ₀_app_zero] using this.symm

end IsWeaklyContractible

end SSet
