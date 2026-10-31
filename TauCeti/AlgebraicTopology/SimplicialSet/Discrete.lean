/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Discrete simplicial sets

The discrete simplicial set on a type `ι` is the constant simplicial set
`(Functor.const SimplexCategoryᵒᵖ).obj ι`: its simplices in every dimension are the elements of
`ι`, and all its faces and degeneracies are identities. It is the free simplicial set on the
vertices `ι`: a map from it to a simplicial set `X` is a family `ι → X _⦋0⦌` of vertices
(`SSet.constHomEquiv`). Its only nondegenerate simplices are its vertices, so it has exactly as
many nondegenerate simplices as `ι` has elements (`SSet.constNEquiv`). Discrete simplicial sets are
therefore the test objects for statements about families of vertices that are phrased in terms of
the number of nondegenerate simplices, such as cardinal filteredness.

## Main declarations

* `SSet.constHomEquiv`: maps from the discrete simplicial set on `ι` are families of vertices.
* `SSet.constNEquiv`: the nondegenerate simplices of the discrete simplicial set on `ι` are the
  elements of `ι`.
* `SSet.kanComplex_const`: discrete simplicial sets are Kan complexes.
* `SSet.toπ₀`: the map from a simplicial set to the discrete simplicial set on its connected
  components.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable (ι : Type u) {X : SSet.{u}}

/-- Maps from the discrete simplicial set on `ι` to `X` are families of vertices of `X` indexed by
`ι`; the map attached to a family sends `i` in every dimension to the degenerate simplex on the
vertex at `i`. This is the adjunction between constant presheaves and evaluation at the terminal
object `⦋0⦌` of `SimplexCategory`. -/
noncomputable def constHomEquiv : ((Functor.const SimplexCategoryᵒᵖ).obj ι ⟶ X) ≃ (ι → X _⦋0⦌) :=
  ((constantPresheafAdj (Type u) SimplexCategory.isTerminalZero).homEquiv ι X).trans
    TypeCat.homEquiv

@[simp]
lemma constHomEquiv_apply (f : (Functor.const SimplexCategoryᵒᵖ).obj ι ⟶ X) (i : ι) :
    constHomEquiv ι f i = f.app (op ⦋0⦌) i :=
  (rfl)

/-- The map from the discrete simplicial set given by a family of vertices sends the vertex `i`
to the vertex at `i`. The source of the component is stated as `ι`, its simp-normal form. -/
@[simp]
lemma constHomEquiv_symm_app_zero (x : ι → X _⦋0⦌) (i : ι) :
    ConcreteCategory.hom (X := ι) (Y := X _⦋0⦌) (((constHomEquiv ι).symm x).app (op ⦋0⦌)) i =
      x i :=
  congrFun ((constHomEquiv ι).apply_symm_apply x) i

/-- Every simplex of positive dimension of a discrete simplicial set is degenerate. -/
@[simp]
lemma const_degenerate_succ (n : ℕ) :
    SSet.degenerate ((Functor.const SimplexCategoryᵒᵖ).obj ι) (n + 1) = Set.univ :=
  -- Faces and degeneracies of a discrete simplicial set are identities, so `i = σ₀ i`.
  Set.eq_univ_of_forall fun i ↦
    σ_mem_degenerate (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) (n := n) 0 i

/-- The nondegenerate simplices of the discrete simplicial set on `ι` are its vertices, the
elements of `ι`. -/
def constNEquiv : SSet.N ((Functor.const SimplexCategoryᵒᵖ).obj ι) ≃ ι where
  toFun s := s.simplex
  invFun i := N.mk (n := 0) i (by simp)
  left_inv s := by
    induction s with | mk n s
    obtain ⟨s, hs⟩ := s
    obtain _ | n := n
    · rfl
    · simp [nonDegenerate, const_degenerate_succ] at hs
  right_inv _ := rfl

/-- Discrete simplicial sets are Kan complexes: the faces of a horn in a discrete simplicial set
are all the same element, which is then a filler. -/
instance kanComplex_const : KanComplex ((Functor.const SimplexCategoryᵒᵖ).obj ι) := by
  rw [KanComplex.iff]
  intro n i f hf
  refine ⟨(yonedaEquiv (n := ⦋n + 1⦌)).symm (yonedaEquiv (f _ (i.succAbove_ne 0)) : ι),
    fun j hj ↦ yonedaEquiv.injective ?_⟩
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  -- The faces of a discrete simplicial set are identities, so faces of simplices are dropped by
  -- `change` here and in the compatibility conditions below.
  change yonedaEquiv (f _ (i.succAbove_ne 0)) = yonedaEquiv (f j hj)
  obtain _ | n := n
  · obtain rfl : j = i.succAbove 0 := by have := i.succAbove_ne 0; omega
    rfl
  · rw [horn.isCompatible_iff] at hf
    rcases lt_trichotomy (i.succAbove 0) j with h | h | h
    · have := congrArg yonedaEquiv (hf _ _ (i.succAbove_ne 0) hj h)
      rwa [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at this
    · subst h
      rfl
    · have := congrArg yonedaEquiv (hf _ _ hj (i.succAbove_ne 0) h)
      rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at this
      exact this.symm

variable (X) in
/-- The map from a simplicial set to the discrete simplicial set on its connected components,
sending a simplex to the component of its vertices. -/
noncomputable def toπ₀ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (π₀ X) where
  app n := ↾fun σ ↦ π₀.mk (X.map (⦋0⦌.const n.unop 0).op σ)
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ ⟨φ⟩
    ext σ
    -- `change` unfolds the components of `toπ₀` and the identity maps of a discrete simplicial
    -- set. All vertices of `σ` lie in one component, because `Δ[n]` is connected.
    change π₀.mk (X.map (⦋0⦌.const ⦋m⦌ 0).op (X.map φ.op σ)) =
      π₀.mk (X.map (⦋0⦌.const ⦋n⦌ 0).op σ)
    rw [← Functor.map_comp_apply, ← op_comp, ← yonedaEquiv_symm_app_objEquiv_symm,
      ← yonedaEquiv_symm_app_objEquiv_symm, ← mapπ₀_mk, ← mapπ₀_mk]
    exact congrArg _ (Subsingleton.elim _ _)

/-- The map to the discrete simplicial set on the connected components sends a simplex to the
component of its initial vertex. -/
lemma toπ₀_app {n : SimplexCategoryᵒᵖ} (σ : X.obj n) :
    (toπ₀ X).app n σ = π₀.mk (X.map (⦋0⦌.const n.unop 0).op σ) :=
  (rfl)

/-- The map to the discrete simplicial set on the connected components sends a vertex to its
component. -/
@[simp]
lemma toπ₀_app_zero (x : X _⦋0⦌) : dsimp% (toπ₀ X).app _ x = π₀.mk x := by
  rw [toπ₀_app, Subsingleton.elim (⦋0⦌.const ⦋0⦌ 0) (𝟙 _)]
  simp

end SSet
