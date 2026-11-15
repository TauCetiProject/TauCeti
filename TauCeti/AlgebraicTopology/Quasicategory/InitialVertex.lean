/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.TerminalVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.Op

/-!
# Initial vertices of simplicial sets

A vertex `x` of a simplicial set `X` is initial (`SSet.IsInitialVertex`) if it is a terminal vertex
of the opposite simplicial set `Xᵒᵖ` (`SSet.IsTerminalVertex`), which reverses the order of the
vertices of every simplex. This is the definition of an initial object of a quasicategory in
Higher Topos Theory, and colimits of diagrams in a quasicategory are the initial vertices of its
coslices.

Equivalently, every simplex boundary whose first vertex is `x` extends to a simplex
(`SSet.isInitialVertex_iff`). This criterion uses reversal of simplex boundaries.

Through the identification of the edges and `2`-simplices of `Xᵒᵖ` with those of `X`
(`SSet.Edge.opEquiv`, `SSet.Edge.CompStruct.opEquiv`), the properties of terminal vertices give
an edge from an initial vertex to every vertex (`SSet.IsInitialVertex.nonempty_edge`), a
`2`-simplex filling every triangle starting at an initial vertex
(`SSet.IsInitialVertex.nonempty_compStruct`), and inverses of the edges between initial vertices
(`SSet.IsInitialVertex.nonempty_invStruct`), so that initial vertices are unique up to
equivalence. Conversely, terminal vertices of `X` are the initial vertices of `Xᵒᵖ`
(`SSet.isInitialVertex_op_iff`). Since the nerve of `Cᵒᵖ` is the opposite of the nerve of `C`
(`CategoryTheory.nerve.opIso`), a vertex of the nerve of a category is initial exactly when it is
an initial object (`CategoryTheory.nerve.isInitialVertex_iff`), and the first vertex of `Δ[n]` is
initial (`SSet.stdSimplex.isInitialVertex_zero`).

## References

* J. Lurie, *Higher Topos Theory*, §1.2.12 (initial and final objects).
-/

public section

universe v u

open CategoryTheory Limits Opposite Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- A vertex `x` of a simplicial set `X` is *initial* if it is a terminal vertex
(`SSet.IsTerminalVertex`) of the opposite simplicial set `Xᵒᵖ`, which reverses the order of the
vertices of every simplex. -/
def IsInitialVertex (x : X _⦋0⦌) : Prop :=
  X.op.IsTerminalVertex (X.opObjEquiv.symm x)

lemma isInitialVertex_iff_isTerminalVertex_op (x : X _⦋0⦌) :
    X.IsInitialVertex x ↔ X.op.IsTerminalVertex (X.opObjEquiv.symm x) :=
  Iff.rfl

/-- The terminal vertices of a simplicial set `X` are the initial vertices of `Xᵒᵖ`. -/
lemma isInitialVertex_op_iff (x : X _⦋0⦌) :
    X.op.IsInitialVertex (X.opObjEquiv.symm x) ↔ X.IsTerminalVertex x :=
  isTerminalVertex_iff_of_iso (opFunctorCompOpFunctorIso.app X).symm x

/-- A vertex is initial exactly when every simplex boundary starting at that vertex extends
across the simplex. The condition uses the first vertex of the boundary. -/
lemma isInitialVertex_iff (x : X _⦋0⦌) :
    X.IsInitialVertex x ↔ ∀ ⦃n : ℕ⦄ (σ₀ : (∂Δ[n + 1] : SSet) ⟶ X),
      σ₀.app _ (boundary.vertex n 0) = x →
        ∃ σ : Δ[n + 1] ⟶ X, σ₀ = ∂Δ[n + 1].ι ≫ σ := by
  constructor
  · intro hx n σ₀ hσ₀
    rw [isInitialVertex_iff_isTerminalVertex_op, isTerminalVertex_iff] at hx
    let τ₀ := (boundary.opIso (n + 1)).inv ≫ opFunctor.map σ₀
    obtain ⟨τ, hτ⟩ := hx τ₀ (by
      rw [yonedaEquiv_comp, ← NatTrans.naturality_apply, boundary.map_const_yonedaEquiv_ι]
      simp only [τ₀, NatTrans.comp_app, ConcreteCategory.comp_apply]
      simp [opFunctor_map, hσ₀])
    exact (boundary.exists_extension_iff_op σ₀).2 ⟨τ, hτ⟩
  · intro hx
    rw [isInitialVertex_iff_isTerminalVertex_op, isTerminalVertex_iff]
    intro n σ₀ hσ₀
    let τ₀ := (boundary.opIso (n + 1)).inv ≫ opFunctor.map σ₀ ≫
      opFunctorCompOpFunctorIso.hom.app X
    have hlast : σ₀.app _ (boundary.vertex n (Fin.last (n + 1))) = opObjEquiv.symm x := by
      rw [yonedaEquiv_comp, ← NatTrans.naturality_apply, boundary.map_const_yonedaEquiv_ι]
        at hσ₀
      simpa using hσ₀
    obtain ⟨τ, hτ⟩ := hx τ₀ (by
      simp only [τ₀, NatTrans.comp_app, ConcreteCategory.comp_apply]
      simp [opFunctor_map, hlast])
    apply (boundary.exists_extension_iff_op σ₀).2
    refine ⟨τ ≫ opFunctorCompOpFunctorIso.inv.app X, ?_⟩
    rw [← Category.assoc, ← hτ]
    simp [τ₀]

namespace IsInitialVertex

variable {x : X _⦋0⦌}

/-- An initial vertex has an edge to every vertex. -/
lemma nonempty_edge (hx : X.IsInitialVertex x) (y : X _⦋0⦌) : Nonempty (X.Edge x y) :=
  (IsTerminalVertex.nonempty_edge hx (X.opObjEquiv.symm y)).map Edge.opEquiv.symm

/-- Every triangle whose first vertex is initial is filled by a `2`-simplex. In particular, any two
edges from an initial vertex to a vertex are homotopic. -/
lemma nonempty_compStruct (hx : X.IsInitialVertex x) {x₁ x₂ : X _⦋0⦌} (e₀₁ : X.Edge x x₁)
    (e₁₂ : X.Edge x₁ x₂) (e₀₂ : X.Edge x x₂) : Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) :=
  (IsTerminalVertex.nonempty_compStruct hx (Edge.opEquiv e₁₂) (Edge.opEquiv e₀₁)
    (Edge.opEquiv e₀₂)).map Edge.CompStruct.opEquiv.symm

/-- Every edge between initial vertices is invertible. Thus initial vertices are unique up to
equivalence. -/
lemma nonempty_invStruct (hx : X.IsInitialVertex x) {x' : X _⦋0⦌}
    (hx' : X.IsInitialVertex x') (e : X.Edge x x') : Nonempty e.InvStruct := by
  obtain ⟨e'⟩ := hx'.nonempty_edge x
  obtain ⟨h⟩ := hx.nonempty_compStruct e e' (.id x)
  obtain ⟨h'⟩ := hx'.nonempty_compStruct e' e (.id x')
  exact ⟨⟨e', h, h'⟩⟩

/-- Initial vertices are preserved by isomorphisms of simplicial sets. -/
lemma map_iso (hx : X.IsInitialVertex x) (e : X ≅ Y) : Y.IsInitialVertex (e.hom.app _ x) :=
  IsTerminalVertex.map_iso hx (opFunctor.mapIso e)

end IsInitialVertex

/-- Initial vertices correspond under isomorphisms of simplicial sets. -/
lemma isInitialVertex_iff_of_iso (e : X ≅ Y) (x : X _⦋0⦌) :
    Y.IsInitialVertex (e.hom.app _ x) ↔ X.IsInitialVertex x :=
  isTerminalVertex_iff_of_iso (opFunctor.mapIso e) _

end SSet

namespace CategoryTheory.nerve

open SSet

/-- A vertex of the nerve of a category is initial exactly when it is an initial object of the
category. -/
theorem isInitialVertex_iff {C : Type u} [Category.{v} C] (x : C) :
    (nerve C).IsInitialVertex (nerveEquiv.symm x) ↔ Nonempty (IsInitial x) := by
  -- The vertex `x` of `(nerve C)ᵒᵖ` is the vertex `op x` of `nerve Cᵒᵖ`.
  have h := isTerminalVertex_iff_of_iso (opIso C) (nerveEquiv.symm (op x))
  rw [opIso_hom_app_nerveEquiv_symm, nerve.isTerminalVertex_iff] at h
  exact h.trans ⟨fun ⟨h⟩ ↦ ⟨h.unop⟩, fun ⟨h⟩ ↦ ⟨h.op⟩⟩

end CategoryTheory.nerve

namespace SSet.stdSimplex

/-- The first vertex of the standard simplex `Δ[n]` is initial. -/
theorem isInitialVertex_zero (n : ℕ) :
    (Δ[n] : SSet.{u}).IsInitialVertex (obj₀Equiv.symm 0) := by
  rw [isInitialVertex_iff_isTerminalVertex_op, ← isTerminalVertex_iff_of_iso (opIso ⦋n⦌)]
  -- Reversing the vertices of `Δ[n]` exchanges its first and last vertices.
  convert isTerminalVertex_last.{u} n
  ext i
  simp [stdSimplex.opObjEquiv_apply]

end SSet.stdSimplex
