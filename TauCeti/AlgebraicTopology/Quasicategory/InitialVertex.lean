/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.TerminalVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
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
(`SSet.isInitialVertex_iff`). This criterion uses reversal of simplex boundaries. By the universal
property of the join, it says that the projection `X_{x/} ⟶ X` from the coslice under `x` is a
trivial fibration (`SSet.isInitialVertex_iff_rlp_monomorphisms_π`): under
`Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, the boundary `∂Δ[n + 1]` is the union of `Δ[n]` and `Δ[0] ⋆ ∂Δ[n]`.

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
initial (`SSet.stdSimplex.isInitialVertex_zero`). Every vertex of a terminal simplicial set, such
as `Δ[0]`, is initial (`SSet.isInitialVertex_of_isTerminal`).

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

/-- Under `Δ[0] ⋆ Δ[n] ≅ Δ[0 + n + 1]`, the vertex `Δ[0]` of `(∂Δ[0] ⋆ Δ[n]) ∪ (Δ[0] ⋆ ∂Δ[n])` is
the first vertex of `∂Δ[0 + n + 1]`. -/
private lemma yonedaEquiv_symm_vertex_zero_comp_isoOfPreimageEq_inv (n : ℕ) :
    yonedaEquiv.symm (boundary.vertex (0 + n) 0) ≫
      (Subcomplex.isoOfPreimageEq (join.stdSimplexIso.{u} 0 n)
        (join.preimage_unionJoin_boundary_boundary 0 n)).inv =
        join.inl _ _ ≫ Subcomplex.unionJoin.ι₂ (boundary.{u} 0) ∂Δ[n] := by
  rw [← cancel_mono (Subcomplex.unionJoin (boundary.{u} 0) ∂Δ[n]).ι,
    ← cancel_mono (join.stdSimplexIso.{u} 0 n).hom]
  simp only [Category.assoc, Subcomplex.isoOfPreimageEq_inv_ι, Iso.inv_hom_id,
    Category.comp_id, Subcomplex.unionJoin.ι₂_ι_assoc, join.inl_map_assoc, Category.id_comp,
    join.inl_comp_stdSimplexIso_hom]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_map]
  refine (boundary.vertex_val _ _).trans ?_
  ext i
  fin_cases i
  rfl

/-- If `x` is initial, the projection `X_{x/} ⟶ X` lifts against `∂Δ[n] ⟶ Δ[n]`: a lifting
problem glues, on `(∂Δ[0] ⋆ Δ[n]) ∪ (Δ[0] ⋆ ∂Δ[n]) ≅ ∂Δ[0 + n + 1]`, to a map with first vertex
`x`. -/
private lemma hasLiftingProperty_π_of_isInitialVertex {x : X _⦋0⦌} (hx : X.IsInitialVertex x)
    (n : ℕ) : HasLiftingProperty ∂Δ[n].ι (coslice.π (yonedaEquiv.symm x)) := by
  rw [isInitialVertex_iff] at hx
  have h₀ : ¬ (∂Δ[0] : SSet.{u}).Nonempty := by
    rw [boundary_zero]
    exact Subcomplex.not_nonempty_bot
  have := join.isIso_inr (L := Δ[n]) h₀
  have := join.isIso_inr (L := ∂Δ[n]) h₀
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- Glue the cocone `Δ[0] ⋆ ∂Δ[n] ⟶ X` of `a` with `b` on `Δ[n] ≅ ∂Δ[0] ⋆ Δ[n]`.
  have hc : join.map (𝟙 _) ∂Δ[n].ι ≫ inv (join.inr (boundary.{u} 0 : SSet.{u}) Δ[n]) ≫ b =
      join.map (boundary.{u} 0).ι (𝟙 _) ≫ (coslice.homEquiv a).val := by
    rw [← cancel_epi (join.inr _ _), join.inr_map_assoc, IsIso.hom_inv_id_assoc,
      join.inr_map_assoc, Category.id_comp, ← coslice.comp_π, sq.w]
  let U := Subcomplex.unionJoin (boundary.{u} 0) ∂Δ[n]
  let g := (Subcomplex.unionJoin.isPushout (boundary.{u} 0) ∂Δ[n]).desc
    (inv (join.inr (boundary.{u} 0 : SSet.{u}) Δ[n]) ≫ b) (coslice.homEquiv a).val hc
  have hg₁ : Subcomplex.unionJoin.ι₁ _ _ ≫ g =
      inv (join.inr (boundary.{u} 0 : SSet.{u}) Δ[n]) ≫ b :=
    (Subcomplex.unionJoin.isPushout _ _).inl_desc _ _ _
  have hg₂ : Subcomplex.unionJoin.ι₂ _ _ ≫ g = (coslice.homEquiv a).val :=
    (Subcomplex.unionJoin.isPushout _ _).inr_desc _ _ _
  let e := join.stdSimplexIso.{u} 0 n
  have key : U.preimage e.inv = ∂Δ[0 + n + 1] := join.preimage_unionJoin_boundary_boundary 0 n
  let i := Subcomplex.isoOfPreimageEq e key
  -- Extend the glued map, whose first vertex is `x`, to `Δ[0 + n + 1] ≅ Δ[0] ⋆ Δ[n]`.
  obtain ⟨σ, hσ⟩ := hx (i.inv ≫ g) (by
    apply yonedaEquiv.symm.injective
    rw [← yonedaEquiv_symm_comp,
      reassoc_of% yonedaEquiv_symm_vertex_zero_comp_isoOfPreimageEq_inv n, hg₂,
      (coslice.homEquiv a).property])
  have hσU : U.ι ≫ e.hom ≫ σ = g := by
    rw [← Subcomplex.isoOfPreimageEq_hom_ι_assoc e key, ← hσ, i.hom_inv_id_assoc]
  have hinl : join.inl Δ[0] Δ[n] ≫ e.hom ≫ σ = yonedaEquiv.symm x := by
    rw [← Category.id_comp (join.inl Δ[0] Δ[n]), ← join.inl_map (𝟙 _) ∂Δ[n].ι, Category.assoc,
      ← Subcomplex.unionJoin.ι₂_ι, Category.assoc, hσU, hg₂]
    exact (coslice.homEquiv a).property
  let l := coslice.homEquiv.symm ⟨e.hom ≫ σ, hinl⟩
  have hl : (coslice.homEquiv l).val = e.hom ≫ σ := by rw [Equiv.apply_symm_apply]
  refine ⟨⟨⟨l, coslice.hom_ext ?_, ?_⟩⟩⟩
  · rw [coslice.homEquiv_comp_coe, hl, ← Subcomplex.unionJoin.ι₂_ι, Category.assoc, hσU, hg₂]
  · rw [coslice.comp_π, hl, ← Category.id_comp (join.inr Δ[0] Δ[n]),
      ← join.inr_map (boundary.{u} 0).ι (𝟙 _), Category.assoc, ← Subcomplex.unionJoin.ι₁_ι,
      Category.assoc, hσU, hg₁, IsIso.hom_inv_id_assoc]

/-- If the projection `X_{x/} ⟶ X` lifts against all boundary inclusions, then `x` is initial: a
map `∂Δ[0 + m + 1] ≅ (∂Δ[0] ⋆ Δ[m]) ∪ (Δ[0] ⋆ ∂Δ[m]) ⟶ X` with first vertex `x` is a lifting
problem against the projection. -/
private lemma isInitialVertex_of_hasLiftingProperty_π {x : X _⦋0⦌}
    (h : ∀ n : ℕ, HasLiftingProperty ∂Δ[n].ι (coslice.π (yonedaEquiv.symm x))) :
    X.IsInitialVertex x := by
  rw [isInitialVertex_iff]
  intro n σ₀ hσ₀
  obtain ⟨m, rfl⟩ : ∃ m, n = 0 + m := ⟨n, (Nat.zero_add n).symm⟩
  have h₀ : ¬ (∂Δ[0] : SSet.{u}).Nonempty := by
    rw [boundary_zero]
    exact Subcomplex.not_nonempty_bot
  have := join.isIso_inr (L := Δ[m]) h₀
  let U := Subcomplex.unionJoin (boundary.{u} 0) ∂Δ[m]
  let e := join.stdSimplexIso.{u} 0 m
  have key : U.preimage e.inv = ∂Δ[0 + m + 1] := join.preimage_unionJoin_boundary_boundary 0 m
  let i := Subcomplex.isoOfPreimageEq e key
  let g : (U : SSet.{u}) ⟶ X := i.hom ≫ σ₀
  -- The map `g` on `U` is a cocone `a` under `x` on `∂Δ[m]` and a simplex `b` on `Δ[m]`.
  have ha : join.inl _ _ ≫ Subcomplex.unionJoin.ι₂ _ _ ≫ g = yonedaEquiv.symm x := by
    rw [← reassoc_of% yonedaEquiv_symm_vertex_zero_comp_isoOfPreimageEq_inv m,
      i.inv_hom_id_assoc, yonedaEquiv_symm_comp, hσ₀]
  let a := coslice.homEquiv.symm ⟨Subcomplex.unionJoin.ι₂ _ _ ≫ g, ha⟩
  let b : Δ[m] ⟶ X := join.inr _ _ ≫ Subcomplex.unionJoin.ι₁ (boundary.{u} 0) ∂Δ[m] ≫ g
  have sq : CommSq a ∂Δ[m].ι (coslice.π (yonedaEquiv.symm x)) b := ⟨by
    rw [coslice.comp_π, Equiv.apply_symm_apply, ← join.inr_map_assoc (𝟙 _) ∂Δ[m].ι,
      (Subcomplex.unionJoin.isPushout _ _).w_assoc, join.inr_map_assoc, Category.id_comp]⟩
  have := h m
  have hl₁ := congrArg (fun F ↦ (coslice.homEquiv F).val) sq.fac_left
  simp only [coslice.homEquiv_comp_coe, a, Equiv.apply_symm_apply] at hl₁
  have hl₂ := sq.fac_right
  rw [coslice.comp_π] at hl₂
  -- The lift is a map `Δ[0] ⋆ Δ[m] ≅ Δ[0 + m + 1] ⟶ X` agreeing with `g` on both parts of `U`.
  refine ⟨e.inv ≫ (coslice.homEquiv sq.lift).val, ?_⟩
  have hU : U.ι ≫ (coslice.homEquiv sq.lift).val = g := by
    refine (Subcomplex.unionJoin.isPushout _ _).hom_ext ?_ ?_
    · rw [Subcomplex.unionJoin.ι₁_ι_assoc, ← cancel_epi (join.inr (boundary.{u} 0 : SSet.{u}) _),
        join.inr_map_assoc, Category.id_comp, hl₂]
    · rw [Subcomplex.unionJoin.ι₂_ι_assoc, hl₁]
  rw [← cancel_epi i.hom, Subcomplex.isoOfPreimageEq_hom_ι_assoc e key, Iso.hom_inv_id_assoc, hU]

/-- **A vertex `x` is initial exactly when the projection `X_{x/} ⟶ X` from the coslice under `x`
is a trivial fibration**: it has the right lifting property with respect to all monomorphisms.
Under `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, the boundary `∂Δ[n + 1]` is the union of `Δ[n] ≅ ∂Δ[0] ⋆ Δ[n]` and
`Δ[0] ⋆ ∂Δ[n]`, so that a map `∂Δ[n + 1] ⟶ X` with first vertex `x` is a lifting problem of
`∂Δ[n] ⟶ Δ[n]` against the projection. -/
theorem isInitialVertex_iff_rlp_monomorphisms_π (x : X _⦋0⦌) :
    X.IsInitialVertex x ↔
      (MorphismProperty.monomorphisms SSet.{u}).rlp (coslice.π (yonedaEquiv.symm x)) := by
  rw [rlp_monomorphisms]
  exact ⟨fun hx _ _ _ ⟨n⟩ ↦ hasLiftingProperty_π_of_isInitialVertex hx n,
    fun h ↦ isInitialVertex_of_hasLiftingProperty_π fun n ↦
      h _ (modelCategoryQuillen.boundary_ι_mem_I n)⟩

/-- Every vertex of a terminal simplicial set, such as `Δ[0]`, is initial. -/
lemma isInitialVertex_of_isTerminal (hX : IsTerminal X) (x : X _⦋0⦌) : X.IsInitialVertex x :=
  (isInitialVertex_iff x).2 fun _ _ _ ↦ ⟨hX.from _, hX.hom_ext _ _⟩

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
