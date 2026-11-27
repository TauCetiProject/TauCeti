/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Limits.Preorder
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Slice
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Terminal vertices of simplicial sets

A vertex `x` of a simplicial set `X` is terminal (`SSet.IsTerminalVertex`) if, for every `n ≥ 1`,
every map `∂Δ[n] ⟶ X` whose last vertex is `x` extends to `Δ[n]`. This is Joyal's definition of
a terminal object of a quasicategory. By the universal property of the join, it says that the
projection `X_{/x} ⟶ X` from the slice over `x` is a trivial fibration
(`SSet.isTerminalVertex_iff_rlp_monomorphisms_π`): under `Δ[n] ⋆ Δ[0] ≅ Δ[n + 1]`, the boundary
`∂Δ[n + 1]` is the union of `∂Δ[n] ⋆ Δ[0]` and `Δ[n]`. For a quasicategory this is equivalent to
the contractibility of the mapping spaces into `x` (HTT Proposition 1.2.12.4). Limits of diagrams
in a quasicategory are the terminal vertices of its slices.

In dimension one the condition provides an edge from every vertex to `x`
(`SSet.IsTerminalVertex.nonempty_edge`), and in dimension two a `2`-simplex filling every
triangle ending at `x` (`SSet.IsTerminalVertex.nonempty_compStruct`), so that any two edges to
`x` with the same source are homotopic. Consequently every edge between terminal vertices is
invertible (`SSet.IsTerminalVertex.nonempty_invStruct`), and terminal vertices are unique up to
equivalence. For a strict Segal simplicial set only the conditions in dimensions one and two
matter (`SSet.isTerminalVertex_iff_of_isStrictSegal`). In particular, a vertex of the nerve of
a category is terminal exactly when it is a terminal object of the category
(`CategoryTheory.nerve.isTerminalVertex_iff`), and the last vertex of `Δ[n]` is terminal
(`SSet.stdSimplex.isTerminalVertex_last`). Every vertex of a terminal simplicial set, such as
`Δ[0]`, is terminal (`SSet.isTerminalVertex_of_isTerminal`).

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
* J. Lurie, *Higher Topos Theory*, §1.2.12 (final objects), Proposition 1.2.12.4.
-/

public section

universe v u

open CategoryTheory Limits Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- A vertex `x` of a simplicial set `X` is *terminal* if, for every `n ≥ 1`, every map
`σ₀ : ∂Δ[n] ⟶ X` whose last vertex is `x` extends to `Δ[n]`. The last vertex of
`σ₀ : ∂Δ[n + 1] ⟶ X` is the last vertex of its face `0`, the face opposite to the vertex `0`. -/
def IsTerminalVertex (x : X _⦋0⦌) : Prop :=
  ∀ ⦃n : ℕ⦄ (σ₀ : (∂Δ[n + 1] : SSet) ⟶ X),
    X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op (yonedaEquiv (boundary.ι 0 ≫ σ₀)) = x →
      ∃ σ : Δ[n + 1] ⟶ X, σ₀ = ∂Δ[n + 1].ι ≫ σ

lemma isTerminalVertex_iff (x : X _⦋0⦌) :
    X.IsTerminalVertex x ↔ ∀ ⦃n : ℕ⦄ (σ₀ : (∂Δ[n + 1] : SSet) ⟶ X),
      X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op
          (yonedaEquiv (boundary.ι 0 ≫ σ₀)) = x →
        ∃ σ : Δ[n + 1] ⟶ X, σ₀ = ∂Δ[n + 1].ι ≫ σ :=
  Iff.rfl

namespace IsTerminalVertex

variable {x : X _⦋0⦌}

/-- Every vertex has an edge to a terminal vertex. -/
lemma nonempty_edge (hx : X.IsTerminalVertex x) (y : X _⦋0⦌) : Nonempty (X.Edge y x) := by
  let v : Fin 2 → X _⦋0⦌ := ![x, y]
  have hf : boundary.IsCompatible (fun j ↦ yonedaEquiv.symm (v j)) :=
    (boundary.isCompatible_zero_iff_true _).2 trivial
  obtain ⟨σ, hσ⟩ := hx hf.desc (by
    rw [hf.ι_desc, Equiv.apply_symm_apply, Fin.last_zero, SimplexCategory.const_eq_id, op_id,
      X.map_id, id_apply]
    rfl)
  have h (j : Fin 2) : X.δ j (yonedaEquiv σ) = v j := by
    rw [← (boundary.eq_ι_comp_iff _ _).1 hσ, hf.ι_desc, Equiv.apply_symm_apply]
  exact ⟨Edge.mk (yonedaEquiv σ) (h 1) (h 0)⟩

/-- Every triangle whose last vertex is terminal is filled by a `2`-simplex. In particular, any
two edges from a vertex to a terminal vertex are homotopic. -/
lemma nonempty_compStruct (hx : X.IsTerminalVertex x) {x₀ x₁ : X _⦋0⦌} (e₀₁ : X.Edge x₀ x₁)
    (e₁₂ : X.Edge x₁ x) (e₀₂ : X.Edge x₀ x) : Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let v : Fin 3 → X _⦋1⦌ := ![e₁₂.edge, e₀₂.edge, e₀₁.edge]
  have hf : boundary.IsCompatible (fun j ↦ yonedaEquiv.symm (v j)) := by
    rw [boundary.isCompatible_iff]
    intro j k hjk
    apply yonedaEquiv.injective
    simp only [stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
    fin_cases j <;> fin_cases k <;> simp at hjk
    · exact e₁₂.tgt_eq.trans e₀₂.tgt_eq.symm
    · exact e₁₂.src_eq.trans e₀₁.tgt_eq.symm
    · exact e₀₂.src_eq.trans e₀₁.src_eq.symm
  obtain ⟨σ, hσ⟩ := hx hf.desc (by
    rw [hf.ι_desc, Equiv.apply_symm_apply, show (Fin.last 1 : Fin 2) = 1 by simp,
      ← SimplexCategory.δ_zero_eq_const]
    exact e₁₂.tgt_eq)
  have h (j : Fin 3) : X.δ j (yonedaEquiv σ) = v j := by
    rw [← (boundary.eq_ι_comp_iff _ _).1 hσ, hf.ι_desc, Equiv.apply_symm_apply]
  exact ⟨Edge.CompStruct.mk (yonedaEquiv σ) (h 2) (h 0) (h 1)⟩

/-- Every edge between terminal vertices is invertible. Thus terminal vertices are unique up to
equivalence. -/
lemma nonempty_invStruct (hx : X.IsTerminalVertex x) {x' : X _⦋0⦌}
    (hx' : X.IsTerminalVertex x') (e : X.Edge x x') : Nonempty e.InvStruct := by
  obtain ⟨e'⟩ := hx.nonempty_edge x'
  obtain ⟨h⟩ := hx.nonempty_compStruct e e' (.id x)
  obtain ⟨h'⟩ := hx'.nonempty_compStruct e' e (.id x')
  exact ⟨⟨e', h, h'⟩⟩

/-- Terminal vertices are preserved by isomorphisms of simplicial sets. -/
lemma map_iso (hx : X.IsTerminalVertex x) (e : X ≅ Y) : Y.IsTerminalVertex (e.hom.app _ x) := by
  intro n σ₀ hσ₀
  obtain ⟨σ, hσ⟩ := hx (σ₀ ≫ e.inv) (by
    rw [← Category.assoc, yonedaEquiv_comp, ← NatTrans.naturality_apply, hσ₀]
    simp)
  exact ⟨σ ≫ e.hom, by rw [← Category.assoc, ← hσ, Category.assoc, e.inv_hom_id,
    Category.comp_id]⟩

end IsTerminalVertex

/-- Terminal vertices correspond under isomorphisms of simplicial sets. -/
lemma isTerminalVertex_iff_of_iso (e : X ≅ Y) (x : X _⦋0⦌) :
    Y.IsTerminalVertex (e.hom.app _ x) ↔ X.IsTerminalVertex x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map_iso e⟩
  simpa using h.map_iso e.symm

/-- Under `Δ[n] ⋆ Δ[0] ≅ Δ[n + 0 + 1]`, the last vertex of the face opposite to `0` is the vertex
`Δ[0]`. -/
private lemma const_last_comp_δ_zero (n : ℕ) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ stdSimplex.δ 0 =
      join.inr Δ[n] Δ[0] ≫ (join.stdSimplexIso.{u} n 0).hom := by
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun i ↦ ?_
  rw [join.yonedaEquiv_inr_comp_stdSimplexIso_hom.{u} (n := n) (m := 0) i,
    stdSimplex.yonedaEquiv_comp_apply]
  ext
  simp [CosimplicialObject.δ, SimplexCategory.δ]

/-- Under `Δ[n] ⋆ Δ[0] ≅ Δ[n + 1]`, the vertex `Δ[0]` of `(∂Δ[n] ⋆ Δ[0]) ∪ (Δ[n] ⋆ ∂Δ[0])` is the
last vertex of the face opposite to `0` of `∂Δ[n + 1]`. -/
private lemma const_last_comp_boundary_ι_comp_isoOfPreimageEq_inv (n : ℕ) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ boundary.ι 0 ≫
      (Subcomplex.isoOfPreimageEq (join.stdSimplexIso.{u} n 0)
        (join.preimage_unionJoin_boundary_boundary n 0 : _ = ∂Δ[n + 1])).inv =
        join.inr _ _ ≫ Subcomplex.unionJoin.ι₁ ∂Δ[n] ∂Δ[0] := by
  rw [← cancel_mono (Subcomplex.unionJoin ∂Δ[n] ∂Δ[0]).ι,
    ← cancel_mono (join.stdSimplexIso.{u} n 0).hom]
  simp only [Category.assoc, Subcomplex.isoOfPreimageEq_inv_ι, boundary.ι_ι_assoc,
    Iso.inv_hom_id, Category.comp_id, Subcomplex.unionJoin.ι₁_ι_assoc, join.inr_map_assoc,
    Category.id_comp]
  exact const_last_comp_δ_zero n

/-- If `x` is terminal, the projection `X_{/x} ⟶ X` lifts against `∂Δ[n] ⟶ Δ[n]`: a lifting
problem glues, on `(∂Δ[n] ⋆ Δ[0]) ∪ (Δ[n] ⋆ ∂Δ[0]) ≅ ∂Δ[n + 1]`, to a map with last vertex `x`. -/
private lemma hasLiftingProperty_π_of_isTerminalVertex {x : X _⦋0⦌} (hx : X.IsTerminalVertex x)
    (n : ℕ) : HasLiftingProperty ∂Δ[n].ι (slice.π (yonedaEquiv.symm x)) := by
  have h₀ : ¬ (∂Δ[0] : SSet.{u}).Nonempty := by
    rw [boundary_zero]
    exact Subcomplex.not_nonempty_bot
  have := join.isIso_inl (K := Δ[n]) h₀
  have := join.isIso_inl (K := ∂Δ[n]) h₀
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- Glue the cone `∂Δ[n] ⋆ Δ[0] ⟶ X` of `a` with `b` on `Δ[n] ≅ Δ[n] ⋆ ∂Δ[0]`.
  have hc : join.map (𝟙 _) (boundary.{u} 0).ι ≫ (slice.homEquiv a).val =
      join.map ∂Δ[n].ι (𝟙 _) ≫ inv (join.inl Δ[n] (boundary.{u} 0 : SSet.{u})) ≫ b := by
    rw [← cancel_epi (join.inl _ _), join.inl_map_assoc, Category.id_comp, join.inl_map_assoc,
      IsIso.hom_inv_id_assoc, ← slice.comp_π, sq.w]
  let U := Subcomplex.unionJoin ∂Δ[n] (boundary.{u} 0)
  let g := (Subcomplex.unionJoin.isPushout ∂Δ[n] (boundary.{u} 0)).desc
    (slice.homEquiv a).val (inv (join.inl Δ[n] (boundary.{u} 0 : SSet.{u})) ≫ b) hc
  have hg₁ : Subcomplex.unionJoin.ι₁ _ _ ≫ g = (slice.homEquiv a).val :=
    (Subcomplex.unionJoin.isPushout _ _).inl_desc _ _ _
  have hg₂ : Subcomplex.unionJoin.ι₂ _ _ ≫ g =
      inv (join.inl Δ[n] (boundary.{u} 0 : SSet.{u})) ≫ b :=
    (Subcomplex.unionJoin.isPushout _ _).inr_desc _ _ _
  let e := join.stdSimplexIso.{u} n 0
  have key : U.preimage e.inv = ∂Δ[n + 1] := join.preimage_unionJoin_boundary_boundary n 0
  let i := Subcomplex.isoOfPreimageEq e key
  -- Extend the glued map, whose last vertex is `x`, to `Δ[n + 1] ≅ Δ[n] ⋆ Δ[0]`.
  obtain ⟨σ, hσ⟩ := hx (i.inv ≫ g) (by
    rw [yonedaEquiv_naturality,
      reassoc_of% const_last_comp_boundary_ι_comp_isoOfPreimageEq_inv n, hg₁,
      (slice.homEquiv a).property, Equiv.apply_symm_apply])
  have hσU : U.ι ≫ e.hom ≫ σ = g := by
    rw [← Subcomplex.isoOfPreimageEq_hom_ι_assoc e key, ← hσ, i.hom_inv_id_assoc]
  have hinr : join.inr Δ[n] Δ[0] ≫ e.hom ≫ σ = yonedaEquiv.symm x := by
    rw [← Category.id_comp (join.inr Δ[n] Δ[0]), ← join.inr_map ∂Δ[n].ι, Category.assoc,
      ← Subcomplex.unionJoin.ι₁_ι, Category.assoc, hσU, hg₁]
    exact (slice.homEquiv a).property
  let l := slice.homEquiv.symm ⟨e.hom ≫ σ, hinr⟩
  have hl : (slice.homEquiv l).val = e.hom ≫ σ := by rw [Equiv.apply_symm_apply]
  refine ⟨⟨⟨l, slice.hom_ext ?_, ?_⟩⟩⟩
  · rw [slice.homEquiv_comp_coe, hl, ← Subcomplex.unionJoin.ι₁_ι, Category.assoc, hσU, hg₁]
  · rw [slice.comp_π, hl, ← Category.id_comp (join.inl Δ[n] Δ[0]),
      ← join.inl_map (𝟙 _) (boundary.{u} 0).ι, Category.assoc, ← Subcomplex.unionJoin.ι₂_ι,
      Category.assoc, hσU, hg₂, IsIso.hom_inv_id_assoc]

/-- If the projection `X_{/x} ⟶ X` lifts against all boundary inclusions, then `x` is terminal: a
map `∂Δ[n + 1] ≅ (∂Δ[n] ⋆ Δ[0]) ∪ (Δ[n] ⋆ ∂Δ[0]) ⟶ X` with last vertex `x` is a lifting problem
against the projection. -/
private lemma isTerminalVertex_of_hasLiftingProperty_π {x : X _⦋0⦌}
    (h : ∀ n : ℕ, HasLiftingProperty ∂Δ[n].ι (slice.π (yonedaEquiv.symm x))) :
    X.IsTerminalVertex x := by
  intro n σ₀ hσ₀
  have h₀ : ¬ (∂Δ[0] : SSet.{u}).Nonempty := by
    rw [boundary_zero]
    exact Subcomplex.not_nonempty_bot
  have := join.isIso_inl (K := Δ[n]) h₀
  let U := Subcomplex.unionJoin ∂Δ[n] ∂Δ[0]
  let e := join.stdSimplexIso.{u} n 0
  have key : U.preimage e.inv = ∂Δ[n + 1] := join.preimage_unionJoin_boundary_boundary n 0
  let i := Subcomplex.isoOfPreimageEq e key
  let g : (U : SSet.{u}) ⟶ X := i.hom ≫ σ₀
  -- The map `g` on `U` is a cone `a` over `x` on `∂Δ[n]` and a simplex `b` on `Δ[n]`.
  have ha : join.inr _ _ ≫ Subcomplex.unionJoin.ι₁ _ _ ≫ g = yonedaEquiv.symm x := by
    rw [← reassoc_of% const_last_comp_boundary_ι_comp_isoOfPreimageEq_inv n,
      i.inv_hom_id_assoc, ← hσ₀]
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_naturality]
  let a := slice.homEquiv.symm ⟨Subcomplex.unionJoin.ι₁ _ _ ≫ g, ha⟩
  let b : Δ[n] ⟶ X := join.inl _ _ ≫ Subcomplex.unionJoin.ι₂ ∂Δ[n] ∂Δ[0] ≫ g
  have sq : CommSq a ∂Δ[n].ι (slice.π (yonedaEquiv.symm x)) b := ⟨by
    rw [slice.comp_π, Equiv.apply_symm_apply, ← join.inl_map_assoc ∂Δ[n].ι (𝟙 _),
      ← (Subcomplex.unionJoin.isPushout _ _).w_assoc, join.inl_map_assoc, Category.id_comp]⟩
  have hl₁ := congrArg (fun F ↦ (slice.homEquiv F).val) sq.fac_left
  simp only [slice.homEquiv_comp_coe, a, Equiv.apply_symm_apply] at hl₁
  have hl₂ := sq.fac_right
  rw [slice.comp_π] at hl₂
  -- The lift is a map `Δ[n] ⋆ Δ[0] ≅ Δ[n + 1] ⟶ X` agreeing with `g` on both parts of `U`.
  refine ⟨e.inv ≫ (slice.homEquiv sq.lift).val, ?_⟩
  have hU : U.ι ≫ (slice.homEquiv sq.lift).val = g := by
    refine (Subcomplex.unionJoin.isPushout _ _).hom_ext ?_ ?_
    · rw [Subcomplex.unionJoin.ι₁_ι_assoc, hl₁]
    · rw [Subcomplex.unionJoin.ι₂_ι_assoc, ← cancel_epi (join.inl Δ[n] ∂Δ[0]),
        join.inl_map_assoc, Category.id_comp, hl₂]
  rw [← cancel_epi i.hom, Subcomplex.isoOfPreimageEq_hom_ι_assoc e key, Iso.hom_inv_id_assoc, hU]

/-- **A vertex `x` is terminal exactly when the projection `X_{/x} ⟶ X` from the slice over `x` is
a trivial fibration**: it has the right lifting property with respect to all monomorphisms. Under
`Δ[n] ⋆ Δ[0] ≅ Δ[n + 1]`, the boundary `∂Δ[n + 1]` is the union of `∂Δ[n] ⋆ Δ[0]` and
`Δ[n] ≅ Δ[n] ⋆ ∂Δ[0]`, so that a map `∂Δ[n + 1] ⟶ X` with last vertex `x` is a lifting problem of
`∂Δ[n] ⟶ Δ[n]` against the projection. -/
theorem isTerminalVertex_iff_rlp_monomorphisms_π (x : X _⦋0⦌) :
    X.IsTerminalVertex x ↔
      (MorphismProperty.monomorphisms SSet.{u}).rlp (slice.π (yonedaEquiv.symm x)) := by
  rw [rlp_monomorphisms]
  exact ⟨fun hx _ _ _ ⟨n⟩ ↦ hasLiftingProperty_π_of_isTerminalVertex hx n,
    fun h ↦ isTerminalVertex_of_hasLiftingProperty_π fun n ↦
      h _ (modelCategoryQuillen.boundary_ι_mem_I n)⟩

/-- Every vertex of a terminal simplicial set, such as `Δ[0]`, is terminal. -/
lemma isTerminalVertex_of_isTerminal (hX : IsTerminal X) (x : X _⦋0⦌) : X.IsTerminalVertex x :=
  fun _ _ _ ↦ ⟨hX.from _, hX.hom_ext _ _⟩

/-- In a strict Segal simplicial set, such as the nerve of a category, a vertex `x` is terminal
exactly when every vertex has an edge to `x` and every triangle ending at `x` is filled: maps
from the boundaries of higher simplices always extend. -/
theorem isTerminalVertex_iff_of_isStrictSegal [X.IsStrictSegal] (x : X _⦋0⦌) :
    X.IsTerminalVertex x ↔ (∀ y, Nonempty (X.Edge y x)) ∧
      ∀ ⦃x₀ x₁ : X _⦋0⦌⦄ (e₀₁ : X.Edge x₀ x₁) (e₁₂ : X.Edge x₁ x) (e₀₂ : X.Edge x₀ x),
        Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  refine ⟨fun hx ↦ ⟨hx.nonempty_edge, fun _ _ ↦ hx.nonempty_compStruct⟩,
    fun ⟨h₁, h₂⟩ n σ₀ hσ₀ ↦ ?_⟩
  match n with
  | 0 =>
    -- The boundary of an edge consists of its two vertices.
    rw [Fin.last_zero, SimplexCategory.const_eq_id, op_id, X.map_id, id_apply] at hσ₀
    obtain ⟨e⟩ := h₁ (yonedaEquiv (boundary.ι 1 ≫ σ₀))
    refine ⟨yonedaEquiv.symm e.edge, (boundary.eq_ι_comp_iff _ _).2 fun j ↦ ?_⟩
    rw [Equiv.apply_symm_apply]
    fin_cases j
    · exact hσ₀.trans e.tgt_eq.symm
    · exact e.src_eq.symm
  | 1 =>
    -- The boundary of a triangle consists of three edges with matching endpoints.
    rw [show (Fin.last 1 : Fin 2) = 1 by simp, ← SimplexCategory.δ_zero_eq_const] at hσ₀
    have h₀₁ := congrArg yonedaEquiv ((boundary.IsCompatible.of_hom σ₀).δ_pred_comp 0 1)
    have h₀₂ := congrArg yonedaEquiv ((boundary.IsCompatible.of_hom σ₀).δ_pred_comp 0 2)
    have h₁₂ := congrArg yonedaEquiv ((boundary.IsCompatible.of_hom σ₀).δ_pred_comp 1 2)
    simp only [stdSimplex.yonedaEquiv_δ_comp] at h₀₁ h₀₂ h₁₂
    obtain ⟨c⟩ := h₂ (Edge.mk (yonedaEquiv (boundary.ι 2 ≫ σ₀)) rfl rfl)
      (Edge.mk (yonedaEquiv (boundary.ι 0 ≫ σ₀)) h₀₂ hσ₀)
      (Edge.mk (yonedaEquiv (boundary.ι 1 ≫ σ₀)) h₁₂ (h₀₁.symm.trans hσ₀))
    refine ⟨yonedaEquiv.symm c.simplex, (boundary.eq_ι_comp_iff _ _).2 fun j ↦ ?_⟩
    rw [Equiv.apply_symm_apply]
    fin_cases j
    · exact c.d₀.symm
    · exact c.d₁.symm
    · exact c.d₂.symm
  | n + 2 => exact IsStrictSegal.exists_boundary_extension σ₀

end SSet

namespace CategoryTheory.nerve

open SSet

/-- A vertex of the nerve of a category is terminal exactly when it is a terminal object of the
category. -/
theorem isTerminalVertex_iff {C : Type u} [Category.{v} C] (x : C) :
    (nerve C).IsTerminalVertex (nerveEquiv.symm x) ↔ Nonempty (IsTerminal x) := by
  refine (isTerminalVertex_iff_of_isStrictSegal (X := nerve C) _).trans ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    have huniq {y : C} (f g : y ⟶ x) : f = g := by
      have c : Nonempty (Edge.CompStruct (edgeMk f) (edgeMk (𝟙 x)) (edgeMk g)) := by
        rw [edgeMk_id]
        exact h₂ _ _ _
      simpa using (nonempty_compStruct_iff _ _ _).1 c
    exact ⟨IsTerminal.ofUniqueHom
      (fun y ↦ (edgeMk_surjective (h₁ (nerveEquiv.symm y)).some).choose) fun _ _ ↦ huniq _ _⟩
  · rintro ⟨h⟩
    refine ⟨fun y ↦ ?_, fun x₀ x₁ e₀₁ e₁₂ e₀₂ ↦ ?_⟩
    · obtain ⟨y, rfl⟩ := nerveEquiv.symm.surjective y
      exact ⟨edgeMk (h.from y)⟩
    · obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
      obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
      obtain ⟨f₀₁, rfl⟩ := edgeMk_surjective e₀₁
      obtain ⟨f₁₂, rfl⟩ := edgeMk_surjective e₁₂
      obtain ⟨f₀₂, rfl⟩ := edgeMk_surjective e₀₂
      exact (nonempty_compStruct_iff _ _ _).2 (h.hom_ext _ _)

end CategoryTheory.nerve

namespace SSet.stdSimplex

/-- The last vertex of the standard simplex `Δ[n]` is terminal. -/
theorem isTerminalVertex_last (n : ℕ) :
    (Δ[n] : SSet.{u}).IsTerminalVertex (obj₀Equiv.symm (Fin.last n)) := by
  rw [← isTerminalVertex_iff_of_iso (isoNerve n)]
  have : (isoNerve.{u} n).hom.app _ (obj₀Equiv.symm (Fin.last n)) =
      nerveEquiv.symm (ULift.up (Fin.last n)) :=
    ComposableArrows.ext₀ rfl
  rw [this, nerve.isTerminalVertex_iff]
  exact ⟨isTerminalTop⟩

end SSet.stdSimplex
