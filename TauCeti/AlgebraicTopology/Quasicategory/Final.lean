/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# Final maps of simplicial sets

A map `f : K ⟶ L` to a quasicategory is *final* (`SSet.IsFinal`) when, for every vertex `y` of
`L`, the fibre product `K ×_L L_{y/}` of `f` with the projection `SSet.coslice.π` from the coslice
under `y` is weakly contractible (`SSet.IsWeaklyContractible`). By Joyal's quasicategorical
Theorem A (HTT Theorem 4.1.3.1, not proved here) this agrees with Lurie's definition of cofinal
maps through right fibrations, and final maps are those along which restriction detects colimit
cocones. The definition makes sense for any simplicial set `L`, but it is the intended notion only
when `L` is a quasicategory.

For the inclusion `x : Δ[0] ⟶ L` of a vertex, the fibre over `y` is the left mapping space
`Hom^L_L(y, x)`: its simplices are the maps `Δ[0] ⋆ Δ[n] ⟶ L` sending the cone point to `y` and the
base `Δ[n]` to `x` (`SSet.coslice.pullbackConstHomEquiv`), and its vertices are the edges from `y`
to `x` (`SSet.coslice.pullbackConstObj₀Equiv`). If `L` is strict Segal, for instance the nerve of a
category, such maps are determined by their first edge, so this fibre is the discrete simplicial
set on the edges from `y` to `x` (`SSet.coslice.constEdgeIso`). Hence a vertex of a strict
Segal simplicial set is final exactly when every vertex has a unique edge to it. For the nerve of
a category this says that a vertex is final exactly when it is a terminal object, and in a
standard simplex `Δ[n]` exactly when it is the last vertex. In particular `{1} ⟶ Δ[1]` is final,
while `{0} ⟶ Δ[1]` is not: its fibre over the vertex `1` is empty.

## Main definitions

* `SSet.IsFinal f`: the map `f : K ⟶ L` is final.
* `SSet.coslice.pullbackConstHomEquiv x y`: maps to the fibre over `y` of the inclusion of the
  vertex `x` are the maps `Δ[0] ⋆ Z ⟶ L` sending the cone point to `y` and `Z` to `x`.
* `SSet.coslice.constEdgeIso x y`: for a strict Segal `L`, this fibre is the discrete simplicial
  set on the edges from `y` to `x`.

## Main results

* `SSet.isWeaklyContractible_pullback_const_iff`: for a strict Segal `L`, the fibre over `y` of the
  inclusion of `x` is weakly contractible exactly when there is a unique edge from `y` to `x`.
* `SSet.isFinal_const_iff_of_isStrictSegal`: a vertex `x` of a strict Segal simplicial set is final
  exactly when every vertex has a unique edge to `x`.
* `CategoryTheory.nerve.isFinal_const_iff`: a vertex of the nerve of a category is final exactly
  when it is a terminal object.
* `SSet.stdSimplex.isFinal_const_iff`: a vertex of `Δ[n]` is final exactly when it is the last
  vertex; thus `{1} ⟶ Δ[1]` is final (`SSet.stdSimplex.isFinal_const_one`) and `{0} ⟶ Δ[1]` is not
  (`SSet.stdSimplex.not_isFinal_const_zero`).

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (left mapping spaces), Definition 4.1.1.1 and
  Theorem 4.1.3.1.
-/

public section

open CategoryTheory Limits Opposite Simplicial

universe u v

namespace SSet

/-- A map `f : K ⟶ L` is *final* when, for every vertex `y` of `L`, the fibre product
`K ×_L L_{y/}` of `f` with the projection from the coslice of `L` under `y` is weakly contractible.
This is the notion of finality for maps to a quasicategory `L`. -/
class IsFinal {K L : SSet.{u}} (f : K ⟶ L) : Prop where
  isWeaklyContractible_pullback (y : L _⦋0⦌) :
    IsWeaklyContractible (pullback f (coslice.π (const y : Δ[0] ⟶ L)))

/-- A map `f : K ⟶ L` is final exactly when its fibre products with the coslices of `L` under its
vertices are weakly contractible. -/
lemma isFinal_iff {K L : SSet.{u}} (f : K ⟶ L) :
    IsFinal f ↔ ∀ y : L _⦋0⦌, IsWeaklyContractible (pullback f (coslice.π (const y : Δ[0] ⟶ L))) :=
  ⟨fun h ↦ h.isWeaklyContractible_pullback, fun h ↦ ⟨h⟩⟩

namespace coslice

variable {L Z : SSet.{u}} (x y : L _⦋0⦌)

/-- Maps from `Z` to the fibre `{x} ×_L L_{y/}` over `y` of the inclusion of the vertex `x` are
the maps `Δ[0] ⋆ Z ⟶ L` sending the cone point to `y` and `Z` to `x`. This is the universal
property of the left mapping space `Hom^L_L(y, x)`. -/
noncomputable def pullbackConstHomEquiv :
    (Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) ≃
      {τ : join Δ[0] Z ⟶ L // join.inl _ _ ≫ τ = const y ∧ join.inr _ _ ≫ τ = const x} where
  toFun g := ⟨(homEquiv (g ≫ pullback.snd _ _)).1, (homEquiv _).2, by
    rw [← comp_π, Category.assoc, ← pullback.condition, comp_const, comp_const]⟩
  invFun τ := pullback.lift (stdSimplex.isTerminalObj₀.from Z) (homEquiv.symm ⟨τ.1, τ.2.1⟩) (by
    rw [comp_π, Equiv.apply_symm_apply, τ.2.2, comp_const])
  left_inv g := pullback.hom_ext stdSimplex.ext₀ (by
    rw [pullback.lift_snd]
    exact homEquiv.symm_apply_apply _)
  right_inv τ := Subtype.ext (by simp)

/-- The universal property of the fibre `{x} ×_L L_{y/}` is natural: precomposing with
`g : Z' ⟶ Z` corresponds to precomposing with `Δ[0] ⋆ g`. -/
@[simp]
lemma pullbackConstHomEquiv_comp_coe {Z' : SSet.{u}} (g : Z' ⟶ Z)
    (h : Z ⟶ pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) :
    (pullbackConstHomEquiv x y (g ≫ h)).1 = join.map (𝟙 _) g ≫ (pullbackConstHomEquiv x y h).1 := by
  simp only [pullbackConstHomEquiv, Equiv.coe_fn_mk, homEquiv_comp_coe]
  rw [← join.map_comp_assoc, Category.comp_id]

/-- Maps `Δ[0] ⋆ Δ[0] ⟶ L` sending the cone point to `y` and the base to `x` are the edges from `y`
to `x`, through `Δ[0] ⋆ Δ[0] ≅ Δ[1]`. -/
private noncomputable def edgeEquiv :
    {τ : join Δ[0] Δ[0] ⟶ L // join.inl _ _ ≫ τ = const y ∧ join.inr _ _ ≫ τ = const x} ≃
      Edge y x where
  toFun τ := Edge.mk (yonedaEquiv ((join.stdSimplexIso 0 0).inv ≫ τ.1))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, reassoc_of% join.δ_one_comp_stdSimplexIso_inv, τ.2.1,
      yonedaEquiv_const])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, reassoc_of% join.δ_zero_comp_stdSimplexIso_inv,
      τ.2.2, yonedaEquiv_const])
  invFun e := ⟨(join.stdSimplexIso 0 0).hom ≫ yonedaEquiv.symm e.edge,
    by rw [← join.δ_one_comp_stdSimplexIso_inv, Category.assoc, Iso.inv_hom_id_assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq, yonedaEquiv_symm_zero],
    by rw [← join.δ_zero_comp_stdSimplexIso_inv, Category.assoc, Iso.inv_hom_id_assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq, yonedaEquiv_symm_zero]⟩
  left_inv τ := Subtype.ext (by simp)
  right_inv e := Edge.ext (by simp)

/-- The vertices of the fibre `{x} ×_L L_{y/}` over `y` of the inclusion of the vertex `x` are the
edges from `y` to `x`. -/
noncomputable def pullbackConstObj₀Equiv :
    (pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) _⦋0⦌ ≃ Edge y x :=
  yonedaEquiv.symm.trans ((pullbackConstHomEquiv x y).trans (edgeEquiv x y))

/-- The edge attached to a vertex `s` of the fibre `{x} ×_L L_{y/}` is the map
`Δ[1] ≅ Δ[0] ⋆ Δ[0] ⟶ L` corresponding to `s`. -/
lemma pullbackConstObj₀Equiv_apply_edge
    (s : (pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) _⦋0⦌) :
    (pullbackConstObj₀Equiv x y s).edge =
      yonedaEquiv ((join.stdSimplexIso 0 0).inv ≫
        (pullbackConstHomEquiv x y (yonedaEquiv.symm s)).1) :=
  (rfl)

/-- If `L` is strict Segal, every simplex of the fibre `{x} ×_L L_{y/}` is totally degenerate: a
map `Δ[0] ⋆ Δ[n] ⟶ L` sending `Δ[n]` to `x` is determined by its edge from the cone point to the
vertex `0`. -/
private lemma surjective_pullback_map_const [L.IsStrictSegal] (n : ℕ) :
    Function.Surjective ((pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))).map
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op) := by
  intro s
  refine ⟨(pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))).map
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s, ?_⟩
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_naturality_left, ← yonedaEquiv_symm_naturality_left,
    ← (pullbackConstHomEquiv x y).apply_eq_iff_eq, Subtype.ext_iff,
    pullbackConstHomEquiv_comp_coe, pullbackConstHomEquiv_comp_coe]
  apply join.hom_ext_of_isStrictSegal
  · -- The vertex `0` is fixed by the operator collapsing `⦋n⦌` onto its vertex `0`.
    rw [← join.map_comp_assoc, ← join.map_comp_assoc, Category.comp_id, Category.comp_id,
      ← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 ≫ SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) (𝟙 _),
      Category.id_comp]
  · rw [join.inr_map_assoc, join.inr_map_assoc, (pullbackConstHomEquiv x y _).2.2, comp_const,
      comp_const]

/-- If `L` is strict Segal, sending an edge from `y` to `x` to the totally degenerate simplices at
the corresponding vertex of the fibre `{x} ×_L L_{y/}` is an isomorphism from the discrete
simplicial set on these edges. -/
instance isIso_constHomEquiv_symm [L.IsStrictSegal] :
    IsIso ((constHomEquiv (Edge y x)).symm (pullbackConstObj₀Equiv x y).symm) :=
  SSet.isIso_constHomEquiv_symm (pullbackConstObj₀Equiv x y).symm.bijective
    (surjective_pullback_map_const x y)

/-- If `L` is strict Segal, for instance the nerve of a category, the fibre `{x} ×_L L_{y/}` over
`y` of the inclusion of the vertex `x` is the discrete simplicial set on the edges from `y`
to `x`. -/
noncomputable def constEdgeIso [L.IsStrictSegal] :
    (Functor.const SimplexCategoryᵒᵖ).obj (Edge y x) ≅
      pullback (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L)) :=
  asIso ((constHomEquiv (Edge y x)).symm (pullbackConstObj₀Equiv x y).symm)

/-- On vertices, the discreteness isomorphism sends an edge from `y` to `x` to the corresponding
vertex of the fibre `{x} ×_L L_{y/}`. -/
@[simp]
lemma constEdgeIso_hom_app_zero [L.IsStrictSegal] (e : Edge y x) :
    dsimp% (constEdgeIso x y).hom.app (op ⦋0⦌) e = (pullbackConstObj₀Equiv x y).symm e :=
  constHomEquiv_symm_app_zero (Edge y x) (pullbackConstObj₀Equiv x y).symm e

end coslice

section IsStrictSegal

variable {L : SSet.{u}} [L.IsStrictSegal]

/-- If `L` is strict Segal, the fibre `{x} ×_L L_{y/}` over `y` of the inclusion of the vertex `x`
is weakly contractible exactly when there is a unique edge from `y` to `x`. -/
theorem isWeaklyContractible_pullback_const_iff (x y : L _⦋0⦌) :
    IsWeaklyContractible (pullback (const x : Δ[0] ⟶ L) (coslice.π (const y : Δ[0] ⟶ L))) ↔
      Nonempty (Unique (Edge y x)) := by
  rw [← isWeaklyContractible_const_iff]
  exact ⟨fun _ ↦ .of_iso (coslice.constEdgeIso x y).symm,
    fun _ ↦ .of_iso (coslice.constEdgeIso x y)⟩

/-- A vertex `x` of a strict Segal simplicial set `L` is final exactly when every vertex of `L` has
a unique edge to `x`. -/
theorem isFinal_const_iff_of_isStrictSegal (x : L _⦋0⦌) :
    IsFinal (const x : Δ[0] ⟶ L) ↔ ∀ y : L _⦋0⦌, Nonempty (Unique (Edge y x)) := by
  simp_rw [isFinal_iff, isWeaklyContractible_pullback_const_iff]

end IsStrictSegal

namespace stdSimplex

/-- A vertex of the standard simplex `Δ[n]` is final exactly when it is the last vertex. -/
theorem isFinal_const_iff {n : ℕ} (i : Fin (n + 1)) :
    IsFinal (SSet.const (obj₀Equiv.{u}.symm i) : Δ[0] ⟶ Δ[n]) ↔ i = Fin.last n := by
  rw [isFinal_const_iff_of_isStrictSegal, obj₀Equiv.forall_congr_left]
  simp only [unique_iff_subsingleton_and_nonempty, nonempty_edge_iff]
  exact ⟨fun h ↦ Fin.last_le_iff.1 (h _).2, fun h j ↦ ⟨inferInstance, h ▸ Fin.le_last j⟩⟩

/-- The inclusion `{1} ⟶ Δ[1]` of the last vertex is final. -/
theorem isFinal_const_one : IsFinal (SSet.const (obj₀Equiv.{u}.symm 1) : Δ[0] ⟶ Δ[1]) :=
  (isFinal_const_iff 1).2 rfl

/-- The inclusion `{0} ⟶ Δ[1]` is not final: its fibre over the vertex `1` is empty. -/
theorem not_isFinal_const_zero : ¬ IsFinal (SSet.const (obj₀Equiv.{u}.symm 0) : Δ[0] ⟶ Δ[1]) :=
  fun h ↦ absurd ((isFinal_const_iff 0).1 h) (by decide)

end stdSimplex

end SSet

namespace CategoryTheory.nerve

open SSet

/-- A vertex of the nerve of a category is final exactly when it is a terminal object. -/
theorem isFinal_const_iff {C : Type u} [Category.{v} C] (x : nerve C _⦋0⦌) :
    IsFinal (const x : Δ[0] ⟶ nerve C) ↔ Nonempty (IsTerminal (nerveEquiv x)) := by
  -- Edges of the nerve are morphisms of `C`, and vertices are objects.
  have e (y : nerve C _⦋0⦌) : Nonempty (Unique (Edge y x)) ↔
      Nonempty (Unique (nerveEquiv y ⟶ nerveEquiv x)) :=
    ⟨fun ⟨_⟩ ↦ ⟨homEquiv.symm.unique⟩, fun ⟨_⟩ ↦ ⟨homEquiv.unique⟩⟩
  rw [isFinal_const_iff_of_isStrictSegal, forall_congr' e]
  exact ⟨fun h ↦ ⟨IsTerminal.ofUniqueHom (fun c ↦ (h (nerveEquiv.symm c)).some.default)
    (fun c m ↦ (h (nerveEquiv.symm c)).some.uniq m)⟩,
    fun ⟨t⟩ _ ↦ ⟨⟨⟨t.from _⟩, fun m ↦ t.hom_ext m _⟩⟩⟩

end CategoryTheory.nerve
