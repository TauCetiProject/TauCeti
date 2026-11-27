/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.TerminalVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration.Fiber

/-!
# Final maps of simplicial sets

A map `f : K ⟶ L` of simplicial sets is *final* (`SSet.IsFinal`) if, for every vertex `y` of `L`,
the fibre product `K ×_L L_{y/}` of `f` with the projection from the coslice under `y` is weakly
contractible (`SSet.IsWeaklyContractible`). For `L` a quasicategory, Joyal's Theorem A (HTT
Theorem 4.1.3.1) identifies these maps with Lurie's cofinal maps (HTT Definition 4.1.1.1), along
which restriction of cocones is a categorical equivalence (HTT Proposition 4.1.1.8), so that
restricting a diagram along a final map does not change its colimits. Neither comparison is proved
here.

Since weakly contractible simplicial sets are nonempty, a final map is in particular reachable from
every vertex: for every vertex `y` of `L` there is an edge from `y` to a vertex in the image of `f`
(`SSet.IsFinal.exists_edge`).

The basic example is the inclusion of a terminal vertex. If `x` is a terminal vertex of `L`, then
for every vertex `y` the map to the point from the fibre `{x} ×_L L_{y/}`, the left mapping space
from `y` to `x`, is a trivial fibration (`SSet.IsTerminalVertex.rlp_monomorphisms_pullback_const`),
so that this fibre is a contractible Kan complex. Indeed, a map from `∂Δ[n]` to the fibre is a map
`Δ[0] ⋆ ∂Δ[n] ⟶ L` sending the cone point to `y` and `∂Δ[n]` to `x`. It glues with the constant
map at `x` on `Δ[n]` to a map from `(∂Δ[0] ⋆ Δ[n]) ∪ (Δ[0] ⋆ ∂Δ[n]) ≅ ∂Δ[n + 1]`
(`SSet.join.preimage_unionJoin_boundary_boundary`) whose last vertex is `x`, and terminality
extends it to `Δ[n + 1] ≅ Δ[0] ⋆ Δ[n]`. Hence the inclusion of a terminal vertex is final
(`SSet.IsTerminalVertex.isFinal_const`); for instance the inclusion of the vertex `n` into `Δ[n]`
is final (`SSet.stdSimplex.isFinal_const_last`). The inclusion of the vertex `0` into `Δ[1]` is not
(`SSet.stdSimplex.not_isFinal_const_zero`): there is no edge from `1` to `0`, so the fibre over
the vertex `1` is empty.

## Main declarations

* `SSet.IsFinal f`: the map `f` is final.
* `SSet.IsFinal.exists_edge`: every vertex has an edge to a vertex in the image of a final map.
* `SSet.IsTerminalVertex.rlp_monomorphisms_pullback_const`,
  `SSet.IsTerminalVertex.isWeaklyContractible_pullback_const`: the map to the point from a left
  mapping space into a terminal vertex is a trivial fibration, so this space is weakly
  contractible.
* `SSet.IsTerminalVertex.isFinal_const`: the inclusion of a terminal vertex is final.
* `SSet.stdSimplex.isFinal_const_last`, `SSet.stdSimplex.not_isFinal_const_zero`: the inclusion of
  the last vertex of `Δ[n]` is final, and that of the vertex `0` of `Δ[1]` is not.

## References

* J. Lurie, *Higher Topos Theory*, Definition 4.1.1.1, Proposition 4.1.1.8 and Theorem 4.1.3.1.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty Simplicial

namespace SSet

variable {K L : SSet.{u}}

/-- A map `f : K ⟶ L` of simplicial sets is *final* if, for every vertex `y` of `L`, the fibre
product `K ×_L L_{y/}` of `f` with the projection from the coslice under `y` is weakly
contractible. -/
def IsFinal (f : K ⟶ L) : Prop :=
  ∀ y : L _⦋0⦌, IsWeaklyContractible (pullback f (coslice.π (const y : Δ[0] ⟶ L)))

/-- Unfolding `SSet.IsFinal`: `f` is final when all fibres `K ×_L L_{y/}` are weakly
contractible. -/
lemma isFinal_iff (f : K ⟶ L) :
    IsFinal f ↔ ∀ y : L _⦋0⦌, IsWeaklyContractible (pullback f (coslice.π (const y : Δ[0] ⟶ L))) :=
  Iff.rfl

/-- For a final map `f : K ⟶ L`, every vertex `y` of `L` has an edge to a vertex in the image of
`f`: the fibre `K ×_L L_{y/}` is nonempty, and its vertices are the edges from `y` to vertices
`f k`. -/
lemma IsFinal.exists_edge {f : K ⟶ L} (hf : IsFinal f) (y : L _⦋0⦌) :
    ∃ k : K _⦋0⦌, Nonempty (L.Edge y (f.app _ k)) := by
  have := hf y
  obtain ⟨v⟩ := IsWeaklyContractible.nonempty (K := pullback f (coslice.π (const y : Δ[0] ⟶ L)))
  -- The vertex `v` of the fibre is a vertex `k` of `K` and a cocone `Δ[0] ⋆ Δ[0] ⟶ L` under `y`
  -- whose cone point is `f k`.
  let s : (coslice (const y : Δ[0] ⟶ L)) _⦋0⦌ :=
    (pullback.snd f (coslice.π (const y : Δ[0] ⟶ L))).app _ v
  have hs : f.app _ ((pullback.fst f _).app _ v) = (coslice.π (const y : Δ[0] ⟶ L)).app _ s :=
    ConcreteCategory.congr_hom (congr_app (pullback.condition (f := f)) _) v
  refine ⟨(pullback.fst f _).app _ v, ⟨(join.coneEdgeEquiv _ y ⟨(coslice.objEquiv s).val,
    (coslice.objEquiv s).property, ?_⟩).ofEq rfl hs.symm⟩⟩
  rw [coslice.π_app (p := const y) s]
  exact (yonedaEquiv.symm_apply_apply _).symm.trans (yonedaEquiv_symm_zero _)

/-- Under `Δ[0] ⋆ Δ[n] ≅ Δ[0 + n + 1]`, the last vertex of the face opposite to `0` is the last
vertex of the base `Δ[n]`. -/
private lemma const_last_comp_δ_zero (n : ℕ) :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0 + n⦌ (Fin.last _)) ≫ stdSimplex.δ 0 =
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ join.inr Δ[0] Δ[n] ≫
        (join.stdSimplexIso.{u} 0 n).hom := by
  apply yonedaEquiv.injective
  refine stdSimplex.ext _ _ fun i ↦ ?_
  rw [stdSimplex.yonedaEquiv_comp_apply, stdSimplex.yonedaEquiv_comp_apply,
    join.yonedaEquiv_inr_comp_stdSimplexIso_hom]
  ext
  simp [CosimplicialObject.δ, SimplexCategory.δ]
  omega

namespace IsTerminalVertex

variable {x : L _⦋0⦌}

/-- A map `Δ[0] ⋆ ∂Δ[n] ⟶ L` sending `∂Δ[n]` to a terminal vertex `x` extends to a map
`Δ[0] ⋆ Δ[n] ⟶ L` sending `Δ[n]` to `x`. -/
private lemma exists_extension (hx : L.IsTerminalVertex x) {n : ℕ} (τ : join Δ[0] ∂Δ[n] ⟶ L)
    (hτ : join.inr _ _ ≫ τ = const x) :
    ∃ σ : join Δ[0] Δ[n] ⟶ L, join.map (𝟙 _) ∂Δ[n].ι ≫ σ = τ ∧ join.inr _ _ ≫ σ = const x := by
  let U := Subcomplex.unionJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) ∂Δ[n]
  -- Glue `τ` with the constant map at `x` on `∂Δ[0] ⋆ Δ[n] ≅ Δ[n]`.
  have hc : join.map (𝟙 _) ∂Δ[n].ι ≫ (const x : join ∂Δ[0] Δ[n] ⟶ L) =
      join.map ∂Δ[0].ι (𝟙 _) ≫ τ := by
    have := join.isIso_inr (L := ∂Δ[n]) not_nonempty_boundary_zero
    rw [comp_const, ← cancel_epi (join.inr _ _), join.inr_map_assoc, Category.id_comp, hτ,
      comp_const]
  let g : (U : SSet.{u}) ⟶ L := (Subcomplex.unionJoin.isPushout _ _).desc (const x) τ hc
  have hg₁ : Subcomplex.unionJoin.ι₁ _ _ ≫ g = const x :=
    (Subcomplex.unionJoin.isPushout _ _).inl_desc _ _ _
  have hg₂ : Subcomplex.unionJoin.ι₂ _ _ ≫ g = τ :=
    (Subcomplex.unionJoin.isPushout _ _).inr_desc _ _ _
  -- Under `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, the union `U` is the boundary `∂Δ[n + 1]`.
  let e := join.stdSimplexIso.{u} 0 n
  have hU : U.preimage e.inv = ∂Δ[0 + n + 1] := join.preimage_unionJoin_boundary_boundary 0 n
  let i := Subcomplex.isoOfPreimageEq e hU
  -- The last vertex of `∂Δ[0 + n + 1]` is the last vertex `n` of `∂Δ[0] ⋆ Δ[n] ≅ Δ[n]`.
  have hv :
      stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0 + n⦌ (Fin.last _)) ≫ boundary.ι 0 ≫ i.inv =
      (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ join.inr _ _) ≫
        Subcomplex.unionJoin.ι₁ _ _ := by
    rw [← cancel_mono U.ι, ← cancel_mono e.hom]
    simp only [U, i, Category.assoc, Subcomplex.isoOfPreimageEq_inv_ι, boundary.ι_ι_assoc,
      Iso.inv_hom_id, Category.comp_id, Subcomplex.unionJoin.ι₁_ι_assoc, join.inr_map_assoc,
      Category.id_comp]
    exact const_last_comp_δ_zero n
  obtain ⟨σ', hσ'⟩ := (isTerminalVertex_iff x).1 hx (i.inv ≫ g) (by
    rw [yonedaEquiv_naturality, reassoc_of% hv, hg₁, comp_const, comp_const, yonedaEquiv_const])
  have key : U.ι ≫ e.hom ≫ σ' = g := by
    rw [← Subcomplex.isoOfPreimageEq_hom_ι_assoc e hU, ← hσ', i.hom_inv_id_assoc]
  refine ⟨e.hom ≫ σ', ?_, ?_⟩
  · rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, key, hg₂]
  · have hinr : join.inr Δ[0] Δ[n] = join.inr ∂Δ[0] Δ[n] ≫ Subcomplex.unionJoin.ι₁ _ _ ≫ U.ι := by
      rw [Subcomplex.unionJoin.ι₁_ι, join.inr_map, Category.id_comp]
    rw [hinr, Category.assoc, Category.assoc, key, hg₁, comp_const]

variable (hx : L.IsTerminalVertex x) (y : L _⦋0⦌)
include hx

/-- The map to the point from the left mapping space `{x} ×_L L_{y/}` into a terminal vertex `x`
has the right lifting property with respect to all monomorphisms: a map `Δ[0] ⋆ ∂Δ[n] ⟶ L` sending
the cone point to `y` and `∂Δ[n]` to `x` extends to `Δ[0] ⋆ Δ[n]`, still sending `Δ[n]` to `x`. -/
lemma rlp_monomorphisms_pullback_const :
    (monomorphisms SSet.{u}).rlp (stdSimplex.isTerminalObj₀.from
      (pullback (const x : Δ[0] ⟶ L) (coslice.π (const y : Δ[0] ⟶ L)))) := by
  rw [SSet.rlp_monomorphisms]
  refine fun _ _ _ ⟨n⟩ ↦ ⟨fun {a _} _ ↦ ?_⟩
  let τ := coslice.pullbackConstHomEquiv x y a
  obtain ⟨σ, hσ, hσx⟩ := exists_extension hx τ.val τ.property.2
  have hσy : join.inl _ _ ≫ σ = const y := by
    have h : join.inl Δ[0] Δ[n] = join.inl _ _ ≫ join.map (𝟙 _) ∂Δ[n].ι := by
      rw [join.inl_map, Category.id_comp]
    rw [h, Category.assoc, hσ, τ.property.1]
  refine ⟨⟨⟨(coslice.pullbackConstHomEquiv x y).symm ⟨σ, hσy, hσx⟩, ?_,
    stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩⟩
  apply (coslice.pullbackConstHomEquiv x y).injective
  rw [Subtype.ext_iff, coslice.pullbackConstHomEquiv_comp_coe, Equiv.apply_symm_apply]
  exact hσ

/-- The left mapping space `{x} ×_L L_{y/}` from any vertex `y` to a terminal vertex `x` is weakly
contractible. -/
lemma isWeaklyContractible_pullback_const :
    IsWeaklyContractible (pullback (const x : Δ[0] ⟶ L) (coslice.π (const y : Δ[0] ⟶ L))) :=
  ((rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal
    stdSimplex.isTerminalObj₀ _).1 (hx.rlp_monomorphisms_pullback_const y)).2

omit y in
/-- The inclusion `Δ[0] ⟶ L` of a terminal vertex is final. -/
lemma isFinal_const : IsFinal (const x : Δ[0] ⟶ L) :=
  hx.isWeaklyContractible_pullback_const

end IsTerminalVertex

namespace stdSimplex

/-- The inclusion of the last vertex `n` into `Δ[n]` is final, since that vertex is terminal. -/
lemma isFinal_const_last (n : ℕ) :
    IsFinal (SSet.const (obj₀Equiv.symm (Fin.last n)) : Δ[0] ⟶ (Δ[n] : SSet.{u})) :=
  (isTerminalVertex_last n).isFinal_const

/-- The inclusion of the vertex `0` into `Δ[1]` is not final: there is no edge from the vertex `1`
to the vertex `0`. -/
lemma not_isFinal_const_zero :
    ¬ IsFinal (SSet.const (obj₀Equiv.symm 0) : Δ[0] ⟶ (Δ[1] : SSet.{u})) := by
  intro h
  obtain ⟨k, he⟩ := h.exists_edge (obj₀Equiv.symm 1)
  simp only [const_app, SimplexCategory.const_eq_id, op_id, CategoryTheory.Functor.map_id,
    TypeCat.ofHom_apply, ConcreteCategory.id_apply, nonempty_edge_iff] at he
  exact absurd he (by decide)

end stdSimplex

end SSet
