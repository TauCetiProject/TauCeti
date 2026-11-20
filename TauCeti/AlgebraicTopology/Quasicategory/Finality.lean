/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.TerminalVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible
import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits
import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration

/-!
# Final maps of simplicial sets

A map `f : K ⟶ L` is final if `K ×_L L_{y/}` is weakly contractible at every vertex `y` of `L`.
For the inclusion of a terminal vertex, these pullbacks are left mapping spaces with terminal
codomain. They have the right lifting property against every boundary because the pushout-join
of two simplex boundaries is again a simplex boundary.

This is the comma-simplicial-set criterion of J. Lurie, *Higher Topos Theory*, Theorem 4.1.3.1;
for the case of a terminal vertex see Proposition 1.2.12.4 and Corollary 4.1.1.9.
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

variable {K L : SSet.{u}}

/-- A map `f : K ⟶ L` is final when, at every vertex `y` of `L`, the pullback of the coslice
projection `L_{y/} ⟶ L` along `f` is weakly contractible. -/
class IsFinal (f : K ⟶ L) : Prop where
  isWeaklyContractible (y : L _⦋0⦌) :
    IsWeaklyContractible (pullback f (coslice.π (const y : Δ[0] ⟶ L)))

/-- The defining comma-simplicial-set test for finality. -/
lemma isFinal_iff (f : K ⟶ L) :
    IsFinal f ↔ ∀ y : L _⦋0⦌,
      IsWeaklyContractible (pullback f (coslice.π (const y : Δ[0] ⟶ L))) :=
  ⟨fun h ↦ h.isWeaklyContractible, fun h ↦ ⟨h⟩⟩

namespace coslice

/-- A boundary of cones on `y` with base constant at a terminal vertex `x` extends to a cone
with the same constant base. -/
private lemma extend_const_cone {x y : L _⦋0⦌} (hx : L.IsTerminalVertex x) {n : ℕ}
    (a : join (Δ[0] : SSet.{u}) (∂Δ[n] : SSet.{u}) ⟶ L)
    (ha₀ : join.inl _ _ ≫ a = const y) (ha₁ : join.inr _ _ ≫ a = const x) :
    ∃ b : join (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ L,
      join.inl _ _ ≫ b = const y ∧ join.inr _ _ ≫ b = const x ∧
        join.map (𝟙 _) ∂Δ[n].ι ≫ b = a := by
  let P := Subcomplex.unionJoin (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) ∂Δ[n]
  let hP := Subcomplex.unionJoin.isPushout (∂Δ[0] : (Δ[0] : SSet.{u}).Subcomplex) ∂Δ[n]
  have he := join.preimage_unionJoin_boundary_boundary_coneIso.{u} n
  let e := Subcomplex.isoOfPreimageEq (join.coneIso n) he
  -- Glue the given boundary of cones to the constant base facet.
  have hEmpty : ¬ (∂Δ[0] : SSet.{u}).Nonempty := by simp [boundary_zero]
  have := join.isIso_inr (L := (∂Δ[n] : SSet.{u})) hEmpty
  have hcompat : join.map (𝟙 (∂Δ[0] : SSet.{u})) ∂Δ[n].ι ≫ const x =
      join.map ∂Δ[0].ι (𝟙 _) ≫ a := by
    rw [← cancel_epi (join.inr (∂Δ[0] : SSet.{u}) (∂Δ[n] : SSet.{u}))]
    simp [ha₁]
  let d : (P : SSet.{u}) ⟶ L := hP.desc (const x) a hcompat
  have hbase : boundary.ι (0 : Fin (n + 2)) ≫ e.inv ≫ d = (const x : Δ[n] ⟶ L) := by
    have h : boundary.ι (0 : Fin (n + 2)) ≫ e.inv =
        join.inr _ _ ≫ Subcomplex.unionJoin.ι₁ ∂Δ[0] ∂Δ[n] := by
      rw [← cancel_mono P.ι]
      simp [P, e, Subcomplex.unionJoin.ι₁_ι]
    rw [reassoc_of% h, hP.inl_desc]
    simp
  obtain ⟨σ, hσ⟩ := (isTerminalVertex_iff x).1 hx (e.inv ≫ d) (by
    simp only [hbase, yonedaEquiv_naturality, comp_const, yonedaEquiv_const])
  let b := (join.coneIso n).hom ≫ σ
  have hb : P.ι ≫ b = d := by
    dsimp only [b]
    rw [← Subcomplex.isoOfPreimageEq_hom_ι_assoc _ he, ← hσ]
    simp [e]
  have hrest : join.map (𝟙 _) ∂Δ[n].ι ≫ b = a := by
    rw [← Subcomplex.unionJoin.ι₂_ι, Category.assoc, hb, hP.inr_desc]
  refine ⟨b, ?_, ?_, hrest⟩
  · simpa using (congrArg (join.inl _ _ ≫ ·) hrest).trans ha₀
  · dsimp only [b]
    rw [join.inr_comp_coneIso_hom_assoc, ← boundary.ι_ι, Category.assoc, ← hσ]
    exact hbase

/-- The left mapping space into a terminal vertex has a trivial fibration to the point. -/
theorem rlp_monomorphisms_fst_of_isTerminalVertex {x y : L _⦋0⦌} (hx : L.IsTerminalVertex x) :
    (monomorphisms SSet.{u}).rlp
      (pullback.fst (const x : Δ[0] ⟶ L) (π (const y : Δ[0] ⟶ L))) := by
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  refine ⟨fun {a b} _ ↦ ?_⟩
  let a' := pullbackConstHomEquiv x y a
  obtain ⟨c, hc₀, hc₁, hc⟩ := extend_const_cone hx a'.1 a'.2.1 a'.2.2
  refine ⟨⟨(pullbackConstHomEquiv x y).symm ⟨c, hc₀, hc₁⟩, ?_, stdSimplex.ext₀⟩⟩
  apply (pullbackConstHomEquiv x y).injective
  apply Subtype.ext
  simpa using hc

end coslice

/-- The inclusion of a terminal vertex is final. No quasicategory hypothesis is needed for
this implication. -/
theorem IsTerminalVertex.isFinal_const {x : L _⦋0⦌} (hx : L.IsTerminalVertex x) :
    IsFinal (const x : Δ[0] ⟶ L) where
  isWeaklyContractible y := by
    let f := pullback.fst (const x : Δ[0] ⟶ L) (coslice.π (const y : Δ[0] ⟶ L))
    have hf := coslice.rlp_monomorphisms_fst_of_isTerminalVertex (y := y) hx
    let := isSplitEpi_of_rlp_monomorphisms hf
    obtain ⟨H, -⟩ := exists_homotopy_of_rlp_monomorphisms hf (f ≫ section_ f) (𝟙 _) stdSimplex.ext₀
    have he : f ≫ section_ f = const ((section_ f).app _ (stdSimplex.obj₀Equiv.symm 0)) := by
      rw [← const_comp]
      exact congrArg (· ≫ section_ f) stdSimplex.ext₀
    rw [he] at H
    exact IsWeaklyContractible.of_homotopy H

/-- When `L` is strict Segal, the inclusion of `x` is final exactly when each vertex has a
unique edge to `x`: in this case the comma simplicial sets are discrete. -/
theorem isFinal_const_iff_of_isStrictSegal [L.IsStrictSegal] (x : L _⦋0⦌) :
    IsFinal (const x : Δ[0] ⟶ L) ↔ ∀ y : L _⦋0⦌, Nonempty (Unique (Edge y x)) := by
  rw [isFinal_iff]
  refine forall_congr' fun y ↦ ?_
  let e := coslice.constEdgeIso x y
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (isWeaklyContractible_const_iff _).1 (IsWeaklyContractible.of_iso e.symm)
  · have := (isWeaklyContractible_const_iff _).2 h
    exact IsWeaklyContractible.of_iso e

namespace stdSimplex

/-- The last vertex of a standard simplex is final. -/
theorem isFinal_const_last (n : ℕ) :
    IsFinal (SSet.const (obj₀Equiv.symm (Fin.last n)) : Δ[0] ⟶ Δ[n]) :=
  (isTerminalVertex_last n).isFinal_const

/-- The first vertex of a positive-dimensional standard simplex is not final: there is no edge
from the last vertex to the first. -/
theorem not_isFinal_const_zero (n : ℕ) :
    ¬ IsFinal (SSet.const (obj₀Equiv.symm 0) : Δ[0] ⟶ Δ[n + 1]) := by
  intro h
  obtain ⟨h⟩ := (isFinal_const_iff_of_isStrictSegal _).1 h (obj₀Equiv.symm (Fin.last (n + 1)))
  have hle := (nonempty_edge_iff (Fin.last (n + 1)) 0).1 ⟨h.default⟩
  simp at hle

end stdSimplex

end SSet
