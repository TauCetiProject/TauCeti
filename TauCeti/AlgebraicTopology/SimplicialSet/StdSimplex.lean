/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.Data.Finset.Sort

/-!
# Complements on standard simplices

A map of simplicial sets `q : Δ[m] ⟶ Δ[n]` is determined by its vertex map, the `m`-simplex
`yonedaEquiv q` of `Δ[n]`, and it acts on the simplices of `Δ[m]` by composing with it. Standard
simplices are nerves of finite linear orders, hence quasicategories. These facts let one handle
maps from horns and simplices to `Δ[n]`, for instance to `Δ[1]` when splitting a simplex into
an initial and a final segment.

An injective `m`-simplex of `Δ[n]` is the increasing enumeration of its set of vertices, and the
faces of the increasing enumeration of a set `J` enumerate the sets `J` with one element removed.

## Main results

* `SSet.stdSimplex.hom_app_apply`: the vertices of the image of a simplex under a map of standard
  simplices.
* `SSet.stdSimplex.const_app_apply`: the constant map at a vertex of `Δ[n]` sends every simplex
  to the constant simplex at that vertex.
* `SSet.stdSimplex.δ_objMk_orderEmbOfFin`: the faces of the increasing enumeration of a set of
  vertices.
* `SSet.stdSimplex.objMk_orderEmbOfFin_image`: an injective simplex is the increasing enumeration
  of its set of vertices.
* `SSet.stdSimplex.quasicategory`: standard simplices are quasicategories.
* `SSet.horn_one_ι_eq_const`: each horn `Λ[1, i]` of `Δ[1]` is the vertex `i`.
-/

public section

open CategoryTheory Finset Opposite Simplicial

universe u

namespace SSet.stdSimplex

/-- A map of standard simplices `q : Δ[m] ⟶ Δ[n]` sends a simplex `x` of `Δ[m]` to the simplex
whose `j`-th vertex is the image of the `j`-th vertex of `x` under the vertex map of `q`. -/
lemma hom_app_apply {m n d : ℕ} (q : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (x : Δ[m] _⦋d⦌)
    (j : Fin (d + 1)) : q.app _ x j = yonedaEquiv q (x j) := by
  conv_lhs => rw [← yonedaEquiv.symm_apply_apply q]
  -- The map `yonedaEquiv.symm s` acts on `x` by precomposing `s` with `x`.
  rfl

/-- The constant map at the vertex `e` of `Δ[n]` sends every simplex to a simplex all of whose
vertices are `e`. -/
lemma const_app_apply {X : SSet.{u}} {n d : ℕ} (e : Fin (n + 1)) (x : X _⦋d⦌)
    (j : Fin (d + 1)) : (SSet.const (stdSimplex.const n e _) : X ⟶ Δ[n]).app _ x j = e :=
  (rfl)

/-- The `i`-th face of the simplex of `Δ[n]` enumerating a set `J` of vertices in increasing order
enumerates `J` with its `i`-th smallest element removed. -/
lemma δ_objMk_orderEmbOfFin {n m : ℕ} (J : Finset (Fin (n + 1))) (h : #J = m + 2)
    (i : Fin (m + 2)) :
    (Δ[n] : SSet.{u}).δ i (objMk (m := op ⦋m + 1⦌) (J.orderEmbOfFin h).toOrderHom) =
      objMk (m := op ⦋m⦌) ((J.erase (J.orderEmbOfFin h i)).orderEmbOfFin
        (by rw [card_erase_of_mem (J.orderEmbOfFin_mem h i), h]; rfl)).toOrderHom := by
  refine ext _ _ fun k ↦ ?_
  rw [δ_apply, objMk_apply, objMk_apply]
  exact congrFun (orderEmbOfFin_unique
    (by rw [card_erase_of_mem (J.orderEmbOfFin_mem h i), h]; rfl)
    (f := fun k ↦ J.orderEmbOfFin h (i.succAbove k))
    (fun k ↦ mem_erase.2 ⟨fun hk ↦ i.succAbove_ne k ((J.orderEmbOfFin h).injective hk),
      J.orderEmbOfFin_mem h _⟩)
    ((J.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i))) k

/-- A simplex `x` of `Δ[n]` whose vertices are pairwise distinct, that is whose set of vertices has
`m + 1` elements, enumerates its set of vertices in increasing order. -/
lemma objMk_orderEmbOfFin_image {n m : ℕ} (x : (Δ[n] : SSet.{u}) _⦋m⦌)
    (h : #(univ.image x) = m + 1) :
    objMk (m := op ⦋m⦌) ((univ.image x).orderEmbOfFin h).toOrderHom = x := by
  have hx : Function.Injective x :=
    Set.injOn_univ.1 (by simpa using card_image_iff.1 (h.trans (by simp)))
  refine ext _ _ fun k ↦ ?_
  rw [objMk_apply]
  exact (congrFun (orderEmbOfFin_unique h (f := x) (fun k ↦ mem_image_of_mem _ (mem_univ k))
    ((monotone_apply x).strictMono_of_injective hx)) k).symm

/-- Standard simplices are quasicategories, being isomorphic to nerves of linear orders. -/
instance quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) where
  hornFilling' _ _ σ₀ h₀ hₙ := by
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling' (σ₀ ≫ (isoNerve n).hom) h₀ hₙ
    exact ⟨σ ≫ (isoNerve n).inv, by rw [← Category.assoc, ← hσ]; simp⟩

end SSet.stdSimplex

namespace SSet

/-- The horn `Λ[1, i]` is the vertex `i` of `Δ[1]`: every simplex of it is constant at `i`. -/
lemma horn_one_ι_eq_const (i : Fin 2) : Λ[1, i].ι = const (stdSimplex.obj₀Equiv.{u}.symm i) := by
  ext ⟨n⟩ x
  induction n using SimplexCategory.rec with | _ n
  obtain ⟨σ, hσ⟩ := x
  refine stdSimplex.ext _ _ fun k ↦ ?_
  rw [mem_horn_iff_notMem_range] at hσ
  obtain ⟨j, hj, hj'⟩ := hσ
  have hk : σ k ≠ j := fun h ↦ hj' ⟨k, h⟩
  rw [stdSimplex.obj₀Equiv_symm_apply]
  -- The inclusion `Λ[1, i].ι` sends `⟨σ, hσ⟩` to `σ`.
  exact (by omega : σ k = i).trans (stdSimplex.const_app_apply i _ k).symm

end SSet
