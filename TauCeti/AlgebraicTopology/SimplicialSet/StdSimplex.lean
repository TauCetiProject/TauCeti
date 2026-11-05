/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
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
* `SSet.stdSimplex.subcomplex_hom_app_apply`: the vertices of the image of a simplex under a map
  from a subcomplex of a standard simplex to a standard simplex.
* `SSet.stdSimplex.hom_app_obj₀Equiv_symm`: a map `g` of standard simplices sends the vertex `j`
  to the vertex `yonedaEquiv g j`.
* `SSet.stdSimplex.quasicategory`: standard simplices are quasicategories.
* `SSet.stdSimplex.isConnected`: standard simplices are connected.
* `SSet.stdSimplex.contraction`: the homotopy from the constant map at the initial vertex of
  `Δ[n]` to its identity.
* `SSet.horn_one_ι_eq_const`: each horn `Λ[1, i]` of `Δ[1]` is the vertex `i`.
* `SSet.boundary.isConnected`: the boundary `∂Δ[n + 2]` is connected.
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

/-- The vertex map `asOrderHom x` of a simplex `x` of `Δ[n]` evaluates like `x` itself: both are
the vertex function of the morphism `objEquiv x : ⦋d⦌ ⟶ ⦋n⦌` of the simplex category. -/
@[simp]
lemma coe_asOrderHom {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) : ⇑(asOrderHom x) = ⇑x :=
  rfl

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

/-- The top simplex of `Δ[n]`, corresponding to its identity map, has `j` as its `j`-th vertex. -/
@[simp]
lemma yonedaEquiv_id_apply (n : ℕ) (j : Fin (n + 1)) : yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) j = j :=
  (rfl)

/-- The constant simplex at the vertex `k` of `Δ[n]` has all its vertices equal to `k`. -/
@[simp]
lemma const_apply (n : ℕ) (k : Fin (n + 1)) (d : ℕ) (t : Fin (d + 1)) :
    stdSimplex.const n k (op ⦋d⦌) t = k :=
  (rfl)

/-- The vertices of the image of a simplex `x` of `Δ[n]` under a simplicial operator `f` are the
vertices of `x` indexed through `f`. -/
@[simp]
lemma obj_map_apply {n d d' : ℕ} (f : op ⦋d⦌ ⟶ op ⦋d'⦌) (x : Δ[n] _⦋d⦌) (j : Fin (d' + 1)) :
    Δ[n].map f x j = x (f.unop.toOrderHom j) :=
  (rfl)

/-- The edge of `Δ[n]` from `a` to `b` starts at `a`. -/
@[simp]
lemma edge_apply_zero (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : edge n a b hab 0 = a :=
  (rfl)

/-- The edge of `Δ[n]` from `a` to `b` ends at `b`. -/
@[simp]
lemma edge_apply_one (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : edge n a b hab 1 = b :=
  (rfl)

/-- A map `g` from a subcomplex `S` of `Δ[d]` to `Δ[n]` acts on vertices: the `t`-th vertex of the
image of a simplex `x` of `S` is the image of the `t`-th vertex of `x`. -/
lemma subcomplex_hom_app_apply {d n a : ℕ} {S : (Δ[d] : SSet.{u}).Subcomplex}
    (g : (S : SSet.{u}) ⟶ Δ[n]) (x : Δ[d] _⦋a⦌) (hx : x ∈ S.obj _) (t : Fin (a + 1))
    (ht : obj₀Equiv.symm (x t) ∈ S.obj (op ⦋0⦌)) :
    g.app _ ⟨x, hx⟩ t = g.app _ ⟨obj₀Equiv.symm (x t), ht⟩ 0 := by
  have h : (⟨obj₀Equiv.symm (x t), ht⟩ : S.obj (op ⦋0⦌)) =
      (S : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋a⦌ t).op ⟨x, hx⟩ :=
    Subtype.ext (stdSimplex.ext _ _ fun _ ↦ by simp)
  rw [h, NatTrans.naturality_apply, obj_map_apply]
  simp

/-- The simplex of `X` corresponding to a map `f : Δ[n] ⟶ X` is the image under `f` of the top
simplex of `Δ[n]`. -/
lemma yonedaEquiv_eq_app_id {X : SSet.{u}} {n : ℕ} (f : Δ[n] ⟶ X) :
    yonedaEquiv f = f.app _ (yonedaEquiv (𝟙 Δ[n])) := by
  rw [← yonedaEquiv_comp, Category.id_comp]

/-- A map of standard simplices `g : Δ[d'] ⟶ Δ[d]` sends the vertex `j` of `Δ[d']` to the vertex
`yonedaEquiv g j` of `Δ[d]`. -/
lemma hom_app_obj₀Equiv_symm {d d' : ℕ} (g : (Δ[d'] : SSet.{u}) ⟶ Δ[d]) (j : Fin (d' + 1)) :
    g.app _ (obj₀Equiv.symm j) = obj₀Equiv.symm (yonedaEquiv g j) :=
  stdSimplex.ext _ _ fun t ↦ by
    rw [hom_app_apply, obj₀Equiv_symm_apply, const_apply, obj₀Equiv_symm_apply, const_apply]

/-- Standard simplices are quasicategories, being isomorphic to nerves of linear orders. -/
instance quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) where
  hornFilling' _ _ σ₀ h₀ hₙ := by
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling' (σ₀ ≫ (isoNerve n).hom) h₀ hₙ
    exact ⟨σ ≫ (isoNerve n).inv, by rw [← Category.assoc, ← hσ]; simp⟩

/-- Standard simplices are connected: the edge from `0` to `k` joins every vertex `k` to the
initial vertex. -/
instance isConnected (n : ℕ) : (Δ[n] : SSet.{u}).IsConnected where
  allEq := π₀.rec fun x ↦ π₀.rec fun y ↦ by
    suffices h : ∀ k : Fin (n + 1), π₀.mk (obj₀Equiv.symm k) = π₀.mk (obj₀Equiv.symm 0) by
      rw [← obj₀Equiv.symm_apply_apply x, ← obj₀Equiv.symm_apply_apply y]
      exact (h _).trans (h _).symm
    intro k
    exact (π₀.sound (Edge.mk (x₀ := obj₀Equiv.symm 0) (x₁ := obj₀Equiv.symm k)
      (edge.{u} n 0 k (Fin.zero_le k)) (ext _ _ fun i ↦ by fin_cases i; rfl)
      (ext _ _ fun i ↦ by fin_cases i; rfl))).symm

/-- The contraction of the standard simplex `Δ[n]` onto its initial vertex: the homotopy from the
constant map at `0` to the identity which is `0` over the vertex `0` of `Δ[1]` and the identity
over the vertex `1`. -/
noncomputable def contraction (n : ℕ) :
    Homotopy (SSet.const (obj₀Equiv.symm 0)) (𝟙 Δ[n]) where
  h :=
    { app m := ↾fun p ↦ objMk
        ⟨fun k ↦ if asOrderHom p.2 k = 0 then 0 else asOrderHom p.1 k,
          fun k l hkl ↦ by
            dsimp only
            split_ifs with hk hl hl
            · exact le_rfl
            · exact Fin.zero_le _
            · exact absurd (Fin.le_zero_iff.1 (hl ▸ (asOrderHom p.2).monotone hkl)) hk
            · exact (asOrderHom p.1).monotone hkl⟩
      -- The formula is computed vertexwise, so it commutes with reindexing by definition.
      naturality m m' φ := by
        ext p
        rfl }
  -- Over the vertex `0` of `Δ[1]` every vertex is sent to `0`, and over `1` it is unchanged.
  h₀ := by
    ext ⟨⟨m⟩⟩ p
    rfl
  h₁ := by
    ext ⟨⟨m⟩⟩ p
    rfl
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

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

/-- The boundary `∂Δ[n + 2]` is connected: it contains every edge of `Δ[n + 2]`, in particular
the edge from `0` to each vertex. -/
instance boundary.isConnected (n : ℕ) : (∂Δ[n + 2] : SSet.{u}).IsConnected where
  nonempty := ⟨⟨stdSimplex.obj₀Equiv.symm 0, by simp [boundary_obj_eq_univ]⟩⟩
  allEq := π₀.rec fun x ↦ π₀.rec fun y ↦ by
    -- Every vertex and every edge of `Δ[n + 2]` lies in its boundary.
    let v (k : Fin (n + 3)) : (∂Δ[n + 2] : SSet.{u}) _⦋0⦌ :=
      ⟨stdSimplex.obj₀Equiv.symm k, by simp [boundary_obj_eq_univ]⟩
    suffices h : ∀ k, π₀.mk (v k) = π₀.mk (v 0) by
      have hv (z : (∂Δ[n + 2] : SSet.{u}) _⦋0⦌) : z = v (stdSimplex.obj₀Equiv z.1) :=
        Subtype.ext (stdSimplex.obj₀Equiv.symm_apply_apply _).symm
      rw [hv x, hv y]
      exact (h _).trans (h _).symm
    intro k
    exact (π₀.sound (Edge.mk (x₀ := v 0) (x₁ := v k)
      ⟨stdSimplex.edge.{u} _ 0 k (Fin.zero_le k), by simp [boundary_obj_eq_univ]⟩
      (Subtype.ext (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl))
      (Subtype.ext (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)))).symm

end SSet
