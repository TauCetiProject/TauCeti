/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Graphs of groups

A graph of groups `𝔸` over a Serre graph `Γ` attaches a group `A_v` to each vertex `v`, a group
`A_e` to each dart `e` with `A_{rev e} = A_e`, and to each dart an injective homomorphism
`ω_e : A_e →* A_{tgt e}`. The other boundary monomorphism of `e` is `α_e := ω_{rev e}`, into
`A_{src e}`. Loops and parallel edges are allowed, and no finiteness is assumed.

Graphs of groups are the data from which the fundamental group of a splitting and its Bass–Serre
tree are built. The one-edge examples are `GraphOfGroups.segment`, the data of an amalgamated
product `A ∗_C B`, and `GraphOfGroups.loop`, the data of an HNN extension.

The equality `A_{rev e} = A_e` is built in by indexing the edge groups by the geometric edges
`SerreGraph.GeomEdge` of `Γ`. Only the monomorphisms `ω` are data, so `α` and `ω` cannot disagree
across reversal: `α_rev_apply` and `ω_rev_apply` identify `α_{rev e}` with `ω_e` and `ω_{rev e}`
with `α_e`. Since `rev (rev e)` and `e` are only propositionally equal, these identifications go
through Mathlib's `MulEquiv.cast` along equalities of indices.

## Main definitions

* `TauCeti.GraphOfGroups`: a graph of groups over a Serre graph.
* `TauCeti.GraphOfGroups.α`: the boundary monomorphism `α_e : A_e →* A_{src e}`.
* `TauCeti.GraphOfGroups.segment`: the graph of groups of an amalgamated product.
* `TauCeti.GraphOfGroups.loop`: the graph of groups of an HNN extension.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.4, Definition 8.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Convention 2.1.
-/

public section

universe u v w x

namespace TauCeti

/-- A graph of groups over a Serre graph `Γ`: a group `A_v` for each vertex, a group `A_e` for
each geometric edge, shared by a dart and its reverse, and for each dart `e` an injective
homomorphism `ω_e : A_e →* A_{tgt e}`. -/
structure GraphOfGroups (Γ : SerreGraph.{u, v}) where
  /-- The vertex group `A_v`. -/
  vertexGroup : Γ.V → Type w
  /-- The group structure on the vertex groups. -/
  [instGroupVertexGroup : ∀ a, Group (vertexGroup a)]
  /-- The edge group of a geometric edge; a dart `e` has edge group
  `edgeGroup (Γ.toGeomEdge e)`. -/
  edgeGroup : Γ.GeomEdge → Type x
  /-- The group structure on the edge groups. -/
  [instGroupEdgeGroup : ∀ y, Group (edgeGroup y)]
  /-- The boundary monomorphism `ω_e : A_e →* A_{tgt e}` of a dart. -/
  ω : ∀ e : Γ.E, edgeGroup (Γ.toGeomEdge e) →* vertexGroup (Γ.tgt e)
  /-- The boundary maps are injective. -/
  ω_injective : ∀ e, Function.Injective (ω e)

namespace GraphOfGroups

attribute [instance] instGroupVertexGroup instGroupEdgeGroup

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)

/-- The boundary monomorphism `α_e : A_e →* A_{src e}` of a dart: the map `ω_{rev e}`, read
through the identification `A_{rev e} = A_e` and `tgt (rev e) = src e`. -/
def α (e : Γ.E) : 𝔸.edgeGroup (Γ.toGeomEdge e) →* 𝔸.vertexGroup (Γ.src e) :=
  ((MulEquiv.cast (M := 𝔸.vertexGroup) (Γ.tgt_rev e)).toMonoidHom.comp (𝔸.ω (Γ.rev e))).comp
    (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e).symm).toMonoidHom

theorem α_apply (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.α e c = MulEquiv.cast (M := 𝔸.vertexGroup) (Γ.tgt_rev e)
      (𝔸.ω (Γ.rev e) (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e).symm c)) :=
  (rfl)

theorem α_injective (e : Γ.E) : Function.Injective (𝔸.α e) := by
  intro c c' h
  simpa only [α_apply, EmbeddingLike.apply_eq_iff_eq, (𝔸.ω_injective _).eq_iff] using h

/-- The map `α` of a reversed dart is `ω` of the dart: `α_{rev e} = ω_e`. -/
@[simp] theorem α_rev_apply (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge (Γ.rev e))) :
    𝔸.α (Γ.rev e) c = 𝔸.ω e (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e) c) := by
  -- `α (rev e)` is defined through `ω (rev (rev e))`; transport along `rev (rev e) = e`.
  have key : ∀ f (_ : f = e) (d : 𝔸.edgeGroup (Γ.toGeomEdge f))
      (d' : 𝔸.edgeGroup (Γ.toGeomEdge e)), d ≍ d' → 𝔸.ω f d ≍ 𝔸.ω e d' := by
    rintro f rfl d d' h
    rw [eq_of_heq h]
  rw [α_apply]
  apply eq_of_heq
  simp only [MulEquiv.cast_apply]
  exact (cast_heq _ _).trans
    (key _ (Γ.rev_rev e) _ _ ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- The map `ω` of a reversed dart is `α` of the dart: `ω_{rev e} = α_e`. -/
@[simp] theorem ω_rev_apply (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge (Γ.rev e))) :
    𝔸.ω (Γ.rev e) c = MulEquiv.cast (M := 𝔸.vertexGroup) (Γ.tgt_rev e).symm
      (𝔸.α e (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e) c)) := by
  simp only [α_apply, MulEquiv.cast_apply, cast_cast, cast_eq]

/-- The graph of groups of an amalgamated product `A ∗_C B`: the segment with vertex groups `A`
at `false` and `B` at `true`, edge group `C`, and monomorphisms `f : C →* A` and `g : C →* B`.
The dart `false`, from the vertex of `A` to the vertex of `B`, has `α = f` and `ω = g`. -/
@[expose] def segment {A B : Type w} {C : Type x} [instA : Group A] [instB : Group B] [Group C]
    (f : C →* A) (g : C →* B) (hf : Function.Injective f) (hg : Function.Injective g) :
    GraphOfGroups.{0, 0, w, x} SerreGraph.segment where
  vertexGroup b := cond b B A
  instGroupVertexGroup b := Bool.rec (motive := fun b => Group (cond b B A)) instA instB b
  edgeGroup _ := C
  ω
    | false => g
    | true => f
  ω_injective
    | false => hg
    | true => hf

section segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C] (f : C →* A) (g : C →* B)
  (hf : Function.Injective f) (hg : Function.Injective g)

@[simp] theorem segment_ω_false : (segment f g hf hg).ω false = g := (rfl)

@[simp] theorem segment_ω_true : (segment f g hf hg).ω true = f := (rfl)

-- `α false = α (rev true)`; the cast in `α_rev_apply` is along the constant family `C`.
@[simp] theorem segment_α_false : (segment f g hf hg).α false = f :=
  MonoidHom.ext fun c => (segment f g hf hg).α_rev_apply true c

@[simp] theorem segment_α_true : (segment f g hf hg).α true = g :=
  MonoidHom.ext fun c => (segment f g hf hg).α_rev_apply false c

end segment

/-- The graph of groups of an HNN extension: one vertex with group `G`, one loop with edge
group `C`, and monomorphisms `f g : C →* G`. The dart `((), true)` has `α = f` and `ω = g`. -/
@[expose] def loop {G : Type w} {C : Type x} [Group G] [Group C] (f g : C →* G)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    GraphOfGroups.{0, 0, w, x} (SerreGraph.rose Unit) where
  vertexGroup _ := G
  edgeGroup _ := C
  ω
    | (_, true) => g
    | (_, false) => f
  ω_injective
    | (_, true) => hg
    | (_, false) => hf

section loop

variable {G : Type w} {C : Type x} [Group G] [Group C] (f g : C →* G)
  (hf : Function.Injective f) (hg : Function.Injective g)

@[simp] theorem loop_ω_true : (loop f g hf hg).ω ((), true) = g := (rfl)

@[simp] theorem loop_ω_false : (loop f g hf hg).ω ((), false) = f := (rfl)

-- As for `segment_α_false`, `α ((), true) = α (rev ((), false))`.
@[simp] theorem loop_α_true : (loop f g hf hg).α ((), true) = f :=
  MonoidHom.ext fun c => (loop f g hf hg).α_rev_apply ((), false) c

@[simp] theorem loop_α_false : (loop f g hf hg).α ((), false) = g :=
  MonoidHom.ext fun c => (loop f g hf hg).α_rev_apply ((), true) c

end loop

end GraphOfGroups

end TauCeti
