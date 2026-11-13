/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker

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
* `TauCeti.GraphOfGroups.αArrow`, `TauCeti.GraphOfGroups.ωArrow`: the boundary monomorphisms of
  a dart `e : a ⟶ b` of the quiver of `Γ`, with values in `A_a` and `A_b`.
* `TauCeti.GraphOfGroups.segment`: the graph of groups of an amalgamated product.
* `TauCeti.GraphOfGroups.loop`: the graph of groups of an HNN extension.
* `TauCeti.GraphOfGroups.restrict`: the restriction of a graph of groups to the subgraph spanned
  by a reversal-closed set of darts, with all vertices of the graph.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.4, Definition 8, and §5.1.
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

/-- `α` of a dart `e'` equal to the reverse of `e` is `ω` of `e`, read through the identifications
of the edge groups and of the vertex groups. -/
theorem cast_α_eq_ω {e e' : Γ.E} (he : e' = Γ.rev e) (h₁ : Γ.src e' = Γ.tgt e)
    (h₂ : Γ.toGeomEdge e = Γ.toGeomEdge e') (d : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    MulEquiv.cast (M := 𝔸.vertexGroup) h₁ (𝔸.α e' (MulEquiv.cast (M := 𝔸.edgeGroup) h₂ d)) =
      𝔸.ω e d := by
  subst he
  rw [α_rev_apply]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
  -- What remains is a transport from `A_{o(e⁻¹)}` to `A_{t(e)}`, the same group by definition.
  rfl

section Arrow

variable {a b : Γ.V}

/-- The boundary monomorphism `α_e : A_e →* A_a` of a dart `e : a ⟶ b` of the quiver of `Γ`:
the map `α` of the underlying dart, read in `A_a` through `src e = a`. -/
def αArrow (e : a ⟶ b) : 𝔸.edgeGroup (Γ.toGeomEdge e.1) →* 𝔸.vertexGroup a :=
  (MulEquiv.cast (M := 𝔸.vertexGroup) e.2.1).toMonoidHom.comp (𝔸.α e.1)

/-- The boundary monomorphism `ω_e : A_e →* A_b` of a dart `e : a ⟶ b` of the quiver of `Γ`:
the map `ω` of the underlying dart, read in `A_b` through `tgt e = b`. -/
def ωArrow (e : a ⟶ b) : 𝔸.edgeGroup (Γ.toGeomEdge e.1) →* 𝔸.vertexGroup b :=
  (MulEquiv.cast (M := 𝔸.vertexGroup) e.2.2).toMonoidHom.comp (𝔸.ω e.1)

theorem αArrow_apply (e : a ⟶ b) (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    𝔸.αArrow e c = MulEquiv.cast (M := 𝔸.vertexGroup) e.2.1 (𝔸.α e.1 c) :=
  (rfl)

theorem ωArrow_apply (e : a ⟶ b) (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    𝔸.ωArrow e c = MulEquiv.cast (M := 𝔸.vertexGroup) e.2.2 (𝔸.ω e.1 c) :=
  (rfl)

@[simp] theorem αArrow_mk (e : Γ.E) : 𝔸.αArrow (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) = 𝔸.α e :=
  (rfl)

@[simp] theorem ωArrow_mk (e : Γ.E) : 𝔸.ωArrow (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) = 𝔸.ω e :=
  (rfl)

theorem αArrow_injective (e : a ⟶ b) : Function.Injective (𝔸.αArrow e) :=
  (MulEquiv.cast (M := 𝔸.vertexGroup) e.2.1).injective.comp (𝔸.α_injective e.1)

theorem ωArrow_injective (e : a ⟶ b) : Function.Injective (𝔸.ωArrow e) :=
  (MulEquiv.cast (M := 𝔸.vertexGroup) e.2.2).injective.comp (𝔸.ω_injective e.1)

/-- The map `α` of an arrow `e'` whose dart is the reverse of the dart of `e` is `ω_e`. -/
private theorem αArrow_eq_ωArrow_of_val_eq_rev (e' : b ⟶ a) (e : a ⟶ b) (h : e'.1 = Γ.rev e.1)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e'.1)) :
    𝔸.αArrow e' c =
      𝔸.ωArrow e (MulEquiv.cast (M := 𝔸.edgeGroup) (by rw [h, Γ.toGeomEdge_rev]) c) := by
  obtain ⟨e, rfl, rfl⟩ := e
  obtain ⟨f, h₁, h₂⟩ := e'
  obtain rfl : f = Γ.rev e := h
  rw [αArrow_apply, ωArrow_mk, α_rev_apply]
  -- Only the cast along `h₁ : src (rev e) = tgt e` is left. It is the identity because `tgt e`
  -- is defined as `src (rev e)` (`SerreGraph.tgt` is exposed for this); the statement of
  -- `α_rev_apply` relies on the same definitional equality.
  rfl

/-- The map `α` of a reversed dart is `ω` of the dart. -/
theorem αArrow_reverse_apply (e : a ⟶ b)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge (Quiver.reverse e).1)) :
    𝔸.αArrow (Quiver.reverse e) c =
      𝔸.ωArrow e (MulEquiv.cast (M := 𝔸.edgeGroup) (by simp) c) :=
  𝔸.αArrow_eq_ωArrow_of_val_eq_rev _ e (Γ.reverse_val e) c

/-- The map `ω` of a reversed dart is `α` of the dart. -/
theorem ωArrow_reverse_apply (e : a ⟶ b)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge (Quiver.reverse e).1)) :
    𝔸.ωArrow (Quiver.reverse e) c =
      𝔸.αArrow e (MulEquiv.cast (M := 𝔸.edgeGroup) (by simp) c) := by
  rw [𝔸.αArrow_eq_ωArrow_of_val_eq_rev e (Quiver.reverse e) (by simp)]
  simp only [MulEquiv.cast_apply, cast_cast, cast_eq]

/-- An edge group element `c` of a dart `e`, read as an element `c'` of the edge group of
`rev e`: `α_{rev e}(c') = ω_e(c)` and `ω_{rev e}(c') = α_e(c)`. -/
theorem exists_αArrow_reverse_eq_and_ωArrow_reverse_eq (e : a ⟶ b)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    ∃ c' : 𝔸.edgeGroup (Γ.toGeomEdge (Quiver.reverse e).1),
      𝔸.αArrow (Quiver.reverse e) c' = 𝔸.ωArrow e c ∧
        𝔸.ωArrow (Quiver.reverse e) c' = 𝔸.αArrow e c :=
  ⟨(MulEquiv.cast (M := 𝔸.edgeGroup) (by simp)).symm c, by
    rw [αArrow_reverse_apply, MulEquiv.apply_symm_apply], by
    rw [ωArrow_reverse_apply, MulEquiv.apply_symm_apply]⟩

@[simp] theorem range_αArrow_reverse (e : a ⟶ b) :
    (𝔸.αArrow (Quiver.reverse e)).range = (𝔸.ωArrow e).range := by
  ext g
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨_, (𝔸.αArrow_reverse_apply e c).symm.trans hc⟩, fun ⟨c, hc⟩ ↦ ?_⟩
  obtain ⟨c', hc', -⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e c
  exact ⟨c', hc'.trans hc⟩

@[simp] theorem range_ωArrow_reverse (e : a ⟶ b) :
    (𝔸.ωArrow (Quiver.reverse e)).range = (𝔸.αArrow e).range := by
  rw [← 𝔸.range_αArrow_reverse, Quiver.reverse_reverse]

@[simp] theorem range_αArrow_dart (e : Γ.E) : (𝔸.αArrow (Γ.dart e)).range = (𝔸.α e).range := by
  rw [Γ.dart_def, αArrow_mk]

@[simp] theorem range_ωArrow_dart (e : Γ.E) : (𝔸.ωArrow (Γ.dart e)).range = (𝔸.ω e).range := by
  rw [Γ.dart_def, ωArrow_mk]

/-- At a vertex where a dart `e'` is followed by its reverse `e`, the image of `ω_{e'}` is the
image of `α_e`. -/
theorem range_ωArrow_eq_range_αArrow {c : Γ.V} (e' : a ⟶ b) (e : b ⟶ c) (h : e'.1 = Γ.rev e.1) :
    (𝔸.ωArrow e').range = (𝔸.αArrow e).range := by
  obtain rfl := Γ.src_eq_tgt_of_val_eq_rev h
  obtain rfl := Γ.eq_reverse_of_val_eq_rev h
  exact 𝔸.range_ωArrow_reverse e

end Arrow

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

section restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- The restriction of a graph of groups `𝔸` over `Γ` to the subgraph `Γ.restrict S hS`, which has
all vertices of `Γ` and the darts of a reversal-closed set `S`: the vertex groups are those of `𝔸`,
and a dart of `S` keeps its edge group and its boundary monomorphism `ω_e`. The body is exposed and
unfolds at instance transparency, so that an element of a vertex group of `𝔸` is accepted as an
element of the corresponding vertex group of the restriction by rewriting and simplification. -/
@[expose, instance_reducible] def restrict : GraphOfGroups.{u, v, w, x} (Γ.restrict S hS) where
  vertexGroup := 𝔸.vertexGroup
  edgeGroup y := 𝔸.edgeGroup
    (SerreGraph.GeomEdge.lift (Γ.restrict S hS) (fun e : S => Γ.toGeomEdge e.1)
      (fun e => Γ.toGeomEdge_rev e.1) y)
  ω e := (𝔸.ω e.1).comp
    (MulEquiv.cast (M := 𝔸.edgeGroup) (SerreGraph.GeomEdge.lift_toGeomEdge _ _ _ e)).toMonoidHom
  ω_injective e := (𝔸.ω_injective e.1).comp (MulEquiv.injective _)

/-- The boundary monomorphism `ω_e` of a dart of the restriction is `ω_e` of `𝔸`, read through the
identification of the edge groups. -/
@[simp] theorem restrict_ω_apply (e : (Γ.restrict S hS).E)
    (c : (𝔸.restrict S hS).edgeGroup ((Γ.restrict S hS).toGeomEdge e)) :
    (𝔸.restrict S hS).ω e c =
      𝔸.ω e.1 (MulEquiv.cast (M := 𝔸.edgeGroup) (SerreGraph.GeomEdge.lift_toGeomEdge _ _ _ e) c) :=
  (rfl)

/-- The boundary monomorphism `α_e` of a dart of the restriction is `α_e` of `𝔸`, read through the
identification of the edge groups. -/
@[simp] theorem restrict_α_apply (e : (Γ.restrict S hS).E)
    (c : (𝔸.restrict S hS).edgeGroup ((Γ.restrict S hS).toGeomEdge e)) :
    (𝔸.restrict S hS).α e c =
      𝔸.α e.1 (MulEquiv.cast (M := 𝔸.edgeGroup)
        (SerreGraph.GeomEdge.lift_toGeomEdge _ _ _ e) c) := by
  rw [α_apply, α_apply, restrict_ω_apply]
  simp only [MulEquiv.cast_apply, cast_cast]
  -- The cast into the vertex group of the restriction is `cast` by `MulEquiv.cast_apply`, and the
  -- two transports of `c` agree by proof irrelevance.
  rfl

end restrict

end GraphOfGroups

end TauCeti
