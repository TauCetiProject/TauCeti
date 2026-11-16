/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AuxiliaryTerminals.Basic
public import TauCeti.Combinatorics.Network.Walk

/-!
# Paths through auxiliary terminals

Adding a fresh source and sink turns walks between vertex sets `A` and `B` into walks between
single terminals. This file makes the three path operations in that reduction explicit.

* `TauCeti.AuxTerminalHom.lift` adds the source and sink arrows to an original walk.
* `TauCeti.AuxTerminalHom.project` removes those two arrows from an auxiliary-terminal walk.
* `TauCeti.AuxTerminalHom.trim` shortens the projected walk to a path whose internal vertices
  avoid both terminal sets.

The lifting formulas record the complete vertex and arrow lists. Projection is the inverse
decomposition on walks from the fresh source to the fresh sink. Trimming can shorten a projection,
so it is characterized instead by containment of its vertices and arrows. These containment
formulas imply that trimming preserves internally vertex-disjoint and arrow-disjoint indexed
families, including the zero-length path at a vertex of `A ∩ B`.
-/

public section

namespace TauCeti

open Finset Sum

universe u v

variable {V : Type u} {Q : V → V → Type v} {A B : Finset V}

namespace AuxTerminalHom

/-- An original arrow, including its endpoints, regarded as an arrow of the auxiliary-terminal
family. -/
def originalArrow : (Σ x y, Q x y) → (Σ x y, AuxTerminalHom Q A B x y)
  | ⟨x, y, e⟩ => ⟨inl x, inl y, original e⟩

/-- An original walk preceded by the arrow from the fresh source. -/
private def liftFromSource {a : V} (ha : a ∈ A) :
    ∀ {w : V}, ArrowWalk Q a w →
      ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl w)
  | _, @Quiver.Path.nil _ .(_) _ =>
      (ArrowWalk.nil _).cons (source (a := a) ha)
  | _, @Quiver.Path.cons _ .(_) _ _ _ q e =>
      (liftFromSource (a := a) ha q).cons (original e)

/-- Lift a walk from `a ∈ A` to `b ∈ B` by adding the fresh-source arrow before it and the
fresh-sink arrow after it. -/
def lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) :=
  (liftFromSource ha q).cons (sink hb)

@[simp]
private theorem liftFromSource_vertices {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    (liftFromSource (B := B) ha q).vertices = inr false :: q.vertices.map inl := by
  induction q with
  | nil => simp [liftFromSource]
  | cons q e ih => simp [liftFromSource, ih]

@[simp]
private theorem liftFromSource_arrows {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    (liftFromSource (B := B) ha q).arrows =
      [⟨inr false, inl a, source ha⟩] ++ q.arrows.map originalArrow := by
  induction q with
  | nil => simp [liftFromSource]
  | cons q e ih => simp [liftFromSource, ih, originalArrow]

@[simp]
theorem lift_vertices {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    (lift ha hb q).vertices = inr false :: q.vertices.map inl ++ [inr true] := by
  simp [lift]

@[simp]
theorem lift_arrows {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    (lift ha hb q).arrows = [⟨inr false, inl a, source ha⟩] ++
      q.arrows.map originalArrow ++ [⟨inl b, inr true, sink hb⟩] := by
  simp [lift]

private theorem nodup_aux_vertices_iff (l : List V) :
    (inr false :: l.map inl ++ [inr true]).Nodup ↔ l.Nodup := by
  simp only [List.nodup_cons, List.mem_map, List.mem_singleton, List.nodup_append]
  simp only [List.nodup_map_iff inl_injective]
  simp

/-- Lifting preserves and reflects the property of being a path. -/
@[simp]
theorem lift_isPath_iff {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    (lift ha hb q).IsPath ↔ q.IsPath := by
  rw [ArrowWalk.isPath_def, ArrowWalk.isPath_def, lift_vertices]
  exact nodup_aux_vertices_iff _

/-- A decomposition of an auxiliary-terminal walk into its source arrow, an original walk, and
its sink arrow. -/
structure Projection
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) where
  /-- The first original vertex. -/
  source : V
  /-- The first original vertex belongs to `A`. -/
  source_mem : source ∈ A
  /-- The last original vertex. -/
  target : V
  /-- The last original vertex belongs to `B`. -/
  target_mem : target ∈ B
  /-- The original part of the auxiliary-terminal walk. -/
  walk : ArrowWalk Q source target
  /-- The exact vertex decomposition. -/
  vertices_eq : p.vertices = inr false :: walk.vertices.map inl ++ [inr true]
  /-- The exact arrow decomposition. -/
  arrows_eq : p.arrows = [⟨inr false, inl source, AuxTerminalHom.source source_mem⟩] ++
    walk.arrows.map originalArrow ++ [⟨inl target, inr true, AuxTerminalHom.sink target_mem⟩]

private theorem eq_nil_of_target_source
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr false)) :
    p = ArrowWalk.nil _ := by
  cases p with
  | nil => rfl
  | @cons y _ _ e =>
      exact isEmptyElim (α := AuxTerminalHom Q A B y (inr false)) e

private theorem exists_projection_to_inl {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {w : V} (hy : y = inl w) :
    ∃ (a : V) (ha : a ∈ A) (q : ArrowWalk Q a w),
      p.vertices = inr false :: q.vertices.map inl ∧
      p.arrows = [⟨inr false, inl a, source ha⟩] ++ q.arrows.map originalArrow := by
  induction p generalizing w with
  | nil => exact absurd hy Sum.inr_ne_inl
  | @cons z y p e ih =>
    subst hy
    rcases z with u | _ | _
    · obtain ⟨a, ha, q, hv, he⟩ := ih rfl
      refine ⟨a, ha, q.cons (originalEquiv.symm e), ?_, ?_⟩
      · simp [hv]
      · simp [he, originalArrow, original_originalEquiv_symm]
    · have hp : p = ArrowWalk.nil _ := eq_nil_of_target_source p
      subst hp
      refine ⟨w, mem_of_source e, ArrowWalk.nil w, rfl, ?_⟩
      simp only [ArrowWalk.arrows_cons, ArrowWalk.arrows_nil, List.nil_append, List.map_nil,
        List.append_nil]
      rw [eq_source e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl w)) e

/-- Every walk from the fresh source to the fresh sink has an exact projection to an original
walk from `A` to `B`. -/
private theorem projection_nonempty
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    Nonempty (Projection p) := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · obtain ⟨a, ha, q, hv, he⟩ := exists_projection_to_inl p rfl
      refine ⟨⟨a, ha, b, mem_of_sink e, q, by simp [hv], ?_⟩⟩
      simp only [ArrowWalk.arrows_cons, he, List.append_assoc]
      rw [eq_sink e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

/-- Project an auxiliary-terminal walk to the original walk between its first and last original
vertices. -/
noncomputable def project
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) : Projection p :=
  Classical.choice (projection_nonempty p)

end AuxTerminalHom

/-- The fresh sink is reachable from the fresh source avoiding a set `X` not containing either
terminal exactly when some vertex of `B` is reachable from some vertex of `A` while avoiding the
original vertices in `X`. -/
theorem reachableAvoiding_auxTerminalHom_iff {X : Set (V ⊕ Bool)} (hσ : inr false ∉ X)
    (hτ : inr true ∉ X) :
    ReachableAvoiding (AuxTerminalHom Q A B) X (inr false) (inr true) ↔
      ∃ a ∈ A, ∃ b ∈ B, ReachableAvoiding Q (inl ⁻¹' X) a b := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := reachableAvoiding_def.1 h
    let P := AuxTerminalHom.project p
    refine ⟨P.source, P.source_mem, P.target, P.target_mem,
      reachableAvoiding_def.2 ⟨P.walk, fun v hv ↦ hp (inl v) ?_⟩⟩
    rw [P.vertices_eq]
    simp [hv]
  · rintro ⟨a, ha, b, hb, h⟩
    obtain ⟨q, hq⟩ := reachableAvoiding_def.1 h
    refine reachableAvoiding_def.2 ⟨AuxTerminalHom.lift ha hb q, fun x hx ↦ ?_⟩
    rw [AuxTerminalHom.lift_vertices] at hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | ⟨v, hv, rfl⟩ | rfl
    exacts [hσ, hq v hv, hτ]

namespace AuxTerminalHom

/-- Projection preserves and reflects the property of being a path. -/
theorem Projection.isPath_iff
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    P.walk.IsPath ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, ArrowWalk.isPath_def, P.vertices_eq]
  exact (nodup_aux_vertices_iff _).symm

/-- A projected auxiliary-terminal walk trimmed to a path whose internal vertices avoid both
terminal sets. -/
structure Trimming
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) where
  /-- The source of the trimmed path. -/
  source : V
  /-- The trimmed source belongs to `A`. -/
  source_mem : source ∈ A
  /-- The target of the trimmed path. -/
  target : V
  /-- The trimmed target belongs to `B`. -/
  target_mem : target ∈ B
  /-- The trimmed original path. -/
  walk : ArrowWalk Q source target
  /-- The trimmed walk is a path. -/
  isPath : walk.IsPath
  /-- Internal vertices of the trimmed path avoid both terminal sets. -/
  interior_notMem : ∀ v ∈ walk.vertices, v ≠ source → v ≠ target → v ∉ A ∧ v ∉ B
  /-- Every trimmed vertex comes from the auxiliary-terminal walk. -/
  vertices_map_subset : walk.vertices.map inl ⊆ p.vertices
  /-- Every trimmed arrow comes from the auxiliary-terminal walk. -/
  arrows_map_subset : walk.arrows.map originalArrow ⊆ p.arrows

/-- Every auxiliary-terminal walk admits a trimming. -/
private theorem trimming_nonempty
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    Nonempty (Trimming p) := by
  let P := project p
  obtain ⟨a, ha, b, hb, q, hq, hv, he, hint⟩ :=
    ArrowWalk.exists_isPath_interior_notMem (A := (A : Set V)) (B := (B : Set V))
      P.walk P.source_mem P.target_mem
  refine ⟨⟨a, ha, b, hb, q, hq, by simpa using hint, ?_, ?_⟩⟩
  · rw [P.vertices_eq]
    exact List.Subset.trans (List.map_subset _ hv) (by simp)
  · rw [P.arrows_eq]
    exact List.Subset.trans (List.map_subset _ he) (by simp)

/-- Trim an auxiliary-terminal walk to an `A`–`B` path whose internal vertices avoid `A ∪ B`.
The path may have length zero when its endpoint belongs to `A ∩ B`. -/
noncomputable def trim
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) : Trimming p :=
  Classical.choice (trimming_nonempty p)

/-- Trimming turns pairwise internally vertex-disjoint auxiliary-terminal walks into pairwise
vertex-disjoint original paths. -/
theorem pairwise_disjoint_vertices_trim {I : Type*}
    (P : I → ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true))
    (hP : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) :
    Pairwise fun i j ↦ (trim (P i)).walk.vertices.Disjoint (trim (P j)).walk.vertices := by
  intro i j hij v hvi hvj
  have h := ArrowWalk.internallyDisjoint_def.1 (hP hij) (inl v)
    ((trim (P i)).vertices_map_subset (List.mem_map_of_mem hvi))
    ((trim (P j)).vertices_map_subset (List.mem_map_of_mem hvj))
  exact h.elim Sum.inl_ne_inr Sum.inl_ne_inr

/-- Trimming preserves pairwise arrow-disjointness. -/
theorem pairwise_disjoint_arrows_trim {I : Type*}
    (P : I → ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true))
    (hP : Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows) :
    Pairwise fun i j ↦ (trim (P i)).walk.arrows.Disjoint (trim (P j)).walk.arrows := by
  intro i j hij e hei hej
  exact hP hij ((trim (P i)).arrows_map_subset (List.mem_map_of_mem hei))
    ((trim (P j)).arrows_map_subset (List.mem_map_of_mem hej))

end AuxTerminalHom

end TauCeti
