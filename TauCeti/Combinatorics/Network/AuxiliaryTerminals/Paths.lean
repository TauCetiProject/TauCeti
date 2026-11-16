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
decomposition on walks from the fresh source to the fresh sink: lifting a projection gives back the
original walk. Trimming can shorten a projection, so it is characterized instead by containment of
its vertices and arrows. These containment formulas imply that trimming turns pairwise internally
vertex-disjoint families into pairwise vertex-disjoint original paths, and families whose original
arrows are pairwise disjoint into pairwise arrow-disjoint original paths. A trimmed path may have
length zero at a vertex of `A ∩ B`.
-/

public section

namespace TauCeti

open Finset Sum

universe u v

variable {V : Type u} {Q : V → V → Type v} {A B : Finset V}

namespace AuxTerminalHom

/-- The inclusion of the original arrow family into the auxiliary-terminal family. -/
private abbrev originalPrefunctor : @Prefunctor V ⟨Q⟩ (V ⊕ Bool) ⟨AuxTerminalHom Q A B⟩ :=
  @Prefunctor.mk V ⟨Q⟩ (V ⊕ Bool) ⟨AuxTerminalHom Q A B⟩ inl fun e ↦ original e

/-- An original walk preceded by the arrow from the fresh source. -/
private def liftFromSource {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl w) :=
  ((ArrowWalk.nil _).cons (source ha)).comp
    (@Prefunctor.mapPath V ⟨Q⟩ (V ⊕ Bool) ⟨AuxTerminalHom Q A B⟩ originalPrefunctor _ _ q)

private theorem liftFromSource_nil {a : V} (ha : a ∈ A) :
    liftFromSource (B := B) ha (ArrowWalk.nil (Q := Q) a) = (ArrowWalk.nil _).cons (source ha) :=
  (rfl)

private theorem liftFromSource_cons {a v w : V} (ha : a ∈ A) (q : ArrowWalk Q a v) (e : Q v w) :
    liftFromSource (B := B) ha (q.cons e) = (liftFromSource ha q).cons (original e) :=
  (rfl)

/-- Lift a walk from `a ∈ A` to `b ∈ B` by adding the fresh-source arrow before it and the
fresh-sink arrow after it. -/
def lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) :=
  (liftFromSource ha q).cons (sink hb)

@[simp]
private theorem vertices_liftFromSource {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    (liftFromSource (B := B) ha q).vertices = inr false :: q.vertices.map inl := by
  rw [liftFromSource, ArrowWalk.vertices_nil_cons_comp, ArrowWalk.vertices,
    @Prefunctor.vertices_mapPath V (V ⊕ Bool) ⟨Q⟩ ⟨AuxTerminalHom Q A B⟩]

@[simp]
private theorem arrows_liftFromSource {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    (liftFromSource (B := B) ha q).arrows =
      [⟨inr false, inl a, source ha⟩] ++ q.arrows.map originalArrow := by
  rw [liftFromSource, ArrowWalk.arrows_comp, Prefunctor.arrows_mapPath, ArrowWalk.arrows_cons,
    ArrowWalk.arrows_nil, List.nil_append]
  exact congrArg _ (List.map_congr_left fun ⟨_, _, e⟩ _ ↦ (originalArrow_mk e).symm)

@[simp]
theorem vertices_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    (lift ha hb q).vertices = inr false :: q.vertices.map inl ++ [inr true] := by
  simp [lift]

@[simp]
theorem arrows_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    (lift ha hb q).arrows = [⟨inr false, inl a, source ha⟩] ++
      q.arrows.map originalArrow ++ [⟨inl b, inr true, sink hb⟩] := by
  simp [lift]

/-- An original arrow occurs in a lifted walk exactly when it occurs in the original walk. -/
theorem originalArrow_mem_arrows_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b)
    {e : Σ x y, Q x y} : originalArrow e ∈ (lift ha hb q).arrows ↔ e ∈ q.arrows := by
  rw [arrows_lift, List.mem_append, List.mem_append,
    List.mem_map_of_injective originalArrow_injective]
  obtain ⟨x, y, e⟩ := e
  simp only [originalArrow_mk, List.mem_singleton, Sigma.mk.injEq, reduceCtorEq, false_and,
    false_or, inl.injEq, or_iff_left_iff_imp, and_imp]
  rintro rfl h
  simp at h

/-- Lifting preserves and reflects the property of being a path. -/
@[simp]
theorem isPath_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    (lift ha hb q).IsPath ↔ q.IsPath := by
  rw [ArrowWalk.isPath_def, ArrowWalk.isPath_def, vertices_lift]
  simp only [List.nodup_cons, List.mem_map, List.mem_singleton, List.nodup_append]
  simp only [List.nodup_map_iff inl_injective]
  simp

/-- A decomposition of an auxiliary-terminal walk into its source arrow, an original walk, and
its sink arrow. -/
@[ext]
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
  /-- Lifting the original part gives back the auxiliary-terminal walk. -/
  lift_walk : lift source_mem target_mem walk = p

private theorem eq_nil_of_target_source
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr false)) :
    p = ArrowWalk.nil _ := by
  cases p with
  | nil => rfl
  | @cons y _ _ e =>
      exact isEmptyElim (α := AuxTerminalHom Q A B y (inr false)) e

private theorem exists_projection_to_inl {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {w : V} (hy : y = inl w) :
    ∃ (a : V) (ha : a ∈ A) (q : ArrowWalk Q a w), p ≍ liftFromSource (B := B) ha q := by
  induction p generalizing w with
  | nil => exact absurd hy Sum.inr_ne_inl
  | @cons z y p e ih =>
    subst hy
    rcases z with u | _ | _
    · obtain ⟨a, ha, q, h⟩ := ih rfl
      refine ⟨a, ha, q.cons (originalEquiv.symm e), ?_⟩
      rw [eq_of_heq h]
      rw [liftFromSource_cons, original_originalEquiv_symm]
    · have hp : p = ArrowWalk.nil _ := eq_nil_of_target_source p
      subst hp
      refine ⟨w, mem_of_source e, ArrowWalk.nil w, ?_⟩
      rw [liftFromSource_nil, ← eq_source e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl w)) e

/-- Every walk from the fresh source to the fresh sink has an exact projection to an original
walk from `A` to `B`. -/
private theorem projection_nonempty
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    Nonempty (Projection p) := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · obtain ⟨a, ha, q, h⟩ := exists_projection_to_inl p rfl
      refine ⟨⟨a, ha, b, mem_of_sink e, q, ?_⟩⟩
      rw [lift, ← eq_of_heq h, ← eq_sink e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

/-- Project an auxiliary-terminal walk to the original walk between its first and last original
vertices. -/
noncomputable def project
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) : Projection p :=
  Classical.choice (projection_nonempty p)

/-- The exact vertex decomposition of a projected walk. -/
theorem Projection.vertices_eq
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    p.vertices = inr false :: P.walk.vertices.map inl ++ [inr true] := by
  obtain ⟨_, _, _, _, _, rfl⟩ := P
  exact vertices_lift ..

/-- The exact arrow decomposition of a projected walk. -/
theorem Projection.arrows_eq
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    p.arrows = [⟨inr false, inl P.source, AuxTerminalHom.source P.source_mem⟩] ++
      P.walk.arrows.map originalArrow ++
        [⟨inl P.target, inr true, AuxTerminalHom.sink P.target_mem⟩] := by
  obtain ⟨_, _, _, _, _, rfl⟩ := P
  exact arrows_lift ..

/-- Projection preserves and reflects the property of being a path. -/
@[simp]
theorem Projection.isPath_iff
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    P.walk.IsPath ↔ p.IsPath := by
  obtain ⟨_, _, _, _, _, rfl⟩ := P
  exact (isPath_lift ..).symm

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
    rw [AuxTerminalHom.vertices_lift] at hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | ⟨v, hv, rfl⟩ | rfl
    exacts [hσ, hq v hv, hτ]

namespace AuxTerminalHom

/-- A projected auxiliary-terminal walk trimmed to a path whose internal vertices avoid both
terminal sets. -/
@[ext]
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
  map_vertices_subset : walk.vertices.map inl ⊆ p.vertices
  /-- Every trimmed arrow comes from the auxiliary-terminal walk. -/
  map_arrows_subset : walk.arrows.map originalArrow ⊆ p.arrows

attribute [simp] Trimming.isPath

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
    ((trim (P i)).map_vertices_subset (List.mem_map_of_mem hvi))
    ((trim (P j)).map_vertices_subset (List.mem_map_of_mem hvj))
  exact h.elim Sum.inl_ne_inr Sum.inl_ne_inr

/-- Trimming turns auxiliary-terminal walks that share no original arrow into pairwise
arrow-disjoint original paths. The walks may share their source and sink arrows, so their trimmed
paths may share endpoints. -/
theorem pairwise_disjoint_arrows_trim {I : Type*}
    (P : I → ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true))
    (hP : Pairwise fun i j ↦
      ∀ ⦃e⦄, originalArrow e ∈ (P i).arrows → originalArrow e ∉ (P j).arrows) :
    Pairwise fun i j ↦ (trim (P i)).walk.arrows.Disjoint (trim (P j)).walk.arrows := by
  intro i j hij e hei hej
  exact hP hij ((trim (P i)).map_arrows_subset (List.mem_map_of_mem hei))
    ((trim (P j)).map_arrows_subset (List.mem_map_of_mem hej))

end AuxTerminalHom

end TauCeti
