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
original walk. `TauCeti.AuxTerminalHom.walkEquiv` packages both round trips. Projection is
computed from the walk and does not trim its original segment. Trimming can shorten a projection,
so it is characterized instead by containment of its vertices and arrows. These containment
formulas imply that trimming turns pairwise internally vertex-disjoint families into pairwise
vertex-disjoint original paths, and families whose original arrows are pairwise disjoint into
pairwise arrow-disjoint original paths. A trimmed path may have length zero at a vertex of `A ∩ B`.
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
def liftFromSource {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl w) :=
  ((ArrowWalk.nil _).cons (source ha)).comp
    (@Prefunctor.mapPath V ⟨Q⟩ (V ⊕ Bool) ⟨AuxTerminalHom Q A B⟩ originalPrefunctor _ _ q)

@[simp]
theorem liftFromSource_nil {a : V} (ha : a ∈ A) :
    liftFromSource (B := B) ha (ArrowWalk.nil (Q := Q) a) = (ArrowWalk.nil _).cons (source ha) :=
  (rfl)

@[simp]
theorem liftFromSource_cons {a v w : V} (ha : a ∈ A) (q : ArrowWalk Q a v) (e : Q v w) :
    liftFromSource (B := B) ha (q.cons e) = (liftFromSource ha q).cons (original e) :=
  (rfl)

/-- Lift a walk from `a ∈ A` to `b ∈ B` by adding the fresh-source arrow before it and the
fresh-sink arrow after it. -/
def lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) :=
  (liftFromSource ha q).cons (sink hb)

/-- The lifted walk ends by appending the auxiliary sink arrow. -/
theorem lift_eq_cons {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b) :
    lift ha hb q = (liftFromSource ha q).cons (sink hb) :=
  (rfl)

@[simp]
theorem vertices_liftFromSource {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
    (liftFromSource (B := B) ha q).vertices = inr false :: q.vertices.map inl := by
  rw [liftFromSource, ArrowWalk.vertices_nil_cons_comp, ArrowWalk.vertices,
    @Prefunctor.vertices_mapPath V (V ⊕ Bool) ⟨Q⟩ ⟨AuxTerminalHom Q A B⟩]

@[simp]
theorem arrows_liftFromSource {a w : V} (ha : a ∈ A) (q : ArrowWalk Q a w) :
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

@[simp]
theorem length_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih, Nat.add_assoc]

@[simp]
theorem length_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (lift ha hb p).length = p.length + 2 := by
  simp [lift_eq_cons, Nat.add_assoc]

/-- An original arrow occurs in a lifted walk exactly when it occurs in the original walk. -/
@[grind =]
theorem originalArrow_mem_arrows_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (q : ArrowWalk Q a b)
    {e : Σ x y, Q x y} : originalArrow e ∈ (lift ha hb q).arrows ↔ e ∈ q.arrows := by
  simp [arrows_lift, List.mem_map_of_injective originalArrow_injective]

/-- Prepending the source arrow preserves and reflects simplicity. -/
@[simp]
theorem isPath_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).IsPath ↔ p.IsPath := by
  simp [ArrowWalk.isPath_def, List.nodup_map_iff inl_injective]

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

/-- Compute the original segment of a walk ending at an original vertex. -/
private def projectPrefix {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {b : V} (hy : y = inl b) :
    Σ a : A, ArrowWalk Q a.val b := by
  induction p generalizing b with
  | nil => exact (Sum.inr_ne_inl hy).elim
  | @cons z y p e ih =>
    subst hy
    rcases z with a | _ | _
    · obtain ⟨a, q⟩ := ih rfl
      exact ⟨a, q.cons (originalEquiv.symm e)⟩
    · exact ⟨⟨b, mem_of_source e⟩, ArrowWalk.nil b⟩
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl b)) e

/-- Remove the source arrow from a walk ending at an original vertex. -/
def projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    Σ a : A, ArrowWalk Q a.val b :=
  projectPrefix p rfl

@[simp]
theorem projectFromSource_nil_cons {b : V} (e : AuxTerminalHom Q A B (inr false) (inl b)) :
    projectFromSource ((ArrowWalk.nil _).cons e) = ⟨⟨b, mem_of_source e⟩, ArrowWalk.nil b⟩ :=
  (rfl)

@[simp]
theorem projectFromSource_cons {a b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl a))
    (e : AuxTerminalHom Q A B (inl a) (inl b)) :
    projectFromSource (p.cons e) =
      ⟨(projectFromSource p).fst, (projectFromSource p).snd.cons (originalEquiv.symm e)⟩ :=
  (rfl)

private theorem liftFromSource_projectPrefix {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {b : V} (hy : y = inl b) :
    liftFromSource (B := B) (projectPrefix p hy).fst.property (projectPrefix p hy).snd ≍ p := by
  induction p generalizing b with
  | nil => exact (Sum.inr_ne_inl hy).elim
  | @cons z y p e ih =>
    subst hy
    rcases z with a | _ | _
    · have h : liftFromSource (B := B) (projectFromSource p).fst.property
          (projectFromSource p).snd = p := eq_of_heq (ih (b := a) rfl)
      apply heq_of_eq
      -- Fold the private projection at the original endpoint to use the public cons equation.
      change liftFromSource (B := B) (projectFromSource (ArrowWalk.cons p e)).fst.property
        (projectFromSource (ArrowWalk.cons p e)).snd = ArrowWalk.cons p e
      rw [projectFromSource_cons, liftFromSource_cons, original_originalEquiv_symm, h]
    · have hp := eq_nil_of_target_source p
      subst hp
      exact heq_of_eq <| (liftFromSource_nil (Q := Q) (B := B) (mem_of_source e)).trans
        (congrArg (fun f ↦ (ArrowWalk.nil (inr false)).cons f) (eq_source e).symm)
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl b)) e

@[simp]
theorem projectFromSource_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    projectFromSource (liftFromSource (B := B) ha p) = ⟨⟨a, ha⟩, p⟩ := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [liftFromSource_cons, projectFromSource_cons, ih, originalEquiv_symm_original]

@[simp]
theorem liftFromSource_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    liftFromSource (projectFromSource p).fst.property (projectFromSource p).snd = p :=
  eq_of_heq (liftFromSource_projectPrefix p rfl)

/-- Lifting with fixed endpoints retains the entire original walk. -/
theorem liftFromSource_injective {a b : V} (ha : a ∈ A) :
    Function.Injective (liftFromSource (Q := Q) (B := B) (w := b) ha) := by
  intro p q h
  have h' := congrArg projectFromSource h
  simpa only [projectFromSource_liftFromSource, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h'

@[simp]
theorem liftFromSource_inj {a b : V} (ha : a ∈ A) {p q : ArrowWalk Q a b} :
    liftFromSource (B := B) ha p = liftFromSource ha q ↔ p = q :=
  (liftFromSource_injective ha).eq_iff

/-- Projection removes exactly one source arrow. -/
theorem length_projectFromSource_add_one {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    (projectFromSource p).snd.length + 1 = p.length := by
  rw [← length_liftFromSource (B := B) (projectFromSource p).fst.property,
    liftFromSource_projectFromSource]

@[simp]
theorem length_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    (projectFromSource p).snd.length = p.length - 1 := by
  rw [← length_projectFromSource_add_one p, Nat.add_sub_cancel]

/-- The vertex list starts with the fresh source, followed by the original vertices in order. -/
theorem vertices_eq_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    p.vertices = inr false :: (projectFromSource p).snd.vertices.map inl := by
  simpa only [liftFromSource_projectFromSource] using
    vertices_liftFromSource (B := B) (projectFromSource p).fst.property (projectFromSource p).snd

/-- The arrow list starts with the source arrow, followed by every original arrow occurrence. -/
theorem arrows_eq_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    p.arrows = [⟨inr false, inl (projectFromSource p).fst.val,
        source (projectFromSource p).fst.property⟩] ++
      (projectFromSource p).snd.arrows.map originalArrow := by
  simpa only [liftFromSource_projectFromSource] using
    arrows_liftFromSource (B := B) (projectFromSource p).fst.property (projectFromSource p).snd

@[simp]
theorem mem_vertices_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) (v : V) :
    v ∈ (projectFromSource p).snd.vertices ↔ inl v ∈ p.vertices := by
  simp [vertices_eq_projectFromSource p]

/-- Recover the source prefix's original vertices in order, including repetitions. -/
theorem map_vertices_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    (projectFromSource p).snd.vertices.map inl = p.vertices.tail := by
  simp [vertices_eq_projectFromSource p]

@[simp]
theorem mem_arrows_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) (e : Σ a b, Q a b) :
    e ∈ (projectFromSource p).snd.arrows ↔ originalArrow e ∈ p.arrows := by
  simp [arrows_eq_projectFromSource p, List.mem_map_of_injective originalArrow_injective]

/-- Recover every original arrow occurrence of the source prefix in order. -/
theorem map_arrows_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    (projectFromSource p).snd.arrows.map originalArrow = p.arrows.tail := by
  simp [arrows_eq_projectFromSource p]

/-- Removing the source arrow preserves and reflects simplicity. -/
@[simp]
theorem isPath_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    (projectFromSource p).snd.IsPath ↔ p.IsPath := by
  rw [← isPath_liftFromSource (B := B) (projectFromSource p).fst.property,
    liftFromSource_projectFromSource]

/-- Project an auxiliary-terminal walk to its untrimmed original segment. It may still pass
through further vertices of `A ∪ B`, and it retains every original arrow occurrence. -/
def project
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) : Projection p := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · let q := projectFromSource p
      refine ⟨q.fst.val, q.fst.property, b, mem_of_sink e, q.snd, ?_⟩
      rw [lift_eq_cons, liftFromSource_projectFromSource, ← eq_sink e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

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

/-- Projection removes exactly the two auxiliary arrows. -/
theorem Projection.length_add_two
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    P.walk.length + 2 = p.length := by
  rw [← length_lift P.source_mem P.target_mem, P.lift_walk]

@[simp]
theorem Projection.length_walk
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    P.walk.length = p.length - 2 := by
  rw [← P.length_add_two, Nat.add_sub_cancel]

@[simp]
theorem Projection.mem_vertices_walk
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) (v : V) :
    v ∈ P.walk.vertices ↔ inl v ∈ p.vertices := by
  simp [P.vertices_eq]

/-- Recover the vertex list of the original segment in order. -/
theorem Projection.map_vertices_walk
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    P.walk.vertices.map inl = p.vertices.tail.dropLast := by
  simp [P.vertices_eq]

@[simp]
theorem Projection.mem_arrows_walk
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p)
    (e : Σ a b, Q a b) : e ∈ P.walk.arrows ↔ originalArrow e ∈ p.arrows := by
  simp [P.arrows_eq, List.mem_map_of_injective originalArrow_injective]

/-- Recover every original arrow occurrence in order. -/
theorem Projection.map_arrows_walk
    {p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)} (P : Projection p) :
    P.walk.arrows.map originalArrow = p.arrows.tail.dropLast := by
  simp [P.arrows_eq]

/-- An empty source-terminal set gives no walk between the auxiliary terminals. -/
instance instIsEmptyWalkSourceEmpty [IsEmpty A] :
    IsEmpty (ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :=
  ⟨fun p ↦ isEmptyElim (⟨(project p).source, (project p).source_mem⟩ : A)⟩

/-- An empty sink-terminal set gives no walk between the auxiliary terminals. -/
instance instIsEmptyWalkSinkEmpty [IsEmpty B] :
    IsEmpty (ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :=
  ⟨fun p ↦ isEmptyElim (⟨(project p).target, (project p).target_mem⟩ : B)⟩

variable (Q A B) in
/-- Walks through the auxiliary terminals correspond to original walks with first endpoint in
`A` and last endpoint in `B`. Repetitions and zero-length original segments are allowed. -/
def walkEquiv :
    (Σ a : A, Σ b : B, ArrowWalk Q a.val b.val) ≃
      ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) where
  toFun p := lift p.fst.property p.snd.fst.property p.snd.snd
  invFun p :=
    let P := project p
    ⟨⟨P.source, P.source_mem⟩, ⟨P.target, P.target_mem⟩, P.walk⟩
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩
    -- Reduce the projection of the final sink arrow to the source-prefix projection.
    change (⟨(projectFromSource (liftFromSource (B := B) ha p)).fst, ⟨b, hb⟩,
      (projectFromSource (liftFromSource (B := B) ha p)).snd⟩ :
        Σ a : A, Σ b : B, ArrowWalk Q a.val b.val) = ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩
    rw [projectFromSource_liftFromSource]
  right_inv p := (project p).lift_walk

@[simp]
theorem walkEquiv_apply (p : Σ a : A, Σ b : B, ArrowWalk Q a.val b.val) :
    walkEquiv Q A B p = lift p.fst.property p.snd.fst.property p.snd.snd :=
  (rfl)

/-- The inverse equivalence extracts exactly the endpoints and walk of the projection. -/
theorem walkEquiv_symm_apply
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (walkEquiv Q A B).symm p =
      ⟨⟨(project p).source, (project p).source_mem⟩,
        ⟨(project p).target, (project p).target_mem⟩, (project p).walk⟩ :=
  (rfl)

/-- Lifting a walk with fixed endpoints is injective. -/
theorem lift_injective {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    Function.Injective (lift (Q := Q) ha hb) := by
  intro p q h
  have h' : walkEquiv Q A B ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩ = walkEquiv Q A B ⟨⟨a, ha⟩, ⟨b, hb⟩, q⟩ := by
    simpa only [walkEquiv_apply] using h
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using (walkEquiv Q A B).injective h'

@[simp]
theorem lift_inj {a b : V} (ha : a ∈ A) (hb : b ∈ B) {p q : ArrowWalk Q a b} :
    lift ha hb p = lift ha hb q ↔ p = q :=
  (lift_injective ha hb).eq_iff

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
      reachableAvoiding_def.2 ⟨P.walk, fun v hv ↦ hp (inl v) ((P.mem_vertices_walk v).1 hv)⟩⟩
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
