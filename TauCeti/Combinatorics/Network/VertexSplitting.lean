/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Excess
public import TauCeti.Combinatorics.Network.Walk

/-!
# Vertex splitting

Splitting the vertices of a directed network turns constraints on vertices into constraints on
arrows. Every vertex `v` is replaced by an entrance `v⁻ = (v, false)` and an exit
`v⁺ = (v, true)` on the vertex type `V × Bool`. Every original arrow `e` from `v` to `w` is
retained, with its identity, as an arrow from `v⁺` to `w⁻`, and every vertex `v`, including an
isolated vertex or one carrying loops, receives one *split arrow* from `v⁻` to `v⁺`. There are no
other arrows; in particular an original loop at `v` becomes an arrow from `v⁺` to `v⁻`.

Since the only arrow leaving an entrance is its split arrow and every arrow entering an exit is
a split arrow, a walk in the split network starting at an entrance alternates between split
arrows and original arrows. Such walks are therefore exactly the lifts of walks in the original
network: a walk from `s` to `t` lifts to a walk from `s⁻` to `t⁻`, or to `t⁺` when the split
arrow of `t` is appended, and projection, which forgets the split arrows, inverts lifting. The
lift of a path is a path, and conversely.

An assignment on the split network consists of an assignment on the original arrows together
with a value on each split arrow. Its excess at `v⁻` is the value entering `v` along original
arrows minus the value on the split arrow of `v`, and its excess at `v⁺` is the value on the
split arrow minus the value leaving `v` along original arrows. Conservation at both copies of
`v` therefore says that the value entering `v`, the value on its split arrow and the value
leaving `v` all agree, and it implies conservation of the original assignment at `v`. Since
original conservation alone does not determine the value on the split arrow, both copies are
needed. Under a capacity `c v` on the split arrow of `v`, conservation at `v⁻` bounds the total
traffic through `v` by `c v`; this is how vertex capacities and vertex separators are reduced to
arrow capacities and arrow cuts.

## Main definitions

* `TauCeti.SplitHom Q`: the arrow family of the network obtained from `Q` by splitting every
  vertex, with its original arrows `TauCeti.SplitHom.original` and its split arrows
  `TauCeti.SplitHom.split`.
* `TauCeti.ArrowWalk.splitLift`: the lift of a walk to the split network.
* `TauCeti.ArrowWalk.splitProj`: the projection of a walk in the split network, which forgets its
  split arrows.
* `TauCeti.ArrowWalk.splitEquiv`: lifting identifies the walks from `s` to `t` with the walks in
  the split network from `s⁻` to either copy of `t`.
* `TauCeti.SplitHom.assignment f φ`: the split assignment with the values of `f` on original
  arrows and `φ v` on the split arrow of `v`; with capacities for `f` and `φ` these are the split
  capacities.
* `TauCeti.SplitHom.network`: the split network, with zero lower bounds and the split capacities
  as upper bounds.
* `TauCeti.SplitHom.originalAssignment g`: the values of a split assignment on original arrows.

## Main results

* `TauCeti.ArrowWalk.isPath_splitLift`: lifting preserves and reflects paths.
* `TauCeti.ArrowWalk.length_splitLift`: a walk with `k` arrows lifts to a walk with `2 * k` or
  `2 * k + 1` arrows.
* `TauCeti.SplitHom.excessAt_entrance` and `TauCeti.SplitHom.excessAt_exit`: the excesses of a
  split assignment at the two copies of a vertex.
* `TauCeti.SplitHom.excessAt_originalAssignment`: the excess of the original part of a split
  assignment at `v` is the sum of its excesses at `v⁻` and `v⁺`.
* `TauCeti.SplitHom.excessAt_entrance_eq_zero_and_excessAt_exit_eq_zero_iff`: conservation at
  both copies of `v` means that the incoming value, the split value and the outgoing value agree.
* `TauCeti.SplitHom.arrowSum_originalAssignment_univ_singleton_le` and
  `TauCeti.SplitHom.arrowSum_originalAssignment_singleton_univ_le`: a split-arrow capacity bounds
  the traffic entering and leaving its vertex.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} (Q : V → V → Type v)

/-- The arrow family of the network obtained from `Q` by splitting every vertex `v` into an
entrance `(v, false)` and an exit `(v, true)`. The arrows from `(v, true)` to `(w, false)` are the
original arrows of `Q v w`; there is exactly one arrow from `(v, false)` to `(v, true)`, the split
arrow of `v`; and there are no other arrows. -/
abbrev SplitHom : V × Bool → V × Bool → Type v
  | (v, true), (w, false) => Q v w
  | (v, false), (w, true) => {_u : PUnit.{v + 1} // v = w}
  | (_, true), (_, true) => PEmpty
  | (_, false), (_, false) => PEmpty

instance SplitHom.instFintype [DecidableEq V] [∀ v w, Fintype (Q v w)] :
    ∀ x y, Fintype (SplitHom Q x y)
  | (v, true), (w, false) => inferInstanceAs (Fintype (Q v w))
  | (v, false), (w, true) => inferInstanceAs (Fintype {_u : PUnit // v = w})
  | (_, true), (_, true) => inferInstanceAs (Fintype PEmpty)
  | (_, false), (_, false) => inferInstanceAs (Fintype PEmpty)

namespace SplitHom

variable {Q}

/-- An original arrow `e : Q v w`, as an arrow from the exit of `v` to the entrance of `w`. -/
def original {v w : V} (e : Q v w) : SplitHom Q (v, true) (w, false) :=
  e

/-- The split arrow of `v`, from its entrance to its exit. -/
def split (v : V) : SplitHom Q (v, false) (v, true) :=
  ⟨PUnit.unit, rfl⟩

/-- The only arrow from the entrance of `v` to its exit is the split arrow of `v`. -/
theorem eq_split {v : V} (e : SplitHom Q (v, false) (v, true)) : e = split v :=
  Subtype.ext rfl

/-- The walk in `Q` traced by an arrow of the split network: an original arrow traces itself and a
split arrow traces the walk of length zero. -/
def toWalk : ∀ {x y : V × Bool}, SplitHom Q x y → ArrowWalk Q x.1 y.1
  | (_, true), (_, false), e => (ArrowWalk.nil _).cons e
  | (_, false), (_, true), ⟨_, rfl⟩ => ArrowWalk.nil _

@[simp]
theorem toWalk_original {v w : V} (e : Q v w) :
    (original e).toWalk = (ArrowWalk.nil v).cons e :=
  (rfl)

@[simp]
theorem toWalk_split (v : V) : (split v : SplitHom Q _ _).toWalk = ArrowWalk.nil v :=
  (rfl)

end SplitHom

namespace ArrowWalk

variable {Q}

/-- The lift of a walk from `s` to `t` to the split network: it starts at the entrance of `s`,
crosses the split arrow of every vertex it visits, and ends at the entrance of `t` for
`b = false` and at the exit of `t` for `b = true`. -/
def splitLift {s : V} : ∀ {t : V} (b : Bool), ArrowWalk Q s t →
    ArrowWalk (SplitHom Q) (s, false) (t, b)
  | _, false, @Quiver.Path.nil _ .(_) _ => nil _
  | _, true, @Quiver.Path.nil _ .(_) _ => (nil _).cons (SplitHom.split s)
  | _, false, @Quiver.Path.cons _ .(_) _ _ _ p e =>
    (splitLift true p).cons (SplitHom.original e)
  | _, true, @Quiver.Path.cons _ .(_) _ _ _ p e =>
    ((splitLift true p).cons (SplitHom.original e)).cons (SplitHom.split _)

@[simp]
theorem splitLift_false_nil (s : V) : (nil s : ArrowWalk Q s s).splitLift false = nil (s, false) :=
  (rfl)

@[simp]
theorem splitLift_false_cons {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) :
    (p.cons e).splitLift false = (p.splitLift true).cons (SplitHom.original e) :=
  (rfl)

@[simp]
theorem splitLift_true_nil (s : V) :
    (nil s : ArrowWalk Q s s).splitLift true = (nil (s, false)).cons (SplitHom.split s) :=
  (rfl)

@[simp]
theorem splitLift_true_cons {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) :
    (p.cons e).splitLift true =
      ((p.splitLift true).cons (SplitHom.original e)).cons (SplitHom.split x) :=
  (rfl)

/-- The lift ending at the exit of `t` is the lift ending at its entrance followed by the split
arrow of `t`. -/
theorem splitLift_true {s t : V} (p : ArrowWalk Q s t) :
    p.splitLift true = (p.splitLift false).cons (SplitHom.split t) := by
  cases p <;> rfl

/-- The projection of a walk in the split network to `Q`, which forgets its split arrows and keeps
its original arrows. -/
def splitProj {x : V × Bool} : ∀ {y : V × Bool}, ArrowWalk (SplitHom Q) x y → ArrowWalk Q x.1 y.1
  | _, @Quiver.Path.nil _ .(_) _ => nil _
  | _, @Quiver.Path.cons _ .(_) _ _ _ p e => (splitProj p).comp e.toWalk

@[simp]
theorem splitProj_nil (x : V × Bool) : (nil x : ArrowWalk (SplitHom Q) x x).splitProj = nil x.1 :=
  (rfl)

@[simp]
theorem splitProj_cons {x y z : V × Bool} (p : ArrowWalk (SplitHom Q) x y)
    (e : SplitHom Q y z) : (p.cons e).splitProj = p.splitProj.comp e.toWalk :=
  (rfl)

/-- Projection inverts lifting. -/
@[simp]
theorem splitProj_splitLift {s t : V} (b : Bool) (p : ArrowWalk Q s t) :
    (p.splitLift b).splitProj = p := by
  induction p generalizing b with
  | nil => cases b <;> rfl
  | cons p e ih =>
    cases b
    · simp [ih, comp]
    · simp [splitLift_true, ih, comp]

/-- Every walk in the split network starting at an entrance is the lift of its projection. -/
@[simp]
theorem splitLift_splitProj {s : V} {y : V × Bool} (q : ArrowWalk (SplitHom Q) (s, false) y) :
    q.splitProj.splitLift y.2 = q := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    rename_i z y
    rcases z with ⟨u, _ | _⟩ <;> rcases y with ⟨w, _ | _⟩
    · exact e.elim
    · obtain rfl : u = w := e.2
      rw [SplitHom.eq_split e, splitProj_cons, SplitHom.toWalk_split, splitLift_true]
      simpa [comp] using ih
    · obtain ⟨e, rfl⟩ : ∃ e' : Q u w, SplitHom.original e' = e := ⟨e, rfl⟩
      rw [splitProj_cons, SplitHom.toWalk_original]
      simp [comp, ih]
    · exact e.elim

/-- Projection takes composition of walks to composition. -/
@[simp]
theorem splitProj_comp {x y z : V × Bool} (p : ArrowWalk (SplitHom Q) x y)
    (q : ArrowWalk (SplitHom Q) y z) : (p.comp q).splitProj = p.splitProj.comp q.splitProj := by
  induction q with
  | nil => simp [comp]
  | cons q e ih => simp only [comp] at ih ⊢; simp [ih, comp]

/-- A walk in the split network starting at the exit of `s` is the lift of its projection with the
split arrow of `s` removed from the front. -/
theorem splitLift_splitProj_of_exit {s : V} {y : V × Bool}
    (q : ArrowWalk (SplitHom Q) (s, true) y) :
    q.splitProj.splitLift y.2 = ((nil (s, false)).cons (SplitHom.split s)).comp q := by
  rw [← splitLift_splitProj (((nil (s, false)).cons (SplitHom.split s)).comp q), splitProj_comp]
  simp [comp]

variable (Q) in
/-- Lifting identifies the walks from `s` to `t` with the walks in the split network from the
entrance of `s` to the entrance (`b = false`) or exit (`b = true`) of `t`; the inverse is
projection. -/
def splitEquiv (s t : V) (b : Bool) :
    ArrowWalk Q s t ≃ ArrowWalk (SplitHom Q) (s, false) (t, b) where
  toFun := splitLift b
  invFun := splitProj
  left_inv := splitProj_splitLift b
  right_inv := splitLift_splitProj

@[simp]
theorem splitEquiv_apply {s t : V} (b : Bool) (p : ArrowWalk Q s t) :
    splitEquiv Q s t b p = p.splitLift b :=
  (rfl)

@[simp]
theorem splitEquiv_symm_apply {s t : V} (b : Bool)
    (q : ArrowWalk (SplitHom Q) (s, false) (t, b)) : (splitEquiv Q s t b).symm q = q.splitProj :=
  (rfl)

/-- A walk with `k` arrows lifts to a walk with `2 * k` arrows ending at an entrance, or `2 * k + 1`
arrows ending at an exit. -/
@[simp]
theorem length_splitLift {s t : V} (b : Bool) (p : ArrowWalk Q s t) :
    (p.splitLift b).length = 2 * p.length + b.toNat := by
  induction p generalizing b with
  | nil => cases b <;> rfl
  | cons p e ih =>
    simp only [length] at ih ⊢
    cases b <;> simp [splitLift_true, ih] <;> omega

/-- The vertices of the lift ending at an exit: each vertex `v` of the walk is replaced by its
entrance and its exit. -/
theorem vertices_splitLift_true {s t : V} (p : ArrowWalk Q s t) :
    (p.splitLift true).vertices = p.vertices.flatMap fun v ↦ [(v, false), (v, true)] := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [vertices, splitLift_true, splitLift_false_cons] at ih ⊢
    simp [Quiver.Path.vertices_cons, ih]

/-- The vertices of the lift of a nonempty walk ending at an entrance: the vertices of the lift of
its prefix ending at an exit, followed by the entrance of its last vertex. -/
theorem vertices_splitLift_false_cons {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) :
    ((p.cons e).splitLift false).vertices = (p.splitLift true).vertices ++ [(x, false)] := by
  simp [Quiver.Path.vertices_cons]

/-- A vertex of the split network lies on the lift of a walk ending at an exit exactly when its
underlying vertex lies on the walk. -/
@[simp]
theorem mem_vertices_splitLift_true {s t : V} {p : ArrowWalk Q s t} {x : V × Bool} :
    x ∈ (p.splitLift true).vertices ↔ x.1 ∈ p.vertices := by
  rcases x with ⟨v, _ | _⟩ <;> simp [vertices_splitLift_true]

/-- Lifting preserves and reflects paths. -/
@[simp]
theorem isPath_splitLift {s t : V} (b : Bool) (p : ArrowWalk Q s t) :
    (p.splitLift b).IsPath ↔ p.IsPath := by
  have htrue : ∀ {t : V} (p : ArrowWalk Q s t), (p.splitLift true).IsPath ↔ p.IsPath := by
    intro t p
    rw [isPath_def, isPath_def, vertices_splitLift_true, List.nodup_flatMap,
      and_iff_right fun v _ ↦ by simp]
    exact List.Pairwise.iff fun a b ↦ by simp [Function.onFun, eq_comm]
  cases b
  · cases p with
    | nil => simp [isPath_def]
    | cons p e =>
      rw [isPath_def, vertices_splitLift_false_cons, List.nodup_append, ← isPath_def, htrue,
        isPath_def, isPath_def]
      simp [Quiver.Path.vertices_cons, List.nodup_append]
  · exact htrue p

/-- A walk in the split network from the entrance of `s` is a path exactly when its projection
is. -/
@[simp]
theorem isPath_splitProj {s : V} {y : V × Bool} {q : ArrowWalk (SplitHom Q) (s, false) y} :
    q.splitProj.IsPath ↔ q.IsPath := by
  conv_rhs => rw [← splitLift_splitProj q]
  exact (isPath_splitLift _ _).symm

/-- The length of a walk in the split network from the entrance of `s` is twice the length of its
projection, plus one when it ends at an exit. -/
theorem length_splitProj {s : V} {y : V × Bool} (q : ArrowWalk (SplitHom Q) (s, false) y) :
    2 * q.splitProj.length + y.2.toNat = q.length := by
  conv_rhs => rw [← splitLift_splitProj q]
  exact (length_splitLift _ _).symm

/-- The arrows traversed by the lift ending at an exit: the split arrow of `s`, followed, for each
arrow of the walk, by that arrow and the split arrow of its target. -/
theorem arrows_splitLift_true {s t : V} (p : ArrowWalk Q s t) :
    (p.splitLift true).arrows = ⟨_, _, SplitHom.split s⟩ :: p.arrows.flatMap fun a ↦
      [⟨(a.1, true), (a.2.1, false), SplitHom.original a.2.2⟩, ⟨_, _, SplitHom.split a.2.1⟩] := by
  induction p with
  | nil => simp [splitLift_true]
  | cons p e ih =>
    rw [splitLift_true, splitLift_false_cons, arrows_cons, arrows_cons, ih, arrows_cons]
    simp

/-- The lift of a walk ending at an exit traverses an original arrow exactly when the walk
traverses it. -/
@[simp]
theorem original_mem_arrows_splitLift_true {s t v w : V} {p : ArrowWalk Q s t} {e : Q v w} :
    ⟨(v, true), (w, false), SplitHom.original e⟩ ∈ (p.splitLift true).arrows ↔
      ⟨v, w, e⟩ ∈ p.arrows := by
  simp only [arrows_splitLift_true, List.mem_cons, List.mem_flatMap]
  constructor
  · rintro (h | ⟨⟨x, y, e'⟩, ha, h | h | h⟩)
    · cases h
    · cases h
      exact ha
    · cases h
    · cases h
  · exact fun h ↦ .inr ⟨_, h, .inl rfl⟩

/-- The lift of a walk ending at an exit traverses the split arrow of `v` exactly when the walk
visits `v`. -/
@[simp]
theorem split_mem_arrows_splitLift_true {s t v : V} {p : ArrowWalk Q s t} :
    ⟨(v, false), (v, true), SplitHom.split v⟩ ∈ (p.splitLift true).arrows ↔ v ∈ p.vertices := by
  have hv : p.vertices = s :: p.arrows.map (fun a ↦ a.2.1) := by
    rw [map_target_arrows]
    exact List.eq_cons_of_mem_head? (@Quiver.Path.vertices_head? V ⟨Q⟩ s t p)
  rw [hv]
  simp only [arrows_splitLift_true, List.mem_cons, List.mem_flatMap, List.mem_map]
  constructor
  · rintro (h | ⟨⟨x, y, e'⟩, ha, h | h | h⟩)
    · cases h
      exact .inl rfl
    · cases h
    · cases h
      exact .inr ⟨_, ha, rfl⟩
    · cases h
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨a, ha, .inr (.inl rfl)⟩

end ArrowWalk

/-! ### Assignments on the split network -/

namespace SplitHom

variable {Q} {K : Type w}

/-- The assignment on the split network with the value `f e` on each original arrow `e` and the
value `φ v` on the split arrow of each vertex `v`. With capacities `cap` on the original arrows and
`c v` on the split arrow of `v`, the split capacities are `assignment cap c`. -/
def assignment (f : Assignment Q K) (φ : V → K) : Assignment (SplitHom Q) K
  | (_, true), (_, false), e => f e
  | (v, false), (_, true), _ => φ v
  | (_, true), (_, true), e => e.elim
  | (_, false), (_, false), e => e.elim

@[simp]
theorem assignment_original (f : Assignment Q K) (φ : V → K) {v w : V} (e : Q v w) :
    assignment f φ (original e) = f e :=
  (rfl)

@[simp]
theorem assignment_split (f : Assignment Q K) (φ : V → K) (v : V) :
    assignment f φ (split v) = φ v :=
  (rfl)

/-- The values of an assignment on the split network on the original arrows. -/
def originalAssignment (g : Assignment (SplitHom Q) K) : Assignment Q K :=
  fun _ _ e ↦ g (original e)

@[simp]
theorem originalAssignment_apply (g : Assignment (SplitHom Q) K) {v w : V} (e : Q v w) :
    originalAssignment g e = g (original e) :=
  (rfl)

@[simp]
theorem originalAssignment_assignment (f : Assignment Q K) (φ : V → K) :
    originalAssignment (assignment f φ) = f :=
  (rfl)

/-- Every assignment on the split network is determined by its values on the original arrows and
on the split arrows. -/
theorem assignment_originalAssignment (g : Assignment (SplitHom Q) K) :
    assignment (originalAssignment g) (fun v ↦ g (split v)) = g := by
  funext x y e
  rcases x with ⟨v, _ | _⟩ <;> rcases y with ⟨w, _ | _⟩
  · exact e.elim
  · obtain rfl : v = w := e.2
    rw [eq_split e, assignment_split]
  · rfl
  · exact e.elim

/-- Two assignments on the split network are equal when they agree on the original arrows and on
the split arrows. -/
theorem assignment_ext {g g' : Assignment (SplitHom Q) K}
    (h : originalAssignment g = originalAssignment g') (h' : ∀ v, g (split v) = g' (split v)) :
    g = g' := by
  rw [← assignment_originalAssignment g, ← assignment_originalAssignment g', h, funext h']

@[simp]
theorem assignment_zero [Zero K] : assignment (0 : Assignment Q K) 0 = 0 :=
  assignment_ext rfl fun _ ↦ rfl

/-- Split assignments are compared arrowwise on original arrows and vertexwise on split
arrows. -/
@[simp]
theorem assignment_le_assignment_iff [LE K] {f f' : Assignment Q K} {φ φ' : V → K} :
    assignment f φ ≤ assignment f' φ' ↔ f ≤ f' ∧ φ ≤ φ' := by
  constructor
  · exact fun h ↦ ⟨fun v w e ↦ h _ _ (original e), fun v ↦ h _ _ (split v)⟩
  · rintro ⟨hf, hφ⟩ ⟨v, _ | _⟩ ⟨w, _ | _⟩ e
    · exact e.elim
    · exact hφ v
    · exact hf v w e
    · exact e.elim

/-- The split network: zero lower bounds, the capacity `cap e` on each original arrow `e` and the
capacity `c v` on the split arrow of each vertex `v`. The body is exposed because the dependent
arrow family occurs in the types of the projection lemmas below. -/
@[expose]
def network [Zero K] [LE K] (cap : Assignment Q K) (hcap : ∀ {v w} (e : Q v w), 0 ≤ cap e)
    (c : V → K) (hc : ∀ v, 0 ≤ c v) : Network K (V × Bool) :=
  Network.ofCapacity (SplitHom Q) (assignment cap c) fun {x y} e ↦ by
    rcases x with ⟨v, _ | _⟩ <;> rcases y with ⟨w, _ | _⟩
    · exact e.elim
    · exact hc v
    · exact hcap e
    · exact e.elim

section Network

variable [Zero K] [LE K] (cap : Assignment Q K) (hcap : ∀ {v w} (e : Q v w), 0 ≤ cap e)
  (c : V → K) (hc : ∀ v, 0 ≤ c v)

@[simp]
theorem network_Hom : (network cap hcap c hc).Hom = SplitHom Q :=
  (rfl)

@[simp]
theorem network_lower {x y : V × Bool} (e : SplitHom Q x y) :
    (network cap hcap c hc).lower e = 0 :=
  (rfl)

@[simp]
theorem network_upper {x y : V × Bool} (e : SplitHom Q x y) :
    (network cap hcap c hc).upper e = assignment cap c e :=
  (rfl)

end Network

section Excess

variable [AddCommGroup K] [Fintype V] [DecidableEq V] (g : Assignment (SplitHom Q) K) (v : V)

/-- The only arrow from the entrance of `v` to an exit, and the only arrow from an entrance to the
exit of `v`, is the split arrow of `v`. So the value of a split assignment on the arrows leaving an
entrance, or entering an exit, is its value on the split arrow. -/
private theorem sum_sum_split (v : V) :
    (∑ w, ∑ e : SplitHom Q (v, false) (w, true), g e = g (split v)) ∧
      ∑ w, ∑ e : SplitHom Q (w, false) (v, true), g e = g (split v) := by
  constructor
  · rw [Fintype.sum_eq_single v fun w hw ↦ Finset.sum_eq_zero fun e _ ↦ (hw e.2.symm).elim]
    exact Fintype.sum_eq_single (split v) fun e he ↦ (he (eq_split e)).elim
  · rw [Fintype.sum_eq_single v fun w hw ↦ Finset.sum_eq_zero fun e _ ↦ (hw e.2).elim]
    exact Fintype.sum_eq_single (split v) fun e he ↦ (he (eq_split e)).elim

variable [∀ v w, Fintype (Q v w)]

/-- The excess of a split assignment at the entrance `(v, false)` is the value entering `v` along
original arrows minus the value on the split arrow of `v`. -/
theorem excessAt_entrance :
    excessAt g (v, false) = arrowSum (originalAssignment g) univ {v} - g (split v) := by
  rw [excessAt_def, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, univ_eq_empty, sum_empty, (sum_sum_split g v).1, add_zero,
    arrowSum_def, sum_singleton]
  -- Arrows from an exit to an entrance are original arrows, summed with the `Fintype` instance of
  -- `Q`, so these sums are the sums of `originalAssignment g` by definition.
  rfl

/-- The excess of a split assignment at the exit `(v, true)` is the value on the split arrow of
`v` minus the value leaving `v` along original arrows. -/
theorem excessAt_exit :
    excessAt g (v, true) = g (split v) - arrowSum (originalAssignment g) {v} univ := by
  rw [excessAt_def, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, univ_eq_empty, sum_empty, (sum_sum_split g v).2, zero_add,
    arrowSum_def, sum_singleton]
  -- As in `excessAt_entrance`, the sums over original arrows hold by definition.
  rfl

/-- The excess of the original part of a split assignment at `v` is the sum of its excesses at
the entrance and at the exit of `v`. -/
theorem excessAt_originalAssignment :
    excessAt (originalAssignment g) v = excessAt g (v, false) + excessAt g (v, true) := by
  rw [excessAt_entrance, excessAt_exit, excessAt_eq_arrowSum_sub]
  abel

/-- A split assignment is conserved at both copies of `v` exactly when the value entering `v` along
original arrows, the value on the split arrow of `v` and the value leaving `v` along original
arrows agree. -/
theorem excessAt_entrance_eq_zero_and_excessAt_exit_eq_zero_iff :
    excessAt g (v, false) = 0 ∧ excessAt g (v, true) = 0 ↔
      arrowSum (originalAssignment g) univ {v} = g (split v) ∧
        g (split v) = arrowSum (originalAssignment g) {v} univ := by
  rw [excessAt_entrance, excessAt_exit, sub_eq_zero, sub_eq_zero]

/-- Conservation of a split assignment at both copies of `v` implies conservation of its original
part at `v`. -/
theorem excessAt_originalAssignment_eq_zero {g : Assignment (SplitHom Q) K} {v : V}
    (h₀ : excessAt g (v, false) = 0) (h₁ : excessAt g (v, true) = 0) :
    excessAt (originalAssignment g) v = 0 := by
  rw [excessAt_originalAssignment, h₀, h₁, add_zero]

variable [LE K] {c : K} {g}

/-- **Vertex capacities.** If a split assignment has value at most `c` on the split arrow of `v`
and is conserved at the entrance of `v`, then the total value entering `v` along original arrows is
at most `c`. -/
theorem arrowSum_originalAssignment_univ_singleton_le (hg : g (split v) ≤ c)
    (h : excessAt g (v, false) = 0) : arrowSum (originalAssignment g) univ {v} ≤ c := by
  rw [excessAt_entrance, sub_eq_zero] at h
  exact h ▸ hg

/-- If a split assignment has value at most `c` on the split arrow of `v` and is conserved at the
exit of `v`, then the total value leaving `v` along original arrows is at most `c`. -/
theorem arrowSum_originalAssignment_singleton_univ_le (hg : g (split v) ≤ c)
    (h : excessAt g (v, true) = 0) : arrowSum (originalAssignment g) {v} univ ≤ c := by
  rw [excessAt_exit, sub_eq_zero, eq_comm] at h
  exact h ▸ hg

end Excess

end SplitHom

end TauCeti
