/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Compose

/-!
# Stacking Brauer diagrams is associative

Vertical stacking of Brauer diagrams, `TauCeti.composeDiagram`, is associative: stacking `D₁`
above `D₂` and the result above `D₃` gives the same matching of the outer boundary as stacking
`D₂` above `D₃` and `D₁` above that. This is the underlying-matching half of the associativity
of the Brauer algebra, whose multiplication is the composite diagram weighted by `δ` raised to
the middle-loop count of `TauCeti/Combinatorics/Brauer/LoopCount.lean`.

The proof reads both bracketings off one and the same walk, the walk along a strand of the
**three-fold** stack of `D₁` above `D₂` above `D₃`. That stack has two middle boundaries, an
upper one between `D₁` and `D₂` and a lower one between `D₂` and `D₃`, and a strand that has
reached a middle point is about to run either up or down through one of the three diagrams; the
four resulting middle states, together with the outer point at which the strand has already
left the stack, are the positions of the walk.

Only one direction of the comparison is needed in each bracketing, because the walk is a
*function*: a strand leaves the three-fold stack at most once, so the outer point at which it
leaves is unique. So it suffices to prove of *each* bracketing that the point it matches with
`x` is a point at which the strand of the three-fold stack starting at `x` leaves, and the two
are then equal without ever chopping a walk of the three-fold stack into walks of a two-fold
one.

That one direction is in turn a simulation statement, and the same one twice. A two-fold stack
occurring inside a bracketing embeds into the three-fold stack: its middle states are two of the
four, and the outer points at which its strands leave are either genuine outer points of the
three-fold stack or middle states of it. Under that embedding one step of the two-fold walk is
finitely many steps of the three-fold walk -- one step where the two-fold stack uses a diagram
directly, and the walk of the inner stack where it uses a composite -- and
a lemma on simulations of iterates turns that into the same statement for iterates.

## Main results

* `TauCeti.composeDiagram_assoc`: **stacking Brauer diagrams is associative.**

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, "Brauer diagrams and the Brauer algebra".
-/

public section

namespace TauCeti

variable {k : ℕ}

/-! ### Simulating one walk by another -/

/-- If every step of `f` is simulated by finitely many steps of `g` along `Φ`, then so is every
iterate of `f`. -/
private theorem exists_iterate_of_forall_exists_iterate {α β : Type*} {f : α → α} {g : β → β}
    {Φ : α → β} (h : ∀ a, ∃ m, g^[m] (Φ a) = Φ (f a)) (n : ℕ) (a : α) :
    ∃ m, g^[m] (Φ a) = Φ (f^[n] a) := by
  induction n generalizing a with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m₁, h₁⟩ := h a
    obtain ⟨m₂, h₂⟩ := ih (f a)
    exact ⟨m₂ + m₁, by rw [Function.iterate_add_apply, h₁, h₂, Function.iterate_succ_apply]⟩

/-! ### The walk along a strand of a stack of two diagrams -/

/-- The walk along a strand of the stack of `D₁` above `D₂`, as a **total** function on the
positions `TauCeti.stackStep` takes its values in: an outer point at which the strand has
already left the stack stays put, and a middle state is carried on by `TauCeti.stackStep`. -/
private def stackWalk (D₁ D₂ : BrauerDiagram k) :
    (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) :=
  Sum.elim Sum.inl (stackStep D₁ D₂)

/-- A strand that has left the stack stays where it is. -/
private theorem stackWalk_inl (D₁ D₂ : BrauerDiagram k) (y : Fin k ⊕ Fin k) :
    stackWalk D₁ D₂ (Sum.inl y) = Sum.inl y := (rfl)

/-- From a middle state the walk follows `TauCeti.stackStep`. -/
private theorem stackWalk_inr (D₁ D₂ : BrauerDiagram k) (s : Fin k ⊕ Fin k) :
    stackWalk D₁ D₂ (Sum.inr s) = stackStep D₁ D₂ s := (rfl)

/-- A chain of `TauCeti.stackStep` steps between middle states is a run of the walk. -/
private theorem exists_iterate_stackWalk_of_reflTransGen (D₁ D₂ : BrauerDiagram k)
    {s t : Fin k ⊕ Fin k}
    (h : Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t) :
    ∃ m, (stackWalk D₁ D₂)^[m] (Sum.inr s) = Sum.inr t := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, by rw [Function.iterate_succ_apply', hm, stackWalk_inr, hstep]⟩

/-- **The composite reads off where the walk leaves the stack.** If the stack of `D₁` above `D₂`
matches the outer point `x` with `y`, then the walk starting along the first arc of the strand at
`x` leaves the stack at `y` after finitely many steps. -/
private theorem exists_iterate_stackWalk (D₁ D₂ : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (h : (composeDiagram D₁ D₂).val x = y) :
    ∃ n, (stackWalk D₁ D₂)^[n] (stackStart D₁ D₂ x) = Sum.inl y := by
  rcases (composeDiagram_val_eq_iff D₁ D₂).mp h with hstart | ⟨s, t, hstart, hpath, hexit⟩
  · exact ⟨0, hstart⟩
  · obtain ⟨m, hm⟩ := exists_iterate_stackWalk_of_reflTransGen D₁ D₂ hpath
    exact ⟨m + 1, by rw [hstart, Function.iterate_succ_apply', hm, stackWalk_inr, hexit]⟩

/-! ### The walk along a strand of a stack of three diagrams -/

/-- The positions of the walk along a strand of the stack of `D₁` above `D₂` above `D₃`.

`Sum.inl y` records that the strand has left the stack at the outer point `y`, a bottom point of
`D₃` or a top point of `D₁`. The remaining positions are the middle states, a point of one of the
two middle boundaries together with the diagram the strand runs through next: on the **upper**
middle boundary, between `D₁` and `D₂`, the strand runs up through `D₁` at
`Sum.inr (Sum.inl (Sum.inl a))` and down through `D₂` at `Sum.inr (Sum.inl (Sum.inr a))`; on the
**lower** one, between `D₂` and `D₃`, it runs up through `D₂` at
`Sum.inr (Sum.inr (Sum.inl a))` and down through `D₃` at `Sum.inr (Sum.inr (Sum.inr a))`. -/
private abbrev TriplePos (k : ℕ) : Type :=
  (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)

/-- Following a strand of the stack of `D₁` above `D₂` above `D₃` one arc further. A strand that
has left the stack stays put; otherwise the arc of the diagram named by the middle state either
leaves the stack or arrives at a middle point, at which the strand turns into the next diagram
along. -/
private def tripleStep (D₁ D₂ D₃ : BrauerDiagram k) : TriplePos k → TriplePos k :=
  Sum.elim Sum.inl <|
    Sum.elim
      (Sum.elim
        (fun a => (D₁.val (Sum.inl a)).elim (fun a' => Sum.inr (Sum.inl (Sum.inr a')))
          fun j => Sum.inl (Sum.inr j))
        fun a => (D₂.val (Sum.inr a)).elim (fun i => Sum.inr (Sum.inr (Sum.inr i)))
          fun a' => Sum.inr (Sum.inl (Sum.inl a')))
      (Sum.elim
        (fun a => (D₂.val (Sum.inl a)).elim (fun a' => Sum.inr (Sum.inr (Sum.inr a')))
          fun b => Sum.inr (Sum.inl (Sum.inl b)))
        fun a => (D₃.val (Sum.inr a)).elim (fun i => Sum.inl (Sum.inl i))
          fun a' => Sum.inr (Sum.inr (Sum.inl a')))

/-- Following the strand of the stack of `D₁` above `D₂` above `D₃` that starts at the outer
point `x` along its first arc, an arc of `D₃` at a bottom point and an arc of `D₁` at a top
point. -/
private def tripleStart (D₁ D₃ : BrauerDiagram k) : (Fin k ⊕ Fin k) → TriplePos k :=
  Sum.elim
    (fun i => (D₃.val (Sum.inl i)).elim (fun i' => Sum.inl (Sum.inl i'))
      fun a => Sum.inr (Sum.inr (Sum.inl a)))
    fun j => (D₁.val (Sum.inr j)).elim (fun b => Sum.inr (Sum.inl (Sum.inr b)))
      fun j' => Sum.inl (Sum.inr j')

/-- A strand that has left the three-fold stack stays where it is. -/
private theorem tripleStep_inl (D₁ D₂ D₃ : BrauerDiagram k) (y : Fin k ⊕ Fin k) :
    tripleStep D₁ D₂ D₃ (Sum.inl y) = Sum.inl y := (rfl)

/-- A strand that has left the three-fold stack stays where it is, however long the walk runs. -/
private theorem iterate_tripleStep_inl (D₁ D₂ D₃ : BrauerDiagram k) (n : ℕ)
    (y : Fin k ⊕ Fin k) : (tripleStep D₁ D₂ D₃)^[n] (Sum.inl y) = Sum.inl y :=
  Function.iterate_fixed (tripleStep_inl D₁ D₂ D₃ y) n

/-- **A strand leaves the three-fold stack at one point only.** The walk is a function, so two
runs of it out of the same position that both leave the stack leave it at the same outer
point. -/
private theorem eq_of_iterate_tripleStep (D₁ D₂ D₃ : BrauerDiagram k) {p : TriplePos k}
    {y y' : Fin k ⊕ Fin k} {n n' : ℕ} (h : (tripleStep D₁ D₂ D₃)^[n] p = Sum.inl y)
    (h' : (tripleStep D₁ D₂ D₃)^[n'] p = Sum.inl y') : y = y' := by
  rcases le_total n n' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, h, iterate_tripleStep_inl] at h'
    exact Sum.inl_injective h'
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [Nat.add_comm, Function.iterate_add_apply, h', iterate_tripleStep_inl] at h
    exact (Sum.inl_injective h).symm

/-! ### The upper two diagrams inside the three-fold stack -/

/-- The stack of `D₁` above `D₂` inside the stack of `D₁` above `D₂` above `D₃`. Its middle
states are the two upper ones; a strand leaving it at one of its own bottom points arrives on the
lower middle boundary and runs on down into `D₃`, and one leaving it at a top point has left the
three-fold stack. -/
private def upperEmbed : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) → TriplePos k :=
  Sum.elim (Sum.elim (fun a => Sum.inr (Sum.inr (Sum.inr a))) fun j => Sum.inl (Sum.inr j))
    fun s => Sum.inr (Sum.inl s)

/-- One step of the walk of the upper two-fold stack is one step of the three-fold walk. -/
private theorem tripleStep_upperEmbed (D₁ D₂ D₃ : BrauerDiagram k)
    (p : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (upperEmbed p) = upperEmbed (stackWalk D₁ D₂ p) := by
  rcases p with z | (b | b)
  · exact ⟨0, by rw [Function.iterate_zero_apply, stackWalk_inl]⟩
  · refine ⟨1, ?_⟩
    rcases h : D₁.val (Sum.inl b) with a' | j <;>
      simp [stackWalk_inr, tripleStep, upperEmbed, h]
  · refine ⟨1, ?_⟩
    rcases h : D₂.val (Sum.inr b) with i | a' <;>
      simp [stackWalk_inr, tripleStep, upperEmbed, h]

/-- The first arc of a strand of the upper two-fold stack that starts on the lower middle
boundary is the arc the three-fold walk follows from there. -/
private theorem upperEmbed_stackStart_inl (D₁ D₂ D₃ : BrauerDiagram k) (a : Fin k) :
    upperEmbed (stackStart D₁ D₂ (Sum.inl a)) =
      tripleStep D₁ D₂ D₃ (Sum.inr (Sum.inr (Sum.inl a))) := by
  rcases h : D₂.val (Sum.inl a) with a' | b <;> simp [tripleStep, upperEmbed, h]

/-- The first arc of a strand of the upper two-fold stack that starts at a top point is the first
arc of the corresponding strand of the three-fold stack. -/
private theorem upperEmbed_stackStart_inr (D₁ D₂ D₃ : BrauerDiagram k) (j : Fin k) :
    upperEmbed (stackStart D₁ D₂ (Sum.inr j)) = tripleStart D₁ D₃ (Sum.inr j) := by
  rcases h : D₁.val (Sum.inr j) with b | j' <;> simp [tripleStart, upperEmbed, h]

/-! ### The lower two diagrams inside the three-fold stack -/

/-- The stack of `D₂` above `D₃` inside the stack of `D₁` above `D₂` above `D₃`. Its middle
states are the two lower ones; a strand leaving it at one of its own top points arrives on the
upper middle boundary and runs on up into `D₁`, and one leaving it at a bottom point has left the
three-fold stack. -/
private def lowerEmbed : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) → TriplePos k :=
  Sum.elim (Sum.elim (fun i => Sum.inl (Sum.inl i)) fun b => Sum.inr (Sum.inl (Sum.inl b)))
    fun s => Sum.inr (Sum.inr s)

/-- One step of the walk of the lower two-fold stack is one step of the three-fold walk. -/
private theorem tripleStep_lowerEmbed (D₁ D₂ D₃ : BrauerDiagram k)
    (p : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (lowerEmbed p) = lowerEmbed (stackWalk D₂ D₃ p) := by
  rcases p with z | (a | a)
  · exact ⟨0, by rw [Function.iterate_zero_apply, stackWalk_inl]⟩
  · refine ⟨1, ?_⟩
    rcases h : D₂.val (Sum.inl a) with a' | b <;>
      simp [stackWalk_inr, tripleStep, lowerEmbed, h]
  · refine ⟨1, ?_⟩
    rcases h : D₃.val (Sum.inr a) with i | a' <;>
      simp [stackWalk_inr, tripleStep, lowerEmbed, h]

/-- The first arc of a strand of the lower two-fold stack that starts at a bottom point is the
first arc of the corresponding strand of the three-fold stack. -/
private theorem lowerEmbed_stackStart_inl (D₁ D₂ D₃ : BrauerDiagram k) (i : Fin k) :
    lowerEmbed (stackStart D₂ D₃ (Sum.inl i)) = tripleStart D₁ D₃ (Sum.inl i) := by
  rcases h : D₃.val (Sum.inl i) with i' | a <;> simp [tripleStart, lowerEmbed, h]

/-- The first arc of a strand of the lower two-fold stack that starts on the upper middle
boundary is the arc the three-fold walk follows from there. -/
private theorem lowerEmbed_stackStart_inr (D₁ D₂ D₃ : BrauerDiagram k) (b : Fin k) :
    lowerEmbed (stackStart D₂ D₃ (Sum.inr b)) =
      tripleStep D₁ D₂ D₃ (Sum.inr (Sum.inl (Sum.inr b))) := by
  rcases h : D₂.val (Sum.inr b) with i | a <;> simp [tripleStep, lowerEmbed, h]

/-! ### Both bracketings leave the three-fold stack at the same point -/

/-- **An arc of the upper composite is a run of the three-fold walk.** -/
private theorem exists_iterate_tripleStep_of_upper (D₁ D₂ D₃ : BrauerDiagram k)
    {w z : Fin k ⊕ Fin k} (h : (composeDiagram D₁ D₂).val w = z) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (upperEmbed (stackStart D₁ D₂ w)) = upperEmbed (Sum.inl z) := by
  obtain ⟨n, hn⟩ := exists_iterate_stackWalk D₁ D₂ h
  obtain ⟨m, hm⟩ := exists_iterate_of_forall_exists_iterate (tripleStep_upperEmbed D₁ D₂ D₃) n
    (stackStart D₁ D₂ w)
  exact ⟨m, by rw [hm, hn]⟩

/-- **An arc of the lower composite is a run of the three-fold walk.** -/
private theorem exists_iterate_tripleStep_of_lower (D₁ D₂ D₃ : BrauerDiagram k)
    {w z : Fin k ⊕ Fin k} (h : (composeDiagram D₂ D₃).val w = z) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (lowerEmbed (stackStart D₂ D₃ w)) = lowerEmbed (Sum.inl z) := by
  obtain ⟨n, hn⟩ := exists_iterate_stackWalk D₂ D₃ h
  obtain ⟨m, hm⟩ := exists_iterate_of_forall_exists_iterate (tripleStep_lowerEmbed D₁ D₂ D₃) n
    (stackStart D₂ D₃ w)
  exact ⟨m, by rw [hm, hn]⟩

/-- The stack of the upper composite above `D₃` inside the three-fold stack: its middle states
are the two lower ones, and it leaves the stack where the three-fold walk does. -/
private def leftEmbed : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) → TriplePos k :=
  Sum.elim Sum.inl fun s => Sum.inr (Sum.inr s)

/-- One step of the walk of the stack of `D₁ ∘ D₂` above `D₃` is finitely many steps of the
three-fold walk. -/
private theorem tripleStep_leftEmbed (D₁ D₂ D₃ : BrauerDiagram k)
    (p : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (leftEmbed p) =
      leftEmbed (stackWalk (composeDiagram D₁ D₂) D₃ p) := by
  rcases p with z | (a | a)
  · exact ⟨0, by rw [Function.iterate_zero_apply, stackWalk_inl]⟩
  · obtain ⟨m, hm⟩ := exists_iterate_tripleStep_of_upper D₁ D₂ D₃ (w := Sum.inl a)
      (z := (composeDiagram D₁ D₂).val (Sum.inl a)) rfl
    rw [upperEmbed_stackStart_inl D₁ D₂ D₃ a] at hm
    refine ⟨m + 1, ?_⟩
    have hrun : (tripleStep D₁ D₂ D₃)^[m + 1] (leftEmbed (Sum.inr (Sum.inl a)))
        = upperEmbed (Sum.inl ((composeDiagram D₁ D₂).val (Sum.inl a))) := by
      rw [Function.iterate_succ_apply]; exact hm
    rw [hrun]
    rcases h : (composeDiagram D₁ D₂).val (Sum.inl a) with a' | j <;>
      simp [stackWalk_inr, leftEmbed, upperEmbed, h]
  · refine ⟨1, ?_⟩
    rcases h : D₃.val (Sum.inr a) with i | a' <;>
      simp [stackWalk_inr, tripleStep, leftEmbed, h]

/-- The stack of `D₁` above the lower composite inside the three-fold stack: its middle states
are the two upper ones, and it leaves the stack where the three-fold walk does. -/
private def rightEmbed : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k) → TriplePos k :=
  Sum.elim Sum.inl fun s => Sum.inr (Sum.inl s)

/-- One step of the walk of the stack of `D₁` above `D₂ ∘ D₃` is finitely many steps of the
three-fold walk. -/
private theorem tripleStep_rightEmbed (D₁ D₂ D₃ : BrauerDiagram k)
    (p : (Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (rightEmbed p) =
      rightEmbed (stackWalk D₁ (composeDiagram D₂ D₃) p) := by
  rcases p with z | (b | b)
  · exact ⟨0, by rw [Function.iterate_zero_apply, stackWalk_inl]⟩
  · refine ⟨1, ?_⟩
    rcases h : D₁.val (Sum.inl b) with a' | j <;>
      simp [stackWalk_inr, tripleStep, rightEmbed, h]
  · obtain ⟨m, hm⟩ := exists_iterate_tripleStep_of_lower D₁ D₂ D₃ (w := Sum.inr b)
      (z := (composeDiagram D₂ D₃).val (Sum.inr b)) rfl
    rw [lowerEmbed_stackStart_inr D₁ D₂ D₃ b] at hm
    refine ⟨m + 1, ?_⟩
    have hrun : (tripleStep D₁ D₂ D₃)^[m + 1] (rightEmbed (Sum.inr (Sum.inr b)))
        = lowerEmbed (Sum.inl ((composeDiagram D₂ D₃).val (Sum.inr b))) := by
      rw [Function.iterate_succ_apply]; exact hm
    rw [hrun]
    rcases h : (composeDiagram D₂ D₃).val (Sum.inr b) with i | a <;>
      simp [stackWalk_inr, rightEmbed, lowerEmbed, h]

/-- **The left bracketing leaves the three-fold stack where it says.** -/
private theorem exists_iterate_tripleStep_left (D₁ D₂ D₃ : BrauerDiagram k)
    (x : Fin k ⊕ Fin k) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (tripleStart D₁ D₃ x) =
      Sum.inl ((composeDiagram (composeDiagram D₁ D₂) D₃).val x) := by
  obtain ⟨m₁, h₁⟩ : ∃ m, (tripleStep D₁ D₂ D₃)^[m] (tripleStart D₁ D₃ x) =
      leftEmbed (stackStart (composeDiagram D₁ D₂) D₃ x) := by
    rcases x with i | j
    · refine ⟨0, ?_⟩
      rcases h : D₃.val (Sum.inl i) with i' | a <;> simp [tripleStart, leftEmbed, h]
    · obtain ⟨m, hm⟩ := exists_iterate_tripleStep_of_upper D₁ D₂ D₃ (w := Sum.inr j)
        (z := (composeDiagram D₁ D₂).val (Sum.inr j)) rfl
      rw [upperEmbed_stackStart_inr D₁ D₂ D₃ j] at hm
      refine ⟨m, ?_⟩
      rw [hm]
      rcases h : (composeDiagram D₁ D₂).val (Sum.inr j) with a | j' <;>
        simp [leftEmbed, upperEmbed, h]
  obtain ⟨n, hn⟩ := exists_iterate_stackWalk (composeDiagram D₁ D₂) D₃
    (x := x) (y := (composeDiagram (composeDiagram D₁ D₂) D₃).val x) rfl
  obtain ⟨m₂, h₂⟩ := exists_iterate_of_forall_exists_iterate (tripleStep_leftEmbed D₁ D₂ D₃) n
    (stackStart (composeDiagram D₁ D₂) D₃ x)
  exact ⟨m₂ + m₁, by rw [Function.iterate_add_apply, h₁, h₂, hn]; rfl⟩

/-- **The right bracketing leaves the three-fold stack where it says.** -/
private theorem exists_iterate_tripleStep_right (D₁ D₂ D₃ : BrauerDiagram k)
    (x : Fin k ⊕ Fin k) :
    ∃ m, (tripleStep D₁ D₂ D₃)^[m] (tripleStart D₁ D₃ x) =
      Sum.inl ((composeDiagram D₁ (composeDiagram D₂ D₃)).val x) := by
  obtain ⟨m₁, h₁⟩ : ∃ m, (tripleStep D₁ D₂ D₃)^[m] (tripleStart D₁ D₃ x) =
      rightEmbed (stackStart D₁ (composeDiagram D₂ D₃) x) := by
    rcases x with i | j
    · obtain ⟨m, hm⟩ := exists_iterate_tripleStep_of_lower D₁ D₂ D₃ (w := Sum.inl i)
        (z := (composeDiagram D₂ D₃).val (Sum.inl i)) rfl
      rw [lowerEmbed_stackStart_inl D₁ D₂ D₃ i] at hm
      refine ⟨m, ?_⟩
      rw [hm]
      rcases h : (composeDiagram D₂ D₃).val (Sum.inl i) with i' | a <;>
        simp [rightEmbed, lowerEmbed, h]
    · refine ⟨0, ?_⟩
      rcases h : D₁.val (Sum.inr j) with b | j' <;> simp [tripleStart, rightEmbed, h]
  obtain ⟨n, hn⟩ := exists_iterate_stackWalk D₁ (composeDiagram D₂ D₃)
    (x := x) (y := (composeDiagram D₁ (composeDiagram D₂ D₃)).val x) rfl
  obtain ⟨m₂, h₂⟩ := exists_iterate_of_forall_exists_iterate (tripleStep_rightEmbed D₁ D₂ D₃) n
    (stackStart D₁ (composeDiagram D₂ D₃) x)
  exact ⟨m₂ + m₁, by rw [Function.iterate_add_apply, h₁, h₂, hn]; rfl⟩

/-- **Stacking Brauer diagrams is associative.** Stacking `D₁` above `D₂` and the composite above
`D₃` matches the outer boundary in the same way as stacking `D₂` above `D₃` and `D₁` above that,
because both read off the point at which a strand of the three-fold stack of `D₁` above `D₂`
above `D₃` leaves it. -/
theorem composeDiagram_assoc (D₁ D₂ D₃ : BrauerDiagram k) :
    composeDiagram (composeDiagram D₁ D₂) D₃ = composeDiagram D₁ (composeDiagram D₂ D₃) := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  obtain ⟨m, hm⟩ := exists_iterate_tripleStep_left D₁ D₂ D₃ x
  obtain ⟨n, hn⟩ := exists_iterate_tripleStep_right D₁ D₂ D₃ x
  exact eq_of_iterate_tripleStep D₁ D₂ D₃ hm hn

end TauCeti
