/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AuxiliaryTerminals.Basic

/-!
# Walks through auxiliary terminals

A walk from the fresh source to the fresh sink consists of one source arrow, a walk along
original arrows from a vertex of `A` to a vertex of `B`, and one sink arrow. This factorization
is unique, even for walks that repeat vertices or arrows. It retains all original arrow
identities, including loops and parallel arrows, and restricts to a correspondence of simple
paths. When the terminal sets overlap, the original walk may have length zero.

This is projection without trimming: the original segment may visit further vertices of
`A ∪ B`. Trimming to a set-to-set path is a separate operation and is not invertible.

The auxiliary-terminal construction is the standard reduction of set-to-set path problems to
two-terminal problems; see Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*.
-/

public section

namespace TauCeti.AuxTerminalHom

open Sum

universe u v

variable {V : Type u} {Q : V → V → Type v} {A B : Finset V}

/-- Prepend the source arrow to a walk along original arrows. -/
def liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b) := by
  induction p with
  | nil => exact (ArrowWalk.nil _).cons (source ha)
  | cons _ e ih => exact ih.cons (original e)

@[simp]
theorem liftFromSource_nil {a : V} (ha : a ∈ A) :
    liftFromSource (Q := Q) (B := B) ha (ArrowWalk.nil a) = (ArrowWalk.nil _).cons (source ha) :=
  (rfl)

@[simp]
theorem liftFromSource_cons {a b c : V} (ha : a ∈ A) (p : ArrowWalk Q a b) (e : Q b c) :
    liftFromSource (B := B) ha (p.cons e) = (liftFromSource ha p).cons (original e) :=
  (rfl)

/-- Adjoin the auxiliary source and sink arrows to an original walk. -/
def liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) :=
  (liftFromSource ha p).cons (sink hb)

/-- A walk lifted to both auxiliary terminals is a lifted source prefix followed by its sink
arrow. -/
theorem liftWalk_def {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    liftWalk ha hb p = (liftFromSource ha p).cons (sink hb) :=
  (rfl)

@[simp]
theorem vertices_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).vertices = inr false :: p.vertices.map inl := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

@[simp]
theorem vertices_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).vertices = inr false :: p.vertices.map inl ++ [inr true] := by
  simp [liftWalk_def]

@[simp]
theorem length_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih, Nat.add_assoc]

@[simp]
theorem length_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).length = p.length + 2 := by
  simp [liftWalk_def, Nat.add_assoc]

/-- The inclusion of original arrow identities, with their endpoints. -/
def originalArrow (e : Σ a b, Q a b) : Σ x y, AuxTerminalHom Q A B x y :=
  ⟨inl e.1, inl e.2.1, original e.2.2⟩

@[simp]
theorem originalArrow_mk {a b : V} (e : Q a b) :
    originalArrow (A := A) (B := B) ⟨a, b, e⟩ = ⟨inl a, inl b, original e⟩ :=
  (rfl)

/-- Inclusion retains the identity of each original arrow. -/
theorem originalArrow_injective :
    Function.Injective (originalArrow (Q := Q) (A := A) (B := B)) := by
  rintro ⟨a, b, e⟩ ⟨a', b', e'⟩ h
  have ha : a = a' := inl_injective (congrArg Sigma.fst h)
  subst ha
  have hb : b = b' := inl_injective (congrArg (fun x => x.2.1) h)
  subst hb
  have he : original (A := A) (B := B) e = original e' := by
    simpa only [originalArrow_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  rw [original_inj] at he
  subst he
  rfl

@[simp]
theorem arrows_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).arrows =
      ⟨inr false, inl a, source ha⟩ :: p.arrows.map originalArrow := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, originalArrow]

@[simp]
theorem arrows_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).arrows =
      ⟨inr false, inl a, source ha⟩ :: p.arrows.map originalArrow ++
        [⟨inl b, inr true, sink hb⟩] := by
  simp [liftWalk_def]

/-- An original arrow occurs in a lifted walk exactly when it occurred in the original walk.
This is not a simp lemma because `arrows_liftWalk` first expands the entire arrow list. -/
theorem originalArrow_mem_arrows_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (p : ArrowWalk Q a b) (e : Σ v w, Q v w) :
    originalArrow e ∈ (liftWalk ha hb p).arrows ↔ e ∈ p.arrows := by
  have hs : originalArrow (A := A) (B := B) e ≠ ⟨inr false, inl a, source ha⟩ :=
    fun h => Sum.inl_ne_inr (congrArg Sigma.fst h)
  have ht : originalArrow (A := A) (B := B) e ≠ ⟨inl b, inr true, sink hb⟩ :=
    fun h => Sum.inl_ne_inr (congrArg (fun x => x.2.1) h)
  simp only [arrows_liftWalk, List.mem_cons, List.mem_append, List.not_mem_nil,
    hs, ht, false_or, or_false, List.mem_map_of_injective originalArrow_injective]

/-- Adding auxiliary terminals preserves and reflects simplicity of a walk. -/
@[simp]
theorem isPath_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).IsPath ↔ p.IsPath := by
  simp [ArrowWalk.isPath_def, List.nodup_append, List.nodup_map_iff inl_injective]

/-- A walk from the auxiliary source to an original vertex has a unique original segment. -/
private def projectPrefix {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {b : V} (hy : y = inl b) :
    Σ a : {a // a ∈ A}, ArrowWalk Q a.1 b := by
  induction p generalizing b with
  | nil => exact (Sum.inr_ne_inl hy).elim
  | @cons z y p e ih =>
    subst hy
    rcases z with a | _ | _
    · obtain ⟨a, q⟩ := ih rfl
      exact ⟨a, q.cons (originalEquiv.symm e)⟩
    · exact ⟨⟨b, mem_of_source e⟩, ArrowWalk.nil b⟩
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl b)) e

private theorem projectPrefix_cons {a b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl a))
    (e : AuxTerminalHom Q A B (inl a) (inl b)) :
    projectPrefix (p.cons e) rfl =
      ⟨(projectPrefix p rfl).1, (projectPrefix p rfl).2.cons (originalEquiv.symm e)⟩ :=
  (rfl)

private theorem liftFromSource_projectPrefix {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {b : V} (hy : y = inl b) :
    HEq (liftFromSource (B := B) (projectPrefix p hy).1.2 (projectPrefix p hy).2) p := by
  induction p generalizing b with
  | nil => exact (Sum.inr_ne_inl hy).elim
  | @cons z y p e ih =>
    subst hy
    rcases z with a | _ | _
    · have h := eq_of_heq (ih (b := a) rfl)
      apply heq_of_eq
      rw [projectPrefix_cons, liftFromSource_cons, original_originalEquiv_symm, h]
    · have hp : p = ArrowWalk.nil (inr false) := by
        cases p with
        | nil => rfl
        | @cons z _ p e => exact isEmptyElim (α := AuxTerminalHom Q A B z (inr false)) e
      subst hp
      exact heq_of_eq <| (liftFromSource_nil (Q := Q) (B := B) (mem_of_source e)).trans
        (congrArg (fun f => (ArrowWalk.nil (inr false)).cons f) (eq_source e).symm)
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl b)) e

private theorem projectPrefix_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    projectPrefix (liftFromSource (B := B) ha p) rfl = ⟨⟨a, ha⟩, p⟩ := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [liftFromSource_cons, projectPrefix_cons, ih, originalEquiv_symm_original]

/-- Remove the two auxiliary terminal arrows, retaining the endpoints and every original arrow.
The original segment need not avoid `A ∪ B` in its interior. -/
def projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    Σ a : {a // a ∈ A}, Σ b : {b // b ∈ B}, ArrowWalk Q a.1 b.1 := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · obtain ⟨a, q⟩ := projectPrefix p rfl
      exact ⟨a, ⟨b, mem_of_sink e⟩, q⟩
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

private theorem projectWalk_cons {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b))
    (e : AuxTerminalHom Q A B (inl b) (inr true)) :
    projectWalk (p.cons e) =
      ⟨(projectPrefix p rfl).1, ⟨b, mem_of_sink e⟩, (projectPrefix p rfl).2⟩ :=
  (rfl)

/-- Projection after lifting recovers both endpoints and the entire original walk. -/
@[simp]
theorem projectWalk_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    projectWalk (liftWalk ha hb p) = ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩ := by
  rw [liftWalk_def, projectWalk_cons, projectPrefix_liftFromSource]

/-- Lifting the projected original segment recovers the entire auxiliary walk. -/
@[simp]
theorem liftWalk_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2 (projectWalk p).2.2 = p := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · have h := eq_of_heq (liftFromSource_projectPrefix p (b := b) rfl)
      rw [projectWalk_cons, liftWalk_def, h, ← eq_sink e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

variable (Q A B) in
/-- Walks through the auxiliary terminals correspond to original walks with first endpoint in
`A` and last endpoint in `B`. Repetitions and zero-length original segments are allowed. -/
def walkEquiv :
    (Σ a : {a // a ∈ A}, Σ b : {b // b ∈ B}, ArrowWalk Q a.1 b.1) ≃
      ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) where
  toFun p := liftWalk p.1.2 p.2.1.2 p.2.2
  invFun := projectWalk
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩
    exact projectWalk_liftWalk ha hb p
  right_inv := liftWalk_projectWalk

@[simp]
theorem walkEquiv_apply (p : Σ a : {a // a ∈ A}, Σ b : {b // b ∈ B}, ArrowWalk Q a.1 b.1) :
    walkEquiv Q A B p = liftWalk p.1.2 p.2.1.2 p.2.2 :=
  (rfl)

@[simp]
theorem walkEquiv_symm_apply
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (walkEquiv Q A B).symm p = projectWalk p :=
  (rfl)

/-- Removing auxiliary terminals preserves and reflects simplicity of a walk. -/
@[simp]
theorem isPath_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (projectWalk p).2.2.IsPath ↔ p.IsPath := by
  rw [← isPath_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2, liftWalk_projectWalk]

end TauCeti.AuxTerminalHom
