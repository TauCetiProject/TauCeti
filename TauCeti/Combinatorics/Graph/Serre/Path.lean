/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic

/-!
# Paths without immediate reversal in a Serre graph

A path in the quiver of a Serre graph is reduced when no consecutive darts cancel. This
condition retains the distinction between a loop and its reversed dart, and between parallel
edges. It is the local normal-form condition used for graph path groups and Stallings graphs.
-/

public section

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph)

/-- A Serre path has no consecutive pair of mutually reversed darts. -/
def Path.IsReduced {a : Γ.V} : ∀ {b : Γ.V}, Γ.Path a b → Prop
  | _, .nil => True
  | _, .cons .nil _ => True
  | _, .cons (.cons p e) f =>
      Path.IsReduced (.cons p e) ∧ f.1 ≠ Γ.rev e.1

@[simp] theorem Path.isReduced_nil (a : Γ.V) :
    Path.IsReduced Γ (Quiver.Path.nil : Γ.Path a a) := trivial

@[simp] theorem Path.isReduced_toPath {a b : Γ.V} (e : Quiver.Hom a b) :
    Path.IsReduced Γ e.toPath := trivial

/-- The reducedness test for a newly appended dart only examines the preceding dart. -/
@[simp] theorem Path.isReduced_cons_cons {a b c d : Γ.V}
    (p : Γ.Path a b) (e : Quiver.Hom b c)
    (f : Quiver.Hom c d) :
    Path.IsReduced Γ ((p.cons e).cons f) ↔
      Path.IsReduced Γ (p.cons e) ∧ f.1 ≠ Γ.rev e.1 := Iff.rfl

private theorem isReduced_pair_comp {a b c d : Γ.V}
    (e : Quiver.Hom a b) (f : Quiver.Hom b c) (p : Γ.Path c d) :
    Path.IsReduced Γ ((e.toPath.comp f.toPath).comp p) ↔
      f.1 ≠ Γ.rev e.1 ∧ Path.IsReduced Γ (f.toPath.comp p) := by
  induction p with
  | nil => simp [Quiver.Path.comp, Quiver.Hom.toPath, Path.IsReduced]
  | cons p k ih =>
    cases p with
    | nil => simp [Quiver.Path.comp, Quiver.Hom.toPath, Path.IsReduced]
    | cons p l =>
      simp only [Quiver.Path.comp_cons, Path.IsReduced] at ih ⊢
      rw [← and_assoc, ← ih]

/-- Reversing a path preserves the absence of immediate backtracking. -/
@[simp] theorem Path.isReduced_reverse {a b : Γ.V} (p : Γ.Path a b) :
    Path.IsReduced Γ p.reverse ↔ Path.IsReduced Γ p := by
  induction p with
  | nil => simp [Path.IsReduced]
  | cons p e ih =>
    cases p with
    | nil => simp [Quiver.Path.reverse, Path.IsReduced]
    | cons p f =>
      rw [Quiver.Path.reverse, Quiver.Path.reverse, ← Quiver.Path.comp_assoc,
        isReduced_pair_comp]
      simp only [reverse_val, Γ.rev_rev, Path.isReduced_cons_cons]
      exact (and_congr (ne_comm : Γ.rev f.1 ≠ e.1 ↔ e.1 ≠ Γ.rev f.1) ih).trans and_comm

/-- Traversing a rose petal and then its reverse is a backtrack. -/
theorem rose_not_isReduced_backtrack {α : Type*} (a : α) :
    ¬ Path.IsReduced (rose α)
      ((Quiver.Path.nil.cons ((rose α).dart (a, true))).cons
        ((rose α).dart (a, false))) := by
  simp [Path.IsReduced, rose]

/-- Traversing one rose petal and then the reverse of a different petal is reduced. -/
theorem rose_isReduced_of_ne {α : Type*} {a b : α} (hab : a ≠ b) :
    Path.IsReduced (rose α)
      ((Quiver.Path.nil.cons ((rose α).dart (a, true))).cons
        ((rose α).dart (b, false))) := by
  simpa [Path.IsReduced, rose] using hab.symm

end SerreGraph

end TauCeti
