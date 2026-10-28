/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.Basic
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Induced labeled copies of colored three-uniform patterns

A `FiniteColored3Pattern` is a total coloring on `Fin k`. Its induced copies in a host
are injective vertex maps matching every triple color, including any designated nonedge
color. `Colored3Graph.inducedCopyCount` counts these labeled maps without dividing by
automorphisms. It is bounded by the falling factorial of the host size.

Patterns with fewer than three vertices impose no color conditions. Constant patterns in
constant hosts of the same color attain the falling-factorial bound, whereas a conflicting
pattern color forces the count to vanish.
-/

public section

namespace TauCeti

/-- A finite labeled three-uniform pattern, with one color for every unordered triple. -/
@[ext]
structure FiniteColored3Pattern (κ : Type*) where
  /-- The number of labeled vertices. -/
  k : ℕ
  /-- The total coloring on the labeled vertices. -/
  graph : Colored3Graph κ (Fin k)

namespace FiniteColored3Pattern

variable {κ : Type*}

/-- The pattern with `k` labeled vertices and constant triple color `c`. -/
def const (k : ℕ) (c : κ) : FiniteColored3Pattern κ := ⟨k, Colored3Graph.const c⟩

@[simp]
theorem k_const (k : ℕ) (c : κ) : (const k c).k = k := (rfl)

@[simp]
theorem graph_const (k : ℕ) (c : κ) :
    (const k c).graph = Colored3Graph.const c := (rfl)

/-- The color of the triple `{i, j, l}` of pattern vertices, given in increasing order. -/
def tripleColor (F : FiniteColored3Pattern κ) (i j l : Fin F.k) (hij : i < j) (hjl : j < l) : κ :=
  F.graph.color (Set.powersetCard.ofCard (s := {i, j, l})
    (Finset.card_eq_three.2 ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩))

theorem tripleColor_def (F : FiniteColored3Pattern κ) (i j l : Fin F.k) (hij : i < j)
    (hjl : j < l) :
    F.tripleColor i j l hij hjl = F.graph.color (Set.powersetCard.ofCard (s := {i, j, l})
      (Finset.card_eq_three.2 ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩)) :=
  (rfl)

end FiniteColored3Pattern

namespace Colored3Graph

variable {κ V : Type*}

/-- An injection realizes the pattern if it preserves every triple color. -/
def IsInducedCopy (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ) (f : Fin F.k ↪ V) :
    Prop :=
  H.comap f = F.graph

theorem isInducedCopy_iff (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ)
    (f : Fin F.k ↪ V) :
    H.IsInducedCopy F f ↔ ∀ s : Set.powersetCard (Fin F.k) 3,
      H.color (Set.powersetCard.map 3 f s) = F.graph.color s := by
  simp only [IsInducedCopy, Colored3Graph.ext_iff, funext_iff, color_comap]

/-- A pattern with fewer than three vertices has no triple constraints. -/
theorem isInducedCopy_of_lt_three (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ)
    (h : F.k < 3) (f : Fin F.k ↪ V) : H.IsInducedCopy F f := by
  rw [isInducedCopy_iff]
  intro s
  have := Finset.card_le_univ s.val
  simp only [Fintype.card_fin, Set.powersetCard.card_eq] at this
  omega

/-- Restricting the host composes the underlying injection. -/
@[simp]
theorem isInducedCopy_comap_iff {W : Type*} (H : Colored3Graph κ V)
    (F : FiniteColored3Pattern κ) (f : W ↪ V) (g : Fin F.k ↪ W) :
    (H.comap f).IsInducedCopy F g ↔ H.IsInducedCopy F (g.trans f) := by
  simp only [IsInducedCopy, comap_comap]

variable [Fintype V]

/-- All labeled induced copies, represented by their vertex embeddings. -/
noncomputable def inducedCopies (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ) :
    Finset (Fin F.k ↪ V) := by
  classical
  exact Finset.univ.filter (H.IsInducedCopy F)

@[simp]
theorem mem_inducedCopies (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ)
    (f : Fin F.k ↪ V) : f ∈ H.inducedCopies F ↔ H.IsInducedCopy F f := by
  classical
  simp [inducedCopies]

/-- The number of labeled induced injections of `F` into `H`. -/
noncomputable def inducedCopyCount (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ) : ℕ :=
  (H.inducedCopies F).card

theorem inducedCopyCount_def (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ) :
    H.inducedCopyCount F = (H.inducedCopies F).card := (rfl)

/-- A positive induced count is equivalent to the existence of a color-preserving injection. -/
theorem inducedCopyCount_pos_iff (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ) :
    0 < H.inducedCopyCount F ↔ ∃ f, H.IsInducedCopy F f := by
  rw [inducedCopyCount_def, Finset.card_pos]
  simp only [Finset.Nonempty, mem_inducedCopies]

/-- The induced count never exceeds the number of vertex injections. -/
theorem inducedCopyCount_le (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ) :
    H.inducedCopyCount F ≤ (Fintype.card V).descFactorial F.k := by
  classical
  rw [inducedCopyCount_def]
  calc
    (H.inducedCopies F).card ≤ Fintype.card (Fin F.k ↪ V) :=
      Finset.card_le_univ _
    _ = (Fintype.card V).descFactorial F.k := by
      simp [Fintype.card_embedding_eq]

/-- A pattern larger than the host has no induced injections. -/
theorem inducedCopyCount_eq_zero_of_card_lt (H : Colored3Graph κ V)
    (F : FiniteColored3Pattern κ) (h : Fintype.card V < F.k) : H.inducedCopyCount F = 0 := by
  exact Nat.eq_zero_of_le_zero ((H.inducedCopyCount_le F).trans_eq (Nat.descFactorial_of_lt h))

/-- Below three vertices every injection is induced, independently of the coloring. -/
theorem inducedCopyCount_of_lt_three (H : Colored3Graph κ V) (F : FiniteColored3Pattern κ)
    (h : F.k < 3) : H.inducedCopyCount F = (Fintype.card V).descFactorial F.k := by
  classical
  have hall : H.inducedCopies F = Finset.univ := by
    ext f
    simp [H.isInducedCopy_of_lt_three F h f]
  simp [inducedCopyCount_def, hall, Fintype.card_embedding_eq]

/-- Constant colorings with the same color admit every injection. -/
@[simp]
theorem inducedCopyCount_const (c : κ) (k : ℕ) :
    (const c : Colored3Graph κ V).inducedCopyCount (FiniteColored3Pattern.const k c) =
      (Fintype.card V).descFactorial k := by
  classical
  have hall : (const c : Colored3Graph κ V).inducedCopies
      (FiniteColored3Pattern.const k c) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro f
    apply (mem_inducedCopies _ _ f).mpr
    simp only [IsInducedCopy, FiniteColored3Pattern.graph_const, comap_const]
  simp [inducedCopyCount_def, hall, Fintype.card_embedding_eq]

/-- A constant host cannot realize a pattern containing a different triple color. -/
theorem inducedCopyCount_const_eq_zero (c : κ) (F : FiniteColored3Pattern κ)
    (h : ∃ s, F.graph.color s ≠ c) : (const c : Colored3Graph κ V).inducedCopyCount F = 0 := by
  classical
  obtain ⟨s, hs⟩ := h
  rw [inducedCopyCount_def, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  apply hs
  simpa using ((isInducedCopy_iff _ _ _).mp ((mem_inducedCopies _ _ _).mp hf) s).symm

end Colored3Graph

end TauCeti
