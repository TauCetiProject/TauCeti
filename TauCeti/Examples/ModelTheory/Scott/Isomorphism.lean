/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Scott.Isomorphism
import TauCeti.ModelTheory.Scott.PureSet
import Mathlib.ModelTheory.Graph

/-!
# Scott isomorphism regression examples

Use the public Scott-sentence characterizations on a two-vertex complete graph, an empty
pure set, and empty structures with opposite nullary interpretations. The graph examples
distinguish cardinality from relations: both a singleton and a two-vertex edgeless graph
fail its Scott sentence. The level-indexed example uses the stabilizing level zero for a
finite pure set. The existence theorem is also exercised across structure universes.
-/

namespace TauCeti

open FirstOrder FirstOrder.Language

-- Self-realization still simplifies when both Scott-sentence simp rules match.
example {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
    (M : Type w) [L.Structure M] [Countable M] :
    SentenceInf.Realize (scottSentence (L := L) M) M := by
  simp

-- The sentence of a fixed finite relational structure holds in an isomorphic copy.
example :
    letI : Language.graph.Structure (Fin 2) := { RelMap | .adj => fun x => x 0 ≠ x 1 }
    letI : Language.graph.Structure Bool := { RelMap | .adj => fun x => x 0 ≠ x 1 }
    SentenceInf.Realize (scottSentence (L := Language.graph) (Fin 2)) Bool := by
  let : Language.graph.Structure (Fin 2) := { RelMap | .adj => fun x => x 0 ≠ x 1 }
  let : Language.graph.Structure Bool := { RelMap | .adj => fun x => x 0 ≠ x 1 }
  apply (realize_scottSentence_iff (Fin 2) Bool).mpr
  refine ⟨{ toEquiv := finTwoEquiv, map_rel' := ?_ }⟩
  intro n r x
  cases r
  exact finTwoEquiv.injective.ne_iff

-- The same sentence excludes a graph of the wrong size.
example :
    letI : Language.graph.Structure (Fin 2) := { RelMap | .adj => fun x => x 0 ≠ x 1 }
    letI : Language.graph.Structure Unit := { RelMap | .adj => fun x => x 0 ≠ x 1 }
    ¬ SentenceInf.Realize (scottSentence (L := Language.graph) (Fin 2)) Unit := by
  let : Language.graph.Structure (Fin 2) := { RelMap | .adj => fun x => x 0 ≠ x 1 }
  let : Language.graph.Structure Unit := { RelMap | .adj => fun x => x 0 ≠ x 1 }
  rw [realize_scottSentence_iff]
  rintro ⟨e⟩
  have h := Fintype.card_congr e.toEquiv
  simp at h

-- Equal cardinality is insufficient: the edge must be preserved.
example :
    letI : Language.graph.Structure (Fin 2) := { RelMap | .adj => fun x => x 0 ≠ x 1 }
    letI : Language.graph.Structure (ULift Bool) := { RelMap | .adj => fun _ => False }
    ¬ SentenceInf.Realize (scottSentence (L := Language.graph) (Fin 2)) (ULift Bool) := by
  let : Language.graph.Structure (Fin 2) := { RelMap | .adj => fun x => x 0 ≠ x 1 }
  let : Language.graph.Structure (ULift Bool) := { RelMap | .adj => fun _ => False }
  rw [realize_scottSentence_iff]
  rintro ⟨e⟩
  exact (e.map_rel Language.adj ![0, 1]).mpr (by decide : (0 : Fin 2) ≠ 1)

section PureSets

variable [Language.empty.Structure (Fin 2)] [Language.empty.Structure Bool]
  [Language.empty.Structure Empty] [Language.empty.Structure Unit]

-- Any countable internally stabilizing level works, not only the canonical choice.
example : SentenceInf.Realize (scottSentenceAt (L := Language.empty) (Fin 2) 0) Bool := by
  apply (realize_scottSentenceAt_iff (Fin 2) (Ordinal.omega_pos 1)
    (selfStabilizesCompletely_empty (Fin 2)) Bool).mpr
  exact ⟨{ toEquiv := finTwoEquiv }⟩

-- The theorem does not silently assume nonempty structures.
example : ¬ SentenceInf.Realize (scottSentence (L := Language.empty) Empty) Unit := by
  rw [realize_scottSentence_iff]
  rintro ⟨e⟩
  exact isEmptyElim (e.symm ())

end PureSets

-- An empty structure still realizes its own Scott sentence.
example :
    letI L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
    letI : L₀.IsRelational := fun _ => inferInstance
    letI : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
    SentenceInf.Realize (scottSentence (L := L₀) Empty) Empty := by
  let L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
  let : L₀.IsRelational := fun _ => inferInstance
  let : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
  exact realize_scottSentence_self Empty

-- Identical empty carriers do not erase different nullary relation interpretations.
example :
    letI L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
    letI : L₀.IsRelational := fun _ => inferInstance
    letI : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
    letI : L₀.Structure (ULift Empty) := ⟨fun f => Empty.elim f, fun _ _ => False⟩
    ¬ SentenceInf.Realize (scottSentence (L := L₀) Empty) (ULift Empty) := by
  let L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
  let : L₀.IsRelational := fun _ => inferInstance
  let : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
  let : L₀.Structure (ULift Empty) := ⟨fun f => Empty.elim f, fun _ _ => False⟩
  rw [realize_scottSentence_iff]
  rintro ⟨e⟩
  exact (e.map_rel (n := 0) ⟨rfl⟩ Fin.elim0).mpr trivial

-- The existential theorem is usable with models in a larger universe, including empty ones.
example {L : Language} [L.IsRelational] [Countable (Σ k, L.Relations k)]
    (M : Type) [L.Structure M] [Countable M] :
    ∃ σ : L.Sentenceω, SentenceInf.Realize σ M ∧
      ∀ (N : Type 1) [L.Structure N] [Countable N],
        SentenceInf.Realize σ N ↔ Nonempty (M ≃[L] N) :=
  scott_isomorphism M

end TauCeti
