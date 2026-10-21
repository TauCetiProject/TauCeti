/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Regression examples for the presentations of back-and-forth systems

These downstream examples check repeated entries, empty structures, nullary relations, and
application of the presentation comparison to Scott sentences using the public API.
-/

namespace TauCeti

open FirstOrder FirstOrder.Language

variable [Language.empty.Structure Bool] [Language.empty.Structure Empty]
  [Language.empty.Structure Unit]

-- Three repeated entries yield a one-point partial equivalence, not a three-point bijection.
example : ∃ (f : Language.empty.FGEquiv Bool Bool) (a : Fin 3 → f.1.dom),
    (f.1.dom : Set Bool) = {false} ∧
      (∀ i, (a i : Bool) = false) ∧ (∀ i, f.1.toEmbedding (a i) = true) := by
  have h : SameAtomicType (L := Language.empty)
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => true) := by
    rw [sameAtomicType_iff]
    exact ⟨fun _ _ => by simp, fun r => isEmptyElim r⟩
  obtain ⟨f, a, ha, hb, hd⟩ := h.exists_fgEquiv
  exact ⟨f, a, by simpa using hd, ha, hb⟩

-- The empty pair is retained when passing from partial equivalences to tuple systems and back.
example : PotentialIso (L := Language.empty) Empty Empty := by
  obtain ⟨S, hS⟩ :=
    (Language.Equiv.refl Language.empty Empty).potentialIso.exists_isTupleBFSystem
  exact hS.potentialIso

-- A tuple system must extend on the second side even if the first structure is empty.
example : ¬ PotentialIso (L := Language.empty) Empty Unit := by
  intro h
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  obtain ⟨x, _⟩ := hS.back hS.empty_mem ()
  exact isEmptyElim x

-- Opposite nullary interpretations obstruct a system even when both structures are empty.
example :
    letI L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
    letI : L₀.IsRelational := fun _ => inferInstance
    letI : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
    letI : L₀.Structure (ULift Empty) := ⟨fun f => Empty.elim f, fun _ _ => False⟩
    ¬ PotentialIso (L := L₀) Empty (ULift Empty) := by
  let L₀ : Language := ⟨fun _ => Empty, fun k => PLift (k = 0)⟩
  let : L₀.IsRelational := fun _ => inferInstance
  let : L₀.Structure Empty := ⟨fun f => Empty.elim f, fun _ _ => True⟩
  let : L₀.Structure (ULift Empty) := ⟨fun f => Empty.elim f, fun _ _ => False⟩
  intro h
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  exact ((hS.sameAtomicType hS.empty_mem).rel_iff (k := 0) ⟨rfl⟩ Fin.elim0).mp trivial

-- The Scott-sentence application includes the empty structure.
example : PotentialIso (L := Language.empty) Empty Empty :=
  potentialIso_of_realize_scottSentence Empty (realize_scottSentence_self Empty)

end TauCeti
