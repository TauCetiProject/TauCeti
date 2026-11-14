/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AuxiliaryTerminals

/-!
# Examples of auxiliary-terminal walk projection

The examples check an overlapping pair of terminal sets, two distinct parallel arrows, and a
walk repeating a loop. In particular projection retains repetitions rather than silently
extracting a path. Empty terminal sets give no walk between the auxiliary terminals.
-/

public section

namespace TauCeti.Examples.AuxiliaryTerminals

open AuxTerminalHom Sum

/-- Two distinct loop arrows on a single vertex. -/
abbrev Loops (_ _ : Unit) := Fin 2

/-- The two terminal sets coincide at the only original vertex. -/
abbrev terminals : Finset Unit := {()}

/-- A common terminal contributes an empty original segment, lifted to a simple two-arrow path. -/
theorem overlapping_terminals :
    let p := liftWalk (Q := Loops) (A := terminals) (B := terminals) (a := ()) (b := ())
      (by simp [terminals]) (by simp [terminals]) (ArrowWalk.nil ())
    p.IsPath ∧ p.length = 2 ∧
      (projectWalk (Q := Loops) (A := terminals) (B := terminals) p).2.2.length = 0 := by
  dsimp only
  rw [projectWalk_liftWalk]
  simp

/-- Distinct parallel loops remain distinct after adjoining the terminal arrows. -/
theorem parallel_loops_ne :
    liftWalk (A := terminals) (B := terminals) (a := ()) (b := ())
      (by simp [terminals]) (by simp [terminals])
      ((ArrowWalk.nil () : ArrowWalk Loops () ()).cons 0) ≠
    liftWalk (A := terminals) (B := terminals) (a := ()) (b := ())
      (by simp [terminals]) (by simp [terminals])
      ((ArrowWalk.nil () : ArrowWalk Loops () ()).cons 1) := by
  intro h
  have hproj := congrArg (projectWalk (Q := Loops) (A := terminals) (B := terminals)) h
  simp only [projectWalk_liftWalk, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hproj
  have harrows := congrArg ArrowWalk.arrows hproj
  simp at harrows

/-- Projection recovers both occurrences of a repeated loop; it does not simplify the walk. -/
theorem repeated_loop_projection :
    let p : ArrowWalk Loops () () := (ArrowWalk.nil () |>.cons (x := ()) 0).cons 0
    let q := liftWalk (A := terminals) (B := terminals) (a := ()) (b := ())
      (by simp [terminals]) (by simp [terminals]) p
    (projectWalk (Q := Loops) (A := terminals) (B := terminals) q).2.2.arrows =
      [⟨(), (), 0⟩, ⟨(), (), 0⟩] ∧ q.length = 4 ∧ ¬q.IsPath := by
  dsimp only
  rw [projectWalk_liftWalk]
  simp [ArrowWalk.isPath_def]

/-- An empty source-terminal set gives no walk between the auxiliary terminals. -/
example {V : Type*} (Q : V → V → Type*) (B : Finset V) :
    IsEmpty (ArrowWalk (AuxTerminalHom Q ∅ B) (inr false) (inr true)) :=
  inferInstance

/-- An empty sink-terminal set gives no walk between the auxiliary terminals. -/
example {V : Type*} (Q : V → V → Type*) (A : Finset V) :
    IsEmpty (ArrowWalk (AuxTerminalHom Q A ∅) (inr false) (inr true)) :=
  inferInstance

end TauCeti.Examples.AuxiliaryTerminals
