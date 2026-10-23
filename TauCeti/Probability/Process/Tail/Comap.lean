/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.Basic
import TauCeti.MeasureTheory.MeasurableSpace.Antitone

/-!
# The tail of a process as a pullback

The future and tail σ-algebras of a process composed with a map are the pullbacks of the
original future and tail σ-algebras. In particular, `tailProcess X` is the pullback of
`pathTail α` by the path map `ω ↦ (X i ω)ᵢ`.

These identities connect events on path space with events on the original sample space. They
require no measure, no measurable structure on the sample space and no standard Borel hypothesis
on the state spaces; the composition results also allow dependent coordinate types.
-/

public section

namespace TauCeti.Probability

variable {Ω Ω' : Type*} {β : ℕ → Type*} [∀ k, MeasurableSpace (β k)]

/-- Future σ-algebras commute with composition of a process with an arbitrary map. -/
@[simp]
theorem tailFamily_comp (X : (k : ℕ) → Ω → β k) (f : Ω' → Ω) (n : ℕ) :
    tailFamily (fun k => X k ∘ f) n = MeasurableSpace.comap f (tailFamily X n) := by
  simp only [tailFamily_eq_iSup_comap, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp]

/-- Tail σ-algebras commute with composition of a process with an arbitrary map. -/
theorem tailProcess_comp (X : (k : ℕ) → Ω → β k) (f : Ω' → Ω) :
    tailProcess (fun k => X k ∘ f) = MeasurableSpace.comap f (tailProcess X) := by
  simp only [tailProcess_eq_iInf_tailFamily, tailFamily_comp]
  exact (TauCeti.MeasureTheory.comap_iInf_of_antitone f (tailFamily_antitone X)).symm

/-- The tail σ-algebra on a sample space is exactly the pullback of the path-space tail
σ-algebra by the process path map. -/
theorem tailProcess_eq_comap_pathTail {α : Type*} [MeasurableSpace α]
    (X : ℕ → Ω → α) :
    tailProcess X = MeasurableSpace.comap (fun ω i => X i ω) (pathTail α) :=
  tailProcess_comp (fun k (x : ℕ → α) => x k) (fun ω i => X i ω)

end TauCeti.Probability
