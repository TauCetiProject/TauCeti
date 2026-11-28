/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Structure

/-!
# Finite punctures of spaces with a PL structure

By placing vertices at arbitrary finite subsets
(`TauCeti.IsTriangulable.exists_vertex_image_of_compactSpace`) and passing to the complement model
in the barycentric subdivision (`TauCeti.IsTriangulable.finiteCWType_compl`), removing any finite
subset `S` from a space carrying a `PLStructure` (with or without boundary, connected or not, in any
dimension `n`) yields a space `↥Sᶜ` of finite CW type.

## Main results

* `TauCeti.PLStructure.exists_vertex_image`: there is a `PLStructure` `s'` of the same
  dimension on `M` in which `S` is a vertex image.
* `TauCeti.PLStructure.finiteCWType_compl`: removing any finite subset from a space with a
  `PLStructure` preserves `FiniteCWType`.
-/

public section

noncomputable section

namespace TauCeti

universe u

namespace PLStructure

variable {M : Type u} [TopologicalSpace M] {n : ℕ}

/-- Given a `PLStructure` on `M` and a finite subset `S : Set M`, there is a `PLStructure` `s'`
of the same dimension `n` on `M` in which `S` is a vertex image. No boundarylessness,
connectedness, or dimension lower bound is required. -/
theorem exists_vertex_image (s : PLStructure M n) {S : Set M} (hS : S.Finite) :
    ∃ (s' : PLStructure M n) (V : Set s'.ι), s'.e '' (s'.K.vertex '' V) = S := by
  have := s.compactSpace
  obtain ⟨ι', K', e', V, hfin, hman, hV⟩ :=
    s.isCombinatoriallyTriangulable.exists_vertex_image_of_compactSpace hS
  exact ⟨{ ι := ι', K := K', isCombinatorialManifold := hman, e := e' }, V, hV⟩

/-- Removing any finite subset `S : Set M` from a space carrying a `PLStructure` leaves a space
of finite CW type. -/
theorem finiteCWType_compl (s : PLStructure M n) {S : Set M} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ := by
  have := s.compactSpace
  exact s.isCombinatoriallyTriangulable.finiteCWType_compl hS

end PLStructure

end TauCeti
