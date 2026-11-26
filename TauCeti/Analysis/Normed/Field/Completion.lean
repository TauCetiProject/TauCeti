/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion

/-!
# The completion of a nontrivially normed field

The coercion of a normed field `L` into its completion preserves the norm
(`UniformSpace.Completion.norm_coe`), so an element of `L` of norm greater than `1` still has norm
greater than `1` in the completion. Hence the completion of a nontrivially normed field is a
nontrivially normed field.
-/

public section

namespace UniformSpace.Completion

/-- The completion of a nontrivially normed field is a nontrivially normed field. -/
noncomputable instance instNontriviallyNormedField {L : Type*} [NontriviallyNormedField L]
    [CompletableTopField L] : NontriviallyNormedField (Completion L) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := L)
    exact ⟨x, by rwa [norm_coe]⟩

end UniformSpace.Completion
