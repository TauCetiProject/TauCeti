/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subspaces of equal dimension are exchanged by an automorphism

In a finite-dimensional normed space over a complete field, two subspaces of the same dimension
are mapped onto each other by a continuous linear automorphism: extend a linear equivalence between
them to the whole space (`Submodule.exists_linearEquiv_restrict_eq`) and use that linear maps on a
finite-dimensional space over a complete field are continuous. (Over an incomplete field the latter
fails: a finite-dimensional space can carry inequivalent norms.)

## Main results

* `Submodule.exists_continuousLinearEquiv_mem_iff`.
-/

public section

namespace Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Subspaces of equal dimension are exchanged by an automorphism.** In a finite-dimensional
space over a complete field, two subspaces of the same dimension are mapped onto each other by a
continuous linear automorphism. -/
theorem exists_continuousLinearEquiv_mem_iff
    (V L : Submodule 𝕜 E) (h : Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ Φ : E ≃L[𝕜] E, ∀ z, z ∈ V ↔ Φ z ∈ L := by
  obtain ⟨g, hg⟩ := V.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq V L h)
  refine ⟨g.toContinuousLinearEquiv, fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩⟩
  · simp [← hg ⟨z, hz⟩]
  · set w := (LinearEquiv.ofFinrankEq V L h).symm ⟨g z, hz⟩
    have hw : g w = g z := by rw [← hg w, LinearEquiv.apply_symm_apply]
    exact g.injective hw ▸ w.2

end Submodule
