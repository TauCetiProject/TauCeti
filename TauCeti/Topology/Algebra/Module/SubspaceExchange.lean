/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subspaces of equal dimension are exchanged by an automorphism

In a finite-dimensional normed space over a complete field, two subspaces of the same dimension
are mapped onto each other by a continuous linear automorphism: choose complements, which have
equal dimensions too, and match the two decompositions.

## Main results

* `TauCeti.exists_continuousLinearEquiv_mem_iff`.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Subspaces of equal dimension are exchanged by an automorphism.** In a finite-dimensional
space over a complete field, two subspaces of the same dimension are mapped onto each other by a
continuous linear automorphism. -/
theorem exists_continuousLinearEquiv_mem_iff
    (V L : Submodule 𝕜 E) (h : Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ Φ : E ≃L[𝕜] E, ∀ z, z ∈ V ↔ Φ z ∈ L := by
  obtain ⟨V', hV⟩ := V.exists_isCompl
  obtain ⟨L', hL⟩ := L.exists_isCompl
  have h' : Module.finrank 𝕜 V' = Module.finrank 𝕜 L' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hV
    have h2 := Submodule.finrank_add_eq_of_isCompl hL
    omega
  let Φ : E ≃ₗ[𝕜] E := (Submodule.prodEquivOfIsCompl V V' hV).symm.trans
    (((LinearEquiv.ofFinrankEq V L h).prodCongr (LinearEquiv.ofFinrankEq V' L' h')).trans
      (Submodule.prodEquivOfIsCompl L L' hL))
  refine ⟨Φ.toContinuousLinearEquiv, fun z ↦ ?_⟩
  have h1 := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero V V' hV (x := z)).symm
  have h2 := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L L' hL
    (x := Φ.toContinuousLinearEquiv z)).symm
  rw [h1, h2]
  simp [Φ]


end TauCeti
