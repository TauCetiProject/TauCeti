/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Transporting point-spectral subspaces along linear equivalences

Conjugating an endomorphism `A : Module.End 𝕜 E` by a linear equivalence `e : E ≃ₗ[𝕜] F` carries
each eigenspace of `A` onto the corresponding eigenspace of `e.conj A`, and therefore maps every
point-spectral subspace `A.pointSpectralSubspace Ω` onto `(e.conj A).pointSpectralSubspace Ω`.
-/

public section

namespace Module.End

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Conjugating an endomorphism by a linear equivalence maps each of its point-spectral subspaces
onto the corresponding point-spectral subspace of the conjugate. -/
theorem map_pointSpectralSubspace_conj (e : E ≃ₗ[𝕜] F) (A : Module.End 𝕜 E) (Ω : Set ℝ) :
    (A.pointSpectralSubspace Ω).map e.toLinearMap = (e.conj A).pointSpectralSubspace Ω := by
  rw [pointSpectralSubspace_eq_iSup, pointSpectralSubspace_eq_iSup, Submodule.map_iSup]
  refine iSup_congr fun μ ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [TauCeti.eigenspace_eq_comap_of_intertwine (e := e) (f := A) (g := e.conj A) (fun _ ↦ by simp)
    (μ : 𝕜), Submodule.map_comap_eq_self (by simp)]

end Module.End
