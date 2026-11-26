/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Flow
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

/-!
# The spectral flow under isometric changes of trivialization

A path of self-adjoint operators often arises written in a trivialization: a family of Hilbert
spaces identified, at each time `t`, with a fixed model by an isometry `U t`. Changing the
trivialization replaces the path `A` on `H` by the conjugated path

`t ↦ U t ∘ A t ∘ (U t)⁻¹`

on another Hilbert space `K`, for linear isometric equivalences `U t : H ≃ₗᵢ[𝕜] K`
(`LinearIsometryEquiv.conjStarAlgEquiv`). This file proves that the spectral flow of Phillips
(`TauCeti.spectralFlow`) does not change (`TauCeti.spectralFlow_conjStarAlgEquiv`).

Isometric conjugation preserves the spectrum and commutes with the continuous functional calculus
(`LinearIsometryEquiv.spectrum_conjStarAlgEquiv`, `LinearIsometryEquiv.cfc_conjStarAlgEquiv`), and
it preserves ranks, so it preserves the ranks of spectral projections. Hence the conjugated path
has the same local eigenvalue counts (`TauCeti.spectralCount_conjStarAlgEquiv`), the same spectral
cuts (`TauCeti.isSpectralCutOn_conjStarAlgEquiv_iff`) and the same spectral flow potentials
(`TauCeti.isSpectralFlowPotential_conjStarAlgEquiv_iff`) as `A`, and so the same spectral flow.
These are pointwise statements, so no continuity of `U` in `t`, and no hypothesis on `A`, is
needed: the spectral flow only sees the eigenvalues of each `A t`, which isometric conjugation does
not move. The same holds for paths on a compactly embedded common domain, in
`TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Conjugation`.

## Main results

* `TauCeti.spectralCount_conjStarAlgEquiv`: isometric conjugation preserves the number of
  eigenvalues in `[0, c]`.
* `TauCeti.isSpectralCutOn_conjStarAlgEquiv_iff`: it preserves spectral cuts.
* `TauCeti.isSpectralFlowPotential_conjStarAlgEquiv_iff`: it preserves spectral flow potentials.
* `TauCeti.spectralFlow_conjStarAlgEquiv`: it preserves the spectral flow.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Set

namespace TauCeti

variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  [NormedAlgebra ℝ (K →L[𝕜] K)] [IsometricContinuousFunctionalCalculus ℝ (K →L[𝕜] K) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (K →L[𝕜] K)]

/-- Isometric conjugation preserves the number of eigenvalues in `[0, c]`, counted with
multiplicity. -/
@[simp]
theorem spectralCount_conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) (c : ℝ) (T : H →L[𝕜] H) :
    spectralCount c (e.conjStarAlgEquiv T) = spectralCount c T := by
  rw [spectralCount_def, spectralCount_def, e.cfc_conjStarAlgEquiv,
    e.finrank_range_conjStarAlgEquiv]

variable {A : ℝ → H →L[𝕜] H} (U : ℝ → H ≃ₗᵢ[𝕜] K)

/-- A number is a spectral cut of a path conjugated by isometries exactly when it is a spectral cut
of the path itself. -/
@[simp]
theorem isSpectralCutOn_conjStarAlgEquiv_iff {c : ℝ} {s : Set ℝ} :
    IsSpectralCutOn (fun t ↦ (U t).conjStarAlgEquiv (A t)) c s ↔ IsSpectralCutOn A c s := by
  simp only [isSpectralCutOn_iff, LinearIsometryEquiv.spectrum_conjStarAlgEquiv]
  refine and_congr_right fun _ ↦ forall₂_congr fun u _ ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [(U u).cfc_conjStarAlgEquiv, LinearIsometryEquiv.finiteDimensional_range_conjStarAlgEquiv_iff]

/-- A path conjugated by isometries has the same spectral flow potentials as the path itself. -/
@[simp]
theorem isSpectralFlowPotential_conjStarAlgEquiv_iff {a b : ℝ} {F : ℝ → ℤ} :
    IsSpectralFlowPotential (fun t ↦ (U t).conjStarAlgEquiv (A t)) a b F ↔
      IsSpectralFlowPotential A a b F := by
  simp only [isSpectralFlowPotential_iff, isSpectralCutOn_conjStarAlgEquiv_iff,
    spectralCount_conjStarAlgEquiv]

/-- **Isometric changes of trivialization preserve the spectral flow.** For any path `A` of
operators on `H` and any family `U` of linear isometric equivalences `H ≃ₗᵢ[𝕜] K`, the conjugated
path `t ↦ U t ∘ A t ∘ (U t)⁻¹` has the same spectral flow. -/
@[simp]
theorem spectralFlow_conjStarAlgEquiv (a b : ℝ) :
    spectralFlow (fun t ↦ (U t).conjStarAlgEquiv (A t)) a b = spectralFlow A a b :=
  spectralFlow_eq_of_isSpectralFlowPotential_iff fun _ ↦
    isSpectralFlowPotential_conjStarAlgEquiv_iff U

end TauCeti
