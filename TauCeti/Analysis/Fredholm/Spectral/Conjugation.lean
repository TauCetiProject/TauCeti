/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
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
not move.

**Paths on a common domain.** An unbounded path is given by bounded operators `A t : D → H` on a
common domain `D`, embedded in `H` by `ι`, and its spectral flow is
`TauCeti.domainSpectralFlow ι A`. A change of trivialization now consists of isometries
`U t : H ≃ₗᵢ[𝕜] K` together with isomorphisms `V t : D ≃L[𝕜] D'` of the domains which intertwine
the embeddings, `ι' ∘ V t = U t ∘ ι`; the conjugated path is `t ↦ U t ∘ A t ∘ (V t)⁻¹`, of
operators `D' → K`. Then `c ι' - U t A t (V t)⁻¹ = U t (c ι - A t) (V t)⁻¹`, so the same shifts are
admissible (`ContinuousLinearMap.isInvertible_smul_sub_comp_comp_symm_iff`), and the shifted
resolvent transforms of the conjugated path are the isometric conjugates `U t (τ_c (A t)) (U t)⁻¹`
of those of `A` (`ContinuousLinearMap.shiftedResolventTransform_comp_comp_symm`). By the bounded
case the two paths have the same spectral flow potentials
(`TauCeti.isDomainSpectralFlowPotential_comp_comp_symm_iff`), hence the same spectral flow
(`TauCeti.domainSpectralFlow_comp_comp_symm`). Again no continuity of `U` or `V` in `t` is needed.

## Main results

* `TauCeti.spectralCount_conjStarAlgEquiv`: isometric conjugation preserves the number of
  eigenvalues in `[0, c]`.
* `TauCeti.isSpectralCutOn_conjStarAlgEquiv_iff`: it preserves spectral cuts.
* `TauCeti.isSpectralFlowPotential_conjStarAlgEquiv_iff`: it preserves spectral flow potentials.
* `TauCeti.spectralFlow_conjStarAlgEquiv`: it preserves the spectral flow.
* `TauCeti.isDomainSpectralFlowPotential_comp_comp_symm_iff`,
  `TauCeti.domainSpectralFlow_comp_comp_symm`: changes of trivialization of a path on a common
  domain preserve its spectral flow potentials and its spectral flow.

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

/-! ### Paths on a compactly embedded common domain -/

section CommonDomain

variable {D D' : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup D']
  [NormedSpace 𝕜 D'] {ι : D →L[𝕜] H} {ι' : D' →L[𝕜] K} {A : ℝ → D →L[𝕜] H}
  (V : ℝ → D ≃L[𝕜] D')

/-- A path on a common domain, conjugated by isometries `U t` of the Hilbert spaces and
isomorphisms `V t` of the domains which intertwine the embeddings, `ι' ∘ V t = U t ∘ ι`, has the
same spectral flow potentials as the path itself. -/
theorem isDomainSpectralFlowPotential_comp_comp_symm_iff {a b : ℝ} {F : ℝ → ℤ}
    (hUV : ∀ t ∈ Icc a b, ι' ∘L (V t : D →L[𝕜] D') = (U t : H →L[𝕜] K) ∘L ι) :
    IsDomainSpectralFlowPotential ι'
        (fun t ↦ (U t : H →L[𝕜] K) ∘L A t ∘L ((V t).symm : D' →L[𝕜] D)) a b F ↔
      IsDomainSpectralFlowPotential ι A a b F := by
  simp only [isDomainSpectralFlowPotential_iff]
  refine forall₃_congr fun s t c ↦ forall₄_congr fun has _ htb _ ↦ ?_
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hinv : (∀ u ∈ Icc s t, ((c : 𝕜) • ι' -
      (U u : H →L[𝕜] K) ∘L A u ∘L ((V u).symm : D' →L[𝕜] D)).IsInvertible) ↔
      ∀ u ∈ Icc s t, ((c : 𝕜) • ι - A u).IsInvertible :=
    forall₂_congr fun u hu ↦ ContinuousLinearMap.isInvertible_smul_sub_comp_comp_symm_iff
      (U u).toContinuousLinearEquiv (V u) (hUV u (hsub hu)) _
  -- The shifted resolvent transforms are the conjugates of those of `A`.
  have hτ : spectralFlow (fun u ↦ ι'.shiftedResolventTransform
      ((U u : H →L[𝕜] K) ∘L A u ∘L ((V u).symm : D' →L[𝕜] D)) c) s t =
      spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) s t := by
    refine (spectralFlow_congr fun u hu ↦ ?_).trans (spectralFlow_conjStarAlgEquiv U s t)
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    -- The coercions of `U u` and of `(U u).toContinuousLinearEquiv` to `H →L[𝕜] K` agree.
    exact ContinuousLinearMap.shiftedResolventTransform_comp_comp_symm
      (U u).toContinuousLinearEquiv (V u) (hUV u (hsub hu)) (A u) c
  rw [hinv, hτ]

/-- **Changes of trivialization preserve the spectral flow on a common domain.** Let `U t` be
isometries of the Hilbert spaces `H ≃ₗᵢ[𝕜] K` and `V t` isomorphisms of the domains `D ≃L[𝕜] D'`
intertwining the embeddings, `ι' ∘ V t = U t ∘ ι`, for `t ∈ [a, b]`. Then the conjugated path
`t ↦ U t ∘ A t ∘ (V t)⁻¹` of operators `D' → K` has the same spectral flow through `ι'` as `A`
through `ι`. No continuity of `U` or `V` in `t` is needed. -/
theorem domainSpectralFlow_comp_comp_symm {a b : ℝ}
    (hUV : ∀ t ∈ Icc a b, ι' ∘L (V t : D →L[𝕜] D') = (U t : H →L[𝕜] K) ∘L ι) :
    domainSpectralFlow ι' (fun t ↦ (U t : H →L[𝕜] K) ∘L A t ∘L ((V t).symm : D' →L[𝕜] D)) a b =
      domainSpectralFlow ι A a b :=
  domainSpectralFlow_eq_of_isDomainSpectralFlowPotential_iff fun _ ↦
    isDomainSpectralFlowPotential_comp_comp_symm_iff U V hUV

end CommonDomain

end TauCeti
