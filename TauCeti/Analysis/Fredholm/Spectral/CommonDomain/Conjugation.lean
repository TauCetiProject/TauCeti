/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.Fredholm.Spectral.Conjugation

/-!
# Changes of trivialization of a path on a common domain

An unbounded path is given by bounded operators `A t : D → H` on a common domain `D`, embedded in
`H` by `ι`, and its spectral flow is `TauCeti.domainSpectralFlow ι A`. A change of trivialization
consists of isometries `U t : H ≃ₗᵢ[𝕜] K` together with isomorphisms `V t : D ≃L[𝕜] D'` of the
domains which intertwine the embeddings, `ι' ∘ V t = U t ∘ ι`; the conjugated path is
`t ↦ U t ∘ A t ∘ (V t)⁻¹`, of operators `D' → K`.

Then `c ι' - U t A t (V t)⁻¹ = U t (c ι - A t) (V t)⁻¹`, so the same shifts are admissible
(`ContinuousLinearMap.isInvertible_smul_sub_comp_comp_symm_iff`), and the shifted resolvent
transforms of the conjugated path are the isometric conjugates `U t (τ_c (A t)) (U t)⁻¹` of those
of `A` (`ContinuousLinearMap.shiftedResolventTransform_comp_comp_symm`). By the bounded case
(`TauCeti.spectralFlow_conjStarAlgEquiv`) the two paths have the same spectral flow potentials,
hence the same spectral flow. These are pointwise statements, so no continuity of `U` or `V` in
`t`, and no hypothesis on `A`, is needed.

## Main results

* `TauCeti.isDomainSpectralFlowPotential_comp_comp_symm_iff`: changes of trivialization of a path
  on a common domain preserve its spectral flow potentials.
* `TauCeti.domainSpectralFlow_comp_comp_symm`: they preserve its spectral flow.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Set

namespace TauCeti

variable {𝕜 H K D D' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  [NormedAlgebra ℝ (K →L[𝕜] K)] [IsometricContinuousFunctionalCalculus ℝ (K →L[𝕜] K) IsSelfAdjoint]
  [IsScalarTower ℝ 𝕜 (K →L[𝕜] K)]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup D'] [NormedSpace 𝕜 D']
  {ι : D →L[𝕜] H} {ι' : D' →L[𝕜] K} {A : ℝ → D →L[𝕜] H}
  (U : ℝ → H ≃ₗᵢ[𝕜] K) (V : ℝ → D ≃L[𝕜] D')

/-- A path on a common domain, conjugated by isometries `U t` of the Hilbert spaces and
isomorphisms `V t` of the domains which intertwine the embeddings, `ι' ∘ V t = U t ∘ ι`, has the
same spectral flow potentials as the path itself. -/
theorem isDomainSpectralFlowPotential_comp_comp_symm_iff {a b : ℝ} {F : ℝ → ℤ}
    (hUV : ∀ t ∈ Icc a b, ι' ∘L (V t : D →L[𝕜] D') = (U t : H →L[𝕜] K) ∘L ι) :
    IsDomainSpectralFlowPotential ι'
        (fun t ↦ (U t : H →L[𝕜] K) ∘L A t ∘L ((V t).symm : D' →L[𝕜] D)) a b F ↔
      IsDomainSpectralFlowPotential ι A a b F := by
  -- The coercions of `U u` and of `(U u).toContinuousLinearEquiv` to continuous linear maps agree.
  have hU (u : ℝ) : ((U u).toContinuousLinearEquiv : H →L[𝕜] K) = (U u : H →L[𝕜] K) := rfl
  have hUsymm (u : ℝ) :
      ((U u).toContinuousLinearEquiv.symm : K →L[𝕜] H) = ((U u).symm : K →L[𝕜] H) := rfl
  simp only [isDomainSpectralFlowPotential_iff]
  refine forall₃_congr fun s t c ↦ forall₄_congr fun has _ htb _ ↦ ?_
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hinv : (∀ u ∈ Icc s t, ((c : 𝕜) • ι' -
      (U u : H →L[𝕜] K) ∘L A u ∘L ((V u).symm : D' →L[𝕜] D)).IsInvertible) ↔
      ∀ u ∈ Icc s t, ((c : 𝕜) • ι - A u).IsInvertible :=
    forall₂_congr fun u hu ↦ by
      rw [← hU u]
      exact ContinuousLinearMap.isInvertible_smul_sub_comp_comp_symm_iff
        (U u).toContinuousLinearEquiv (V u) (hUV u (hsub hu)) _
  -- The shifted resolvent transforms are the conjugates of those of `A`.
  have hτ : spectralFlow (fun u ↦ ι'.shiftedResolventTransform
      ((U u : H →L[𝕜] K) ∘L A u ∘L ((V u).symm : D' →L[𝕜] D)) c) s t =
      spectralFlow (fun u ↦ ι.shiftedResolventTransform (A u) c) s t := by
    refine (spectralFlow_congr fun u hu ↦ ?_).trans (spectralFlow_conjStarAlgEquiv U s t)
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, ← hU u, ← hUsymm u]
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

end TauCeti
