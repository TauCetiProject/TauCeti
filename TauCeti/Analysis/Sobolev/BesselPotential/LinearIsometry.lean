/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LinearIsometry
public import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Linear isometries and reflection on the Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space and `A` a linear isometry of `E`. The
pullback of tempered distributions along `A` commutes with the Bessel potentials `J^s`, and on
`Lᵖ` functions it is composition with the measure-preserving map `A`. So it is a linear isometry
of every Bessel-potential space `H^{s,p}(E, F)`, for every real order `s` and every `1 ≤ p ≤ ∞`
(`BesselPotentialSpace.compLinearIsometryEquiv`). Pulling back is contravariantly functorial, so
the case `A = -1` is the **reflection** `R u = u (-·)`, an involutive isometry of every `H^{s,p}`
(`BesselPotentialSpace.compLinearIsometryEquiv_neg_compLinearIsometryEquiv_neg`).

The reflection compares the two bilinear pairings of the Bessel-potential spaces. The Fourier-side
pairing `B_F(φ, ψ) = ∫ B (𝓕 φ ξ) (𝓕 ψ ξ) dξ` of Schwartz functions is the spatial pairing with a
reflection, `B_F(φ, ψ) = B₀(φ, R ψ)` (`SchwartzMap.integral_bilin_fourier_fourier_eq`). So the
density pairing `H^{s,p} × H^{-s,q} → K` composed with `R` in the second factor is a continuous
bilinear map on the Bessel-potential spaces extending `B_F`
(`besselPotentialPairing_compLinearIsometryEquiv_neg_toBesselPotentialSpaceCLM`, in the
`ContinuousLinearMap` namespace).

## Main declarations

* `BesselPotentialSpace.compLinearIsometryEquiv A`: the pullback along `A` as a linear isometric
  equivalence of `H^{s,p}(E, F)`, with `toDistr_compLinearIsometryEquiv`,
  `toLp_compLinearIsometryEquiv`, `compLinearIsometryEquiv_symm`, `compLinearIsometryEquiv_trans`,
  `compLinearIsometryEquiv_refl` and `compLinearIsometryEquiv_toBesselPotentialSpaceCLM`.
* `BesselPotentialSpace.compLinearIsometryEquiv_neg_compLinearIsometryEquiv_neg`: the reflection is
  an involution.
* `besselPotentialPairing_compLinearIsometryEquiv_neg_toBesselPotentialSpaceCLM`, in the
  `ContinuousLinearMap` namespace: the density pairing composed with the reflection is the
  Fourier-side pairing on Schwartz functions.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, §6.2 (the spaces `H^{s,p}`).
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-! ### Bessel-potential spaces -/

namespace BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pullback along a linear isometry `A`, as a linear map of `H^{s,p}`. -/
private def compLinearIsometryEquivₗ (A : E ≃ₗᵢ[ℝ] E) : H^{s, p}(E, F) →ₗ[ℂ] H^{s, p}(E, F) where
  toFun u :=
    { toDistr := compCLM F A.toLinearEquiv.toEquiv A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm u.toDistr
      toLp := Lp.compMeasurePreserving A A.measurePreserving u.toLp
      bessel_toDistr_eq_toLp := by
        rw [besselPotential_compCLM_linearIsometryEquiv, u.bessel_toDistr_eq_toLp,
          compCLM_linearIsometryEquiv_toTemperedDistribution] }
  map_add' u v := by
    ext1
    simp [toDistr_add]
  map_smul' c u := by
    ext1
    simp [toDistr_smul]

/-- The pullback along a linear isometry `A` of `E`, `u ↦ u ∘ A`, as a linear isometric
equivalence of the Bessel-potential space `H^{s,p}(E, F)`, for every real order `s` and every
`1 ≤ p ≤ ∞`. Its inverse is the pullback along `A⁻¹` (`compLinearIsometryEquiv_symm`). -/
def compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F) where
  toLinearMap := compLinearIsometryEquivₗ A
  invFun := compLinearIsometryEquivₗ A.symm
  left_inv u := by
    ext1
    ext f
    simp [compLinearIsometryEquivₗ]
  right_inv u := by
    ext1
    ext f
    simp [compLinearIsometryEquivₗ]
  norm_map' u := by
    rw [← norm_toLp_eq, ← norm_toLp_eq u]
    exact Lp.norm_compMeasurePreserving _ _

@[simp]
theorem toDistr_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv A u).toDistr = compCLM F A.toLinearEquiv.toEquiv
      A.toLinearEquiv.hasTemperateGrowth_toEquiv A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm
      u.toDistr :=
  (rfl)

@[simp]
theorem toLp_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv A u).toLp = Lp.compMeasurePreserving A A.measurePreserving u.toLp :=
  (rfl)

/-- The pullback along `A⁻¹` inverts the pullback along `A`. -/
@[simp]
theorem compLinearIsometryEquiv_symm (A : E ≃ₗᵢ[ℝ] E) :
    (compLinearIsometryEquiv A : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F)).symm =
      compLinearIsometryEquiv A.symm :=
  (rfl)

/-- **Functoriality of the pullback**: pulling back along `B ∘ A` is pulling back along `B` and
then along `A`. -/
theorem compLinearIsometryEquiv_trans (A B : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) :
    compLinearIsometryEquiv (A.trans B) u =
      compLinearIsometryEquiv A (compLinearIsometryEquiv B u) := by
  ext1
  ext f
  simp only [toDistr_compLinearIsometryEquiv, compCLM_apply_apply,
    SchwartzMap.pushforwardCLM_linearIsometryEquiv]
  refine congrArg _ ?_
  ext x
  simp

/-- Pulling back along the identity is the identity. -/
@[simp]
theorem compLinearIsometryEquiv_refl :
    (compLinearIsometryEquiv (LinearIsometryEquiv.refl ℝ E) : H^{s, p}(E, F) ≃ₗᵢ[ℂ] _) =
      LinearIsometryEquiv.refl ℂ _ := by
  ext1 u
  ext1
  ext f
  simp only [toDistr_compLinearIsometryEquiv, compCLM_apply_apply,
    SchwartzMap.pushforwardCLM_linearIsometryEquiv]
  refine congrArg _ ?_
  ext x
  simp

/-- The **reflection** `R u = u(-·)` is an involution of `H^{s,p}`. -/
@[simp]
theorem compLinearIsometryEquiv_neg_compLinearIsometryEquiv_neg (u : H^{s, p}(E, F)) :
    compLinearIsometryEquiv (LinearIsometryEquiv.neg ℝ)
        (compLinearIsometryEquiv (LinearIsometryEquiv.neg ℝ) u) = u := by
  have h : (LinearIsometryEquiv.neg ℝ).trans (LinearIsometryEquiv.neg ℝ) =
      LinearIsometryEquiv.refl ℝ E := by
    ext x
    simp
  rw [← compLinearIsometryEquiv_trans, h]
  simp

/-- On Schwartz functions the pullback along `A` is composition with `A`. -/
@[simp]
theorem compLinearIsometryEquiv_toBesselPotentialSpaceCLM (A : E ≃ₗᵢ[ℝ] E) (φ : 𝓢(E, F)) :
    compLinearIsometryEquiv A (SchwartzMap.toBesselPotentialSpaceCLM s p φ) =
      SchwartzMap.toBesselPotentialSpaceCLM s p
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv φ) := by
  ext1
  rw [toDistr_compLinearIsometryEquiv, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, compCLM_toTemperedDistributionCLM]
  refine congrArg _ ?_
  ext x
  simp [SchwartzMap.compCLM_apply]

end BesselPotentialSpace

namespace ContinuousLinearMap

variable [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] [NormedAddCommGroup K]
  [NormedSpace ℂ K] [CompleteSpace K] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The Fourier-side pairing `∫ B (𝓕 φ ξ) (𝓕 ψ ξ) dξ` of Schwartz functions is the density pairing
of `H^{s,p} × H^{-s,q}` composed with the reflection `R` in the second factor, which is thus a
continuous bilinear map on the Bessel-potential spaces extending it. -/
theorem besselPotentialPairing_compLinearIsometryEquiv_neg_toBesselPotentialSpaceCLM
    (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ) (φ : 𝓢(E, F)) (ψ : 𝓢(E, G)) :
    B.besselPotentialPairing s p q (SchwartzMap.toBesselPotentialSpaceCLM s p φ)
        (BesselPotentialSpace.compLinearIsometryEquiv (LinearIsometryEquiv.neg ℝ)
          (SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ)) =
      ∫ ξ, B (𝓕 φ ξ) (𝓕 ψ ξ) := by
  rw [BesselPotentialSpace.compLinearIsometryEquiv_toBesselPotentialSpaceCLM,
    besselPotentialPairing_toBesselPotentialSpaceCLM, SchwartzMap.integral_bilin_fourier_fourier_eq]
  simp

end ContinuousLinearMap
