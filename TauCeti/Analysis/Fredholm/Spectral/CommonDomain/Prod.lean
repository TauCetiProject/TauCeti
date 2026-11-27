/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain
public import TauCeti.Analysis.Fredholm.Spectral.Prod
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum

/-!
# The spectral flow on a common domain of a direct sum

Let `ι₁ : D₁ →L H₁` and `ι₂ : D₂ →L H₂` be compact operators from Banach spaces into Hilbert
spaces, and let `A₁ : ℝ → (D₁ →L H₁)` and `A₂ : ℝ → (D₂ →L H₂)` be continuous paths of operators
symmetric through `ι₁` and `ι₂`, each with some invertible shift, as in
`TauCeti.Analysis.Fredholm.Spectral.CommonDomain`. Their direct sum is the path
`t ↦ A₁ t ⊕ A₂ t` of operators from the common domain `WithLp 2 (D₁ × D₂)` into the Hilbert direct
sum `WithLp 2 (H₁ × H₂)`, embedded by the compact operator `ι₁ ⊕ ι₂`
(`ContinuousLinearMap.withLpProdMap`). This file proves that the spectral flow
`TauCeti.domainSpectralFlow` is additive under this direct sum.

A shift `c (ι₁ ⊕ ι₂) - (A₁ t ⊕ A₂ t)` is the block sum of the shifts `c ιᵢ - Aᵢ t`, so it is
invertible exactly when both are, and then its shifted resolvent transform is the block sum of
theirs (`ContinuousLinearMap.shiftedResolventTransform_withLpProdMap`). Hence, over an interval
with a shift admissible for the direct sum, the shift is admissible for both summands and the
spectral flow of the transforms of the direct sum is the sum of theirs, by additivity of the
bounded spectral flow (`TauCeti.spectralFlow_withLpProdMap`). So the sum of spectral flow
potentials of `A₁` and `A₂` is a potential of `A₁ ⊕ A₂`. The direct sum also has some invertible
shift at every time: the shifts that fail to be invertible for either summand form a discrete set
(`ContinuousLinearMap.eventually_isInvertible_smul_sub`).

## Main results

* `ContinuousLinearMap.shiftedResolventTransform_withLpProdMap`: the shifted resolvent transform
  of a block sum is the block sum of the shifted resolvent transforms.
* `TauCeti.domainSpectralFlow_withLpProdMap`: the spectral flow on a common domain is additive
  under direct sums.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4.
-/

public section

open Filter Set Topology

variable {𝕜 D₁ D₂ H₁ H₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D₁] [NormedSpace 𝕜 D₁] [NormedAddCommGroup D₂] [NormedSpace 𝕜 D₂]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [NormedAddCommGroup H₂]
  [InnerProductSpace 𝕜 H₂]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace ContinuousLinearMap

/-- The shifted resolvent transform at a shift `c` of a block sum `A₁ ⊕ A₂`, on the common domain
embedded by `ι₁ ⊕ ι₂`, is the block sum of the shifted resolvent transforms at `c`, when both
shifts `c ιᵢ - Aᵢ` are invertible. -/
theorem shiftedResolventTransform_withLpProdMap {ι₁ A₁ : D₁ →L[𝕜] H₁} {ι₂ A₂ : D₂ →L[𝕜] H₂}
    {c : ℝ} (h₁ : ((c : 𝕜) • ι₁ - A₁).IsInvertible) (h₂ : ((c : 𝕜) • ι₂ - A₂).IsInvertible) :
    (ι₁.withLpProdMap 2 ι₂).shiftedResolventTransform (A₁.withLpProdMap 2 A₂) c =
      (ι₁.shiftedResolventTransform A₁ c).withLpProdMap 2 (ι₂.shiftedResolventTransform A₂ c) := by
  rw [shiftedResolventTransform_def, shiftedResolventTransform_def, shiftedResolventTransform_def,
    ← withLpProdMap_smul, ← withLpProdMap_sub, inverse_withLpProdMap h₁ h₂,
    ← withLpProdMap_comp, withLpProdMap_smul]

end ContinuousLinearMap

namespace TauCeti

open ContinuousLinearMap

variable [CompleteSpace H₁] [CompleteSpace H₂]
  [NormedAlgebra ℝ (H₁ →L[𝕜] H₁)] [IsScalarTower ℝ 𝕜 (H₁ →L[𝕜] H₁)]
  [IsometricContinuousFunctionalCalculus ℝ (H₁ →L[𝕜] H₁) IsSelfAdjoint]
  [NormedAlgebra ℝ (H₂ →L[𝕜] H₂)] [IsScalarTower ℝ 𝕜 (H₂ →L[𝕜] H₂)]
  [IsometricContinuousFunctionalCalculus ℝ (H₂ →L[𝕜] H₂) IsSelfAdjoint]
  [NormedAlgebra ℝ (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))]
  [IsScalarTower ℝ 𝕜 (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))]
  [IsometricContinuousFunctionalCalculus ℝ (WithLp 2 (H₁ × H₂) →L[𝕜] WithLp 2 (H₁ × H₂))
    IsSelfAdjoint]
  [CompleteSpace D₁] [CompleteSpace D₂]
  {ι₁ : D₁ →L[𝕜] H₁} {ι₂ : D₂ →L[𝕜] H₂} {A₁ : ℝ → D₁ →L[𝕜] H₁} {A₂ : ℝ → D₂ →L[𝕜] H₂}

/-- **The spectral flow on a common domain is additive under direct sums.** For continuous paths
`A₁` and `A₂` of operators symmetric through compact operators `ι₁` and `ι₂`, each with some
invertible shift, the spectral flow of the block-diagonal path `t ↦ A₁ t ⊕ A₂ t` on the common
domain embedded by `ι₁ ⊕ ι₂` is the spectral flow of `A₁` plus that of `A₂`. -/
theorem domainSpectralFlow_withLpProdMap {a b : ℝ} (hab : a ≤ b) (hι₁ : IsCompactOperator ι₁)
    (hι₂ : IsCompactOperator ι₂) (hA₁ : ContinuousOn A₁ (Icc a b))
    (hA₂ : ContinuousOn A₂ (Icc a b))
    (hsymm₁ : ∀ t ∈ Icc a b, ∀ x y, ⟪A₁ t x, ι₁ y⟫ = ⟪ι₁ x, A₁ t y⟫)
    (hsymm₂ : ∀ t ∈ Icc a b, ∀ x y, ⟪A₂ t x, ι₂ y⟫ = ⟪ι₂ x, A₂ t y⟫)
    (h₀₁ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι₁ - A₁ t).IsInvertible)
    (h₀₂ : ∀ t ∈ Icc a b, ∃ c₀ : 𝕜, (c₀ • ι₂ - A₂ t).IsInvertible) :
    domainSpectralFlow (ι₁.withLpProdMap 2 ι₂) (fun t ↦ (A₁ t).withLpProdMap 2 (A₂ t)) a b =
      domainSpectralFlow ι₁ A₁ a b + domainSpectralFlow ι₂ A₂ a b := by
  -- The shifts of the direct sum are the block sums of the shifts of the summands.
  have hshift (c : 𝕜) (t : ℝ) :
      c • ι₁.withLpProdMap 2 ι₂ - (A₁ t).withLpProdMap 2 (A₂ t) =
        (c • ι₁ - A₁ t).withLpProdMap 2 (c • ι₂ - A₂ t) := by
    rw [withLpProdMap_sub, withLpProdMap_smul]
  -- Some shift is invertible for both summands, since each fails only on a discrete set.
  have h₀ (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ c₀ : 𝕜, (c₀ • ι₁.withLpProdMap 2 ι₂ - (A₁ t).withLpProdMap 2 (A₂ t)).IsInvertible := by
    obtain ⟨c₁, hc₁⟩ := h₀₁ t ht
    obtain ⟨c₂, hc₂⟩ := h₀₂ t ht
    obtain ⟨c, hc⟩ := ((eventually_isInvertible_smul_sub hι₁ hc₁ 0).and
      (eventually_isInvertible_smul_sub hι₂ hc₂ 0)).exists
    exact ⟨c, by rw [hshift, isInvertible_withLpProdMap_iff]; exact hc⟩
  obtain ⟨F₁, hF₁⟩ := exists_isDomainSpectralFlowPotential hι₁ hA₁ hsymm₁ h₀₁
  obtain ⟨F₂, hF₂⟩ := exists_isDomainSpectralFlowPotential hι₂ hA₂ hsymm₂ h₀₂
  -- The sum of potentials of `A₁` and `A₂` is a potential of their direct sum.
  have hF : IsDomainSpectralFlowPotential (ι₁.withLpProdMap 2 ι₂)
      (fun t ↦ (A₁ t).withLpProdMap 2 (A₂ t)) a b (F₁ + F₂) := by
    refine isDomainSpectralFlowPotential_iff.2 fun s t c has hst htb hc hinv ↦ ?_
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hinv₁ (u : ℝ) (hu : u ∈ Icc s t) : ((c : 𝕜) • ι₁ - A₁ u).IsInvertible :=
      (isInvertible_withLpProdMap_iff.1 (hshift _ u ▸ hinv u hu)).1
    have hinv₂ (u : ℝ) (hu : u ∈ Icc s t) : ((c : 𝕜) • ι₂ - A₂ u).IsInvertible :=
      (isInvertible_withLpProdMap_iff.1 (hshift _ u ▸ hinv u hu)).2
    rw [spectralFlow_congr fun u hu ↦ shiftedResolventTransform_withLpProdMap (hinv₁ u hu)
        (hinv₂ u hu),
      spectralFlow_withLpProdMap hst ((hA₁.mono hsub).shiftedResolventTransform hinv₁)
        ((hA₂.mono hsub).shiftedResolventTransform hinv₂)
        (fun u hu ↦ ι₁.isSelfAdjoint_shiftedResolventTransform (hsymm₁ u (hsub hu)))
        (fun u hu ↦ ι₂.isSelfAdjoint_shiftedResolventTransform (hsymm₂ u (hsub hu)))
        (fun u hu ↦ ι₁.isFredholm_shiftedResolventTransform hι₁ hc (hinv₁ u hu))
        (fun u hu ↦ ι₂.isFredholm_shiftedResolventTransform hι₂ hc (hinv₂ u hu)),
      ← isDomainSpectralFlowPotential_iff.1 hF₁ has hst htb hc hinv₁,
      ← isDomainSpectralFlowPotential_iff.1 hF₂ has hst htb hc hinv₂, Pi.add_apply, Pi.add_apply]
    ring
  rw [domainSpectralFlow_eq_sub (hι₁.withLpProdMap hι₂) hab (hA₁.withLpProdMap hA₂) h₀ hF,
    domainSpectralFlow_eq_sub hι₁ hab hA₁ h₀₁ hF₁, domainSpectralFlow_eq_sub hι₂ hab hA₂ h₀₂ hF₂,
    Pi.add_apply, Pi.add_apply]
  ring

end TauCeti
