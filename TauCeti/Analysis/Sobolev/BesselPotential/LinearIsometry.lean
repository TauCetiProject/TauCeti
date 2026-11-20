/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LinearEquiv
public import TauCeti.Analysis.Sobolev.BesselPotential.Duality

/-!
# Linear isometries act isometrically on the Bessel-potential spaces

Let `A` be a linear isometry of a finite-dimensional real inner product space `E`. Composition with
`A` is an isometric linear automorphism of Mathlib's Bessel-potential space `H^{s,p}(E, F)`, for
every real order `s`, including negative orders, and every `1 ≤ p ≤ ∞`
(`BesselPotentialSpace.compLinearIsometryEquiv`). On a tempered distribution it is the pullback
`A^* u = u ∘ A` (`TemperedDistribution.compCLMOfContinuousLinearEquiv`), and on Schwartz functions
the composition `φ ↦ φ ∘ A`.

The reason is that the norm of `u ∈ H^{s,p}` is the `Lᵖ` norm of `J^s u`, where the Bessel
potential `J^s` is the Fourier multiplier with symbol `(1 + ‖ξ‖ ^ 2) ^ (s / 2)`. This symbol only
depends on `‖ξ‖`, so `J^s` commutes with `A^*`, and `A` preserves Lebesgue measure, so
`‖(J^s u) ∘ A‖_p = ‖J^s u‖_p`.

The main example is the reflection `R u (x) = u (-x)`, the case `A = -1`, which is an involutive
isometry of every `H^{s,p}` (`BesselPotentialSpace.compLinearIsometryEquiv_neg_involutive`). It
relates the bilinear pairing `∫ 𝓕 f · 𝓕 g` on the Fourier side to the spatial density pairing
`∫ f · R g` (`SchwartzMap.integral_bilin_fourier_fourier`), and transposes for the two pairings
by `S ↦ R ∘ S ∘ R`. Since `A` preserves Lebesgue measure, the density pairing of `H^{s,p}` with
`H^{-s,q}` is invariant under `A^*` acting on both factors
(`ContinuousLinearMap.besselPotentialPairing_compLinearIsometryEquiv`), so `R` is its own
transpose for it.

## Main declarations

* `BesselPotentialSpace.compLinearIsometryEquiv A`: composition with `A` as a linear isometric
  equivalence `H^{s,p}(E, F) ≃ₗᵢ[ℂ] H^{s,p}(E, F)`, with its distribution
  (`toDistr_compLinearIsometryEquiv`) and `Lᵖ` part (`toLp_compLinearIsometryEquiv`), its
  inverse `compLinearIsometryEquiv_symm`, functoriality `compLinearIsometryEquiv_trans` and
  `compLinearIsometryEquiv_refl`, and its value on Schwartz functions
  `compLinearIsometryEquiv_toBesselPotentialSpaceCLM`.
* `BesselPotentialSpace.compLinearIsometryEquiv_neg_involutive`: the reflection is an involution.
* `ContinuousLinearMap.besselPotentialPairing_compLinearIsometryEquiv`: invariance of the density
  pairing, and `ContinuousLinearMap.besselPotentialPairing_compLinearIsometryEquiv_neg_left`:
  the reflection is symmetric for it.

## References

* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Cambridge University
  Press, 2000, Chapter 3 (the Sobolev spaces `H^s(ℝⁿ)` and their duality).
-/

public noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pullback along a linear isometry `A` of an element of `H^{s,p}`, as an element of
`H^{s,p}`: its distribution is `A^* u` and its `Lᵖ` part is `(J^s u) ∘ A`. -/
private def compLinearIsometry (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) : H^{s, p}(E, F) where
  toDistr := compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv u.toDistr
  toLp := Lp.compMeasurePreserving A A.measurePreserving u.toLp
  bessel_toDistr_eq_toLp := by
    rw [besselPotential_compCLMOfContinuousLinearEquiv, u.bessel_toDistr_eq_toLp,
      compCLMOfContinuousLinearEquiv_toTemperedDistribution_eq_compMeasurePreserving]

variable (s p) in
/-- **Composition with a linear isometry is an isometry of `H^{s,p}`.** For a linear isometry `A`
of `E`, the pullback `u ↦ u ∘ A` of tempered distributions restricts to a linear isometric
equivalence of the Bessel-potential space `H^{s,p}(E, F)`, for every real `s` and every
`1 ≤ p ≤ ∞`. Its inverse is the pullback along `A⁻¹` (`compLinearIsometryEquiv_symm`). -/
def compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F) where
  toFun := compLinearIsometry A
  invFun := compLinearIsometry A.symm
  left_inv u := ext (by
    dsimp only [compLinearIsometry]
    rw [LinearIsometryEquiv.toContinuousLinearEquiv_symm,
      compCLMOfContinuousLinearEquiv_symm_apply_apply])
  right_inv u := ext (by
    dsimp only [compLinearIsometry]
    rw [LinearIsometryEquiv.toContinuousLinearEquiv_symm,
      compCLMOfContinuousLinearEquiv_apply_symm_apply])
  map_add' u v := ext (map_add (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv) _ _)
  map_smul' c u := ext (map_smul (compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv) _ _)
  norm_map' u := by
    rw [← norm_toLp_eq, ← norm_toLp_eq u]
    exact Lp.norm_compMeasurePreserving u.toLp A.measurePreserving

/-- The distribution of `u ∘ A` is the pullback `A^* u`. -/
@[simp]
theorem toDistr_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A u).toDistr =
      compCLMOfContinuousLinearEquiv F A.toContinuousLinearEquiv u.toDistr :=
  (rfl)

/-- The `Lᵖ` part of `u ∘ A` is the `Lᵖ` part of `u` composed with `A`, as an element of `Lᵖ`. -/
@[simp]
theorem toLp_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A u).toLp =
      Lp.compMeasurePreserving A A.measurePreserving u.toLp :=
  (rfl)

/-- Almost everywhere, the `Lᵖ` part of `u ∘ A` is the `Lᵖ` part of `u` composed with `A`. -/
theorem coeFn_toLp_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A u).toLp =ᵐ[volume] u.toLp ∘ A :=
  Lp.coeFn_compMeasurePreserving u.toLp A.measurePreserving

/-- The inverse of composition with `A` is composition with `A⁻¹`. -/
@[simp]
theorem compLinearIsometryEquiv_symm (A : E ≃ₗᵢ[ℝ] E) :
    (compLinearIsometryEquiv s p (F := F) A).symm = compLinearIsometryEquiv s p A.symm :=
  (rfl)

/-- Composition with `A.trans B = B ∘ A` is composition with `B` followed by composition with
`A`. -/
theorem compLinearIsometryEquiv_trans (A B : E ≃ₗᵢ[ℝ] E) :
    compLinearIsometryEquiv s p (F := F) (A.trans B) =
      (compLinearIsometryEquiv s p B).trans (compLinearIsometryEquiv s p A) :=
  LinearIsometryEquiv.ext fun u ↦ ext (by
    simp only [toDistr_compLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.toContinuousLinearEquiv_trans]
    exact compCLMOfContinuousLinearEquiv_trans _ _ _)

/-- Composition with the identity is the identity of `H^{s,p}`. -/
@[simp]
theorem compLinearIsometryEquiv_refl :
    compLinearIsometryEquiv s p (F := F) (LinearIsometryEquiv.refl ℝ E) =
      LinearIsometryEquiv.refl ℂ _ :=
  LinearIsometryEquiv.ext fun u ↦ ext (by
    simp only [toDistr_compLinearIsometryEquiv, LinearIsometryEquiv.toContinuousLinearEquiv_refl,
      compCLMOfContinuousLinearEquiv_refl, LinearIsometryEquiv.coe_refl, id_eq])

/-- On a Schwartz function `φ`, composition with `A` is the Schwartz function `φ ∘ A`. -/
@[simp]
theorem compLinearIsometryEquiv_toBesselPotentialSpaceCLM (A : E ≃ₗᵢ[ℝ] E) (φ : 𝓢(E, F)) :
    compLinearIsometryEquiv s p A (SchwartzMap.toBesselPotentialSpaceCLM s p φ) =
      SchwartzMap.toBesselPotentialSpaceCLM s p
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv φ) := by
  refine ext ?_
  rw [toDistr_compLinearIsometryEquiv, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
  exact compCLMOfContinuousLinearEquiv_toTemperedDistributionCLM volume _ φ

/-- **The reflection `u ↦ u (-·)` is an involution of `H^{s,p}`.** -/
theorem compLinearIsometryEquiv_neg_involutive :
    Function.Involutive
      (compLinearIsometryEquiv s p (F := F) (LinearIsometryEquiv.neg ℝ (E := E))) := by
  intro u
  conv_lhs => rw [← LinearIsometryEquiv.symm_neg, ← compLinearIsometryEquiv_symm]
  exact LinearIsometryEquiv.symm_apply_apply _ u

end BesselPotentialSpace

namespace ContinuousLinearMap

variable [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] [NormedAddCommGroup K]
  [NormedSpace ℂ K] [CompleteSpace K] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

open BesselPotentialSpace

/-- **The density pairing is invariant under linear isometries**: composing both factors with a
linear isometry `A` does not change `⟨u, w⟩ = ∫ B ((J^s u) x) ((J^{-s} w) x) dx`. -/
@[simp]
theorem besselPotentialPairing_compLinearIsometryEquiv (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ)
    (A : E ≃ₗᵢ[ℝ] E) (u : H^{s, p}(E, F)) (w : H^{-s, q}(E, G)) :
    B.besselPotentialPairing s p q (compLinearIsometryEquiv s p A u)
        (compLinearIsometryEquiv (-s) q A w) =
      B.besselPotentialPairing s p q u w := by
  rw [besselPotentialPairing_apply, besselPotentialPairing_apply]
  conv_rhs => rw [← A.measurePreserving.integral_comp A.toHomeomorph.measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toLp_compLinearIsometryEquiv A u,
    coeFn_toLp_compLinearIsometryEquiv A w] with x hu hw
  rw [hu, hw, Function.comp_apply, Function.comp_apply]

/-- The reflection `R u = u (-·)` is symmetric for the density pairing:
`⟨R u, w⟩ = ⟨u, R w⟩`. -/
theorem besselPotentialPairing_compLinearIsometryEquiv_neg_left (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ)
    (u : H^{s, p}(E, F)) (w : H^{-s, q}(E, G)) :
    B.besselPotentialPairing s p q (compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ) u) w =
      B.besselPotentialPairing s p q u
        (compLinearIsometryEquiv (-s) q (LinearIsometryEquiv.neg ℝ) w) := by
  conv_lhs => rw [← compLinearIsometryEquiv_neg_involutive w]
  exact besselPotentialPairing_compLinearIsometryEquiv B s _ u _

end ContinuousLinearMap
