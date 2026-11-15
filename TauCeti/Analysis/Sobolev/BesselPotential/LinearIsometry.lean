/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Linear isometries act isometrically on Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space and `A : E ≃ₗᵢ[ℝ] E` a linear isometry,
for instance the reflection `x ↦ -x`. Pulling tempered distributions back along `A`,
`(A^* T) f = T (f ∘ A⁻¹)` (`TemperedDistribution.compCLM` for the bijection `A`), commutes with
the Fourier transform (`TemperedDistribution.fourier_compCLM_linearIsometryEquiv`). The Bessel
potential `J^s = 𝓕⁻ (⟨ξ⟩ ^ s 𝓕 ·)` has a symbol which only depends on `‖ξ‖`, so it commutes with
`A^*` too, and `A^*` acts on `Lᵖ` as composition with the measure-preserving map `A`. Hence `A^*`
preserves every Bessel-potential space `H^{s,p}(E, F)`, for every real order `s` and every
`1 ≤ p ≤ ∞`, and is an isometry there: a rotation or reflection of the variables changes no
Sobolev norm, including the norms of negative order.

For the reflection `R = (-1)^*`, which is its own inverse, this says that `R` is an involutive
isometry of every `H^{s,p}`, including the spaces of negative order, whose elements are not
functions. On Schwartz functions `R g = g (-·)` is the reflection in the bilinear Plancherel
identity `∫ M (𝓕 f) (𝓕 g) = ∫ M f (R g)` (`SchwartzMap.integral_bilin_fourier_fourier`).

## Main declarations

* `TemperedDistribution.besselPotential_compCLM_linearIsometryEquiv`: `J^s (A^* T) = A^* (J^s T)`.
* `TemperedDistribution.memSobolev_compCLM_linearIsometryEquiv_iff`: `A^* T ∈ H^{s,p}` exactly when
  `T ∈ H^{s,p}`.
* `BesselPotentialSpace.compLinearIsometryEquiv A`: `A^*` as a linear isometry equivalence of
  `H^{s,p}(E, F)`, with inverse `BesselPotentialSpace.compLinearIsometryEquiv A.symm`
  (`BesselPotentialSpace.symm_compLinearIsometryEquiv`). For the reflection it is an involution
  (`BesselPotentialSpace.compLinearIsometryEquiv_neg_apply_compLinearIsometryEquiv_neg`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1 (the Fourier
  transform commutes with orthogonal changes of variables).
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, Chapter 3 (the Sobolev
  spaces `H^s(ℝⁿ)` and their Bessel-potential norms).
-/

public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap BesselPotentialSpace ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace TemperedDistribution

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [MeasurableSpace E] [BorelSpace E]

/-- **The Bessel potential commutes with the pullback along a linear isometry**, since its symbol
`(1 + ‖ξ‖²) ^ (s / 2)` only depends on `‖ξ‖`. -/
theorem besselPotential_compCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E)
    (hφ : ((A.toEquiv : E ≃ E) : E → E).HasTemperateGrowth)
    (hψ : ((A.toEquiv.symm : E ≃ E) : E → E).HasTemperateGrowth) (s : ℝ) (T : 𝓢'(E, F)) :
    besselPotential E F s (compCLM F A.toEquiv hφ hψ T) =
      compCLM F A.toEquiv hφ hψ (besselPotential E F s T) :=
  fourierMultiplierCLM_compCLM_linearIsometryEquiv A hφ hψ (by fun_prop) (by simp) T

variable [CompleteSpace F]

/-- The pullback along a linear isometry preserves the Bessel-potential spaces `H^{s,p}`. -/
theorem MemSobolev.compCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E)
    (hφ : ((A.toEquiv : E ≃ E) : E → E).HasTemperateGrowth)
    (hψ : ((A.toEquiv.symm : E ≃ E) : E → E).HasTemperateGrowth) {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {T : 𝓢'(E, F)} (hT : T.MemSobolev s p) :
    (compCLM F A.toEquiv hφ hψ T).MemSobolev s p := by
  obtain ⟨u, hu⟩ := hT
  exact ⟨Lp.compMeasurePreserving A A.measurePreserving u, by
    rw [besselPotential_compCLM_linearIsometryEquiv, hu,
      compCLM_linearIsometryEquiv_toTemperedDistribution]⟩

/-- **A rotation or reflection of the variables preserves every Bessel-potential space**:
`A^* T ∈ H^{s,p}` exactly when `T ∈ H^{s,p}`. -/
theorem memSobolev_compCLM_linearIsometryEquiv_iff (A : E ≃ₗᵢ[ℝ] E)
    (hφ : ((A.toEquiv : E ≃ E) : E → E).HasTemperateGrowth)
    (hψ : ((A.toEquiv.symm : E ≃ E) : E → E).HasTemperateGrowth) {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {T : 𝓢'(E, F)} :
    (compCLM F A.toEquiv hφ hψ T).MemSobolev s p ↔ T.MemSobolev s p := by
  refine ⟨fun h ↦ ?_, MemSobolev.compCLM_linearIsometryEquiv A hφ hψ⟩
  rw [← compCLM_symm_compCLM hφ hψ A.hasTemperateGrowth_toEquiv T]
  -- The pullback along `A⁻¹`, written with `A.toEquiv.symm`, is the one along `A.symm`.
  exact h.compCLM_linearIsometryEquiv A.symm hψ A.hasTemperateGrowth_toEquiv

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [MeasurableSpace E]
  [BorelSpace E] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pullback along a linear isometry `A` of `E` as a map `H^{s,p}(E, F) → H^{s,p}(E, F)`; its
`Lᵖ` part is the composition of the `Lᵖ` part with `A`. -/
private def compLinearIsometry (A : E ≃ₗᵢ[ℝ] E) (f : H^{s, p}(E, F)) : H^{s, p}(E, F) where
  toDistr :=
    compCLM F A.toEquiv A.hasTemperateGrowth_toEquiv A.hasTemperateGrowth_toEquiv_symm f.toDistr
  toLp := Lp.compMeasurePreserving A A.measurePreserving f.toLp
  bessel_toDistr_eq_toLp := by
    rw [besselPotential_compCLM_linearIsometryEquiv, f.bessel_toDistr_eq_toLp,
      compCLM_linearIsometryEquiv_toTemperedDistribution]

variable (s p) in
/-- **The pullback along a linear isometry `A` of `E`**, `T ↦ T ∘ A`, as a linear isometry
equivalence of the Bessel-potential space `H^{s,p}(E, F)`, for every real order `s`. Its inverse is
the pullback along `A⁻¹` (`BesselPotentialSpace.symm_compLinearIsometryEquiv`). -/
def compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F) where
  toFun := compLinearIsometry A
  invFun := compLinearIsometry A.symm
  map_add' f g := ext (map_add _ _ _)
  map_smul' c f := ext (map_smul _ _ _)
  left_inv f := ext <| compCLM_symm_compCLM (φ := A.toEquiv) A.hasTemperateGrowth_toEquiv
    A.hasTemperateGrowth_toEquiv_symm A.hasTemperateGrowth_toEquiv f.toDistr
  right_inv f := ext <| compCLM_compCLM_symm (φ := A.toEquiv) A.hasTemperateGrowth_toEquiv
    A.hasTemperateGrowth_toEquiv_symm A.hasTemperateGrowth_toEquiv f.toDistr
  norm_map' f := by
    rw [← norm_toLp_eq, ← norm_toLp_eq]
    exact Lp.norm_compMeasurePreserving _ _

/-- The distribution underlying `A^* f` is the pullback of the distribution of `f`. -/
@[simp]
theorem toDistr_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (f : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A f).toDistr =
      compCLM F A.toEquiv A.hasTemperateGrowth_toEquiv A.hasTemperateGrowth_toEquiv_symm
        f.toDistr :=
  (rfl)

/-- The `Lᵖ` part of `A^* f` is the `Lᵖ` part of `f` composed with `A`. -/
@[simp]
theorem toLp_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (f : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A f).toLp =
      Lp.compMeasurePreserving A A.measurePreserving f.toLp :=
  (rfl)

/-- The inverse of the pullback along `A` is the pullback along `A⁻¹`. -/
@[simp]
theorem symm_compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) :
    (compLinearIsometryEquiv s p A : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F)).symm =
      compLinearIsometryEquiv s p A.symm :=
  (rfl)

/-- **The pullback is contravariantly functorial**: pulling back along `A` and then along `B` is
pulling back along `A` followed by `B`, that is along `x ↦ B (A x)`. -/
theorem compLinearIsometryEquiv_apply_compLinearIsometryEquiv (A B : E ≃ₗᵢ[ℝ] E)
    (f : H^{s, p}(E, F)) :
    compLinearIsometryEquiv s p A (compLinearIsometryEquiv s p B f) =
      compLinearIsometryEquiv s p (A.trans B) f := by
  ext1
  exact congrArg (fun L : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) ↦ L f.toDistr)
    (compCLM_trans (φ := A.toEquiv) (χ := B.toEquiv) A.hasTemperateGrowth_toEquiv
      A.hasTemperateGrowth_toEquiv_symm B.hasTemperateGrowth_toEquiv
      B.hasTemperateGrowth_toEquiv_symm (A.trans B).hasTemperateGrowth_toEquiv
      (A.trans B).hasTemperateGrowth_toEquiv_symm).symm

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compLinearIsometryEquiv_refl :
    compLinearIsometryEquiv s p (LinearIsometryEquiv.refl ℝ E) =
      LinearIsometryEquiv.refl ℂ (H^{s, p}(E, F)) := by
  ext f : 2
  simp only [toDistr_compLinearIsometryEquiv, LinearIsometryEquiv.coe_refl, id_eq]
  exact congrArg (fun L : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) ↦ L f.toDistr) (compCLM_refl _ _)

/-- **The reflection `x ↦ -x` is an involution of every Bessel-potential space.** -/
@[simp]
theorem compLinearIsometryEquiv_neg_apply_compLinearIsometryEquiv_neg (f : H^{s, p}(E, F)) :
    compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ)
        (compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ) f) = f :=
  (compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ (E := E))).symm_apply_apply f

end BesselPotentialSpace
