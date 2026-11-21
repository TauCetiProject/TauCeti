/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Distribution.TemperedDistribution.LinearIsometry
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Linear isometries and the reflection on Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space. Every linear isometry equivalence `A`
of `E` acts on the Bessel-potential space `H^{s,p}(E, F)` by `u ↦ u ∘ A`, as a linear isometry
equivalence, for every real order `s` (including negative orders, where elements are genuine
distributions) and every `1 ≤ p ≤ ∞` (`BesselPotentialSpace.compLinearIsometryEquiv`). On the
underlying tempered distributions it is the pullback `A^*` (`TemperedDistribution.compCLM`), and
on the `Lᵖ` representatives `J^s u` it is composition with the measure-preserving map `A`, because
the Bessel potential `J^s` has a radial symbol and so commutes with `A^*`. The action is
contravariantly functorial (`BesselPotentialSpace.compLinearIsometryEquiv_trans`) and agrees with
composition on Schwartz functions
(`BesselPotentialSpace.compLinearIsometryEquiv_toBesselPotentialSpaceCLM`).

The case `A = -1` is the **reflection** `R u = u (-·)` (`BesselPotentialSpace.reflection`), an
involutive isometry of every `H^{s,p}` (`BesselPotentialSpace.reflection_reflection`). It relates
the spatial bilinear pairing `∫ f(x) g(x) dx` to the Fourier-side pairing `∫ 𝓕 f(ξ) 𝓕 g(ξ) dξ`,
which is the spatial pairing of `f` with `R g` (`SchwartzMap.integral_bilin_fourier_fourier`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.1.
-/

public noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

namespace BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pullback of an element of `H^{s,p}` along a linear isometry equivalence `A`, before it is
bundled as a linear isometry equivalence. -/
private def compAux (A : E ≃ₗᵢ[ℝ] E) (f : H^{s, p}(E, F)) : H^{s, p}(E, F) where
  toDistr := compCLM F A.toHomeomorph.toEquiv A.hasTemperateGrowth_toHomeomorph_toEquiv
    A.hasTemperateGrowth_toHomeomorph_toEquiv_symm f.toDistr
  toLp := Lp.compMeasurePreserving A A.measurePreserving f.toLp
  bessel_toDistr_eq_toLp :=
    besselPotential_compCLM_linearIsometryEquiv_eq_compMeasurePreserving A _ _
      f.bessel_toDistr_eq_toLp

private theorem compAux_symm_compAux (A : E ≃ₗᵢ[ℝ] E) (f : H^{s, p}(E, F)) :
    compAux A.symm (compAux A f) = f := by
  refine injective_toLp E F s p ?_
  simp only [compAux, ← Lp.compMeasurePreserving_comp_apply, LinearIsometryEquiv.self_comp_symm,
    Lp.compMeasurePreserving_id_apply]

variable (s p) in
/-- **Linear isometries act isometrically on `H^{s,p}`.** A linear isometry equivalence `A` of `E`
acts on the Bessel-potential space `H^{s,p}(E, F)` by `u ↦ u ∘ A`, for every real order `s` and
`1 ≤ p ≤ ∞`. On distributions it is the pullback `A^*` and on the `Lᵖ` representatives it is
composition with `A`. -/
def compLinearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F) where
  toFun := compAux A
  invFun := compAux A.symm
  map_add' f g := ext (map_add _ _ _)
  map_smul' c f := ext (map_smul _ _ _)
  left_inv := compAux_symm_compAux A
  right_inv f := by simpa using compAux_symm_compAux A.symm f
  norm_map' f := by
    rw [← norm_toLp_eq, ← norm_toLp_eq]
    exact Lp.norm_compMeasurePreserving _ _

variable (A : E ≃ₗᵢ[ℝ] E)

/-- On the underlying tempered distributions, `BesselPotentialSpace.compLinearIsometryEquiv A` is
the pullback `A^*`. -/
@[simp]
theorem toDistr_compLinearIsometryEquiv (f : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A f).toDistr =
      compCLM F A.toHomeomorph.toEquiv A.hasTemperateGrowth_toHomeomorph_toEquiv
        A.hasTemperateGrowth_toHomeomorph_toEquiv_symm f.toDistr :=
  (rfl)

/-- On the `Lᵖ` representatives `J^s u`, `BesselPotentialSpace.compLinearIsometryEquiv A` is
composition with the measure-preserving map `A`. -/
@[simp]
theorem toLp_compLinearIsometryEquiv (f : H^{s, p}(E, F)) :
    (compLinearIsometryEquiv s p A f).toLp =
      Lp.compMeasurePreserving A A.measurePreserving f.toLp :=
  (rfl)

@[simp]
theorem compLinearIsometryEquiv_symm :
    (compLinearIsometryEquiv s p A (F := F)).symm = compLinearIsometryEquiv s p A.symm :=
  (rfl)

/-- The identity of `E` acts as the identity. -/
@[simp]
theorem compLinearIsometryEquiv_refl :
    compLinearIsometryEquiv s p (LinearIsometryEquiv.refl ℝ E) (F := F) =
      LinearIsometryEquiv.refl ℂ _ := by
  ext1 f
  refine injective_toLp E F s p ?_
  simp

/-- **Functoriality.** Composing with `B ∘ A` is composing with `B` and then with `A`. -/
theorem compLinearIsometryEquiv_trans (B : E ≃ₗᵢ[ℝ] E) :
    compLinearIsometryEquiv s p (A.trans B) (F := F) =
      (compLinearIsometryEquiv s p B).trans (compLinearIsometryEquiv s p A) := by
  ext1 f
  refine injective_toLp E F s p ?_
  simp only [toLp_compLinearIsometryEquiv, LinearIsometryEquiv.trans_apply]
  exact Lp.compMeasurePreserving_comp_apply f.toLp B.measurePreserving A.measurePreserving

/-- On Schwartz functions, `BesselPotentialSpace.compLinearIsometryEquiv A` is composition
with `A`. -/
theorem compLinearIsometryEquiv_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    compLinearIsometryEquiv s p A (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
      SchwartzMap.toBesselPotentialSpaceCLM s p
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv u) := by
  ext1
  rw [toDistr_compLinearIsometryEquiv, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, compCLM_toTemperedDistributionCLM volume]
  refine congrArg _ ?_
  ext x
  simp [SchwartzMap.compCLM_apply]

variable (E F s p) in
/-- The **reflection** `R u = u (-·)` of the Bessel-potential space `H^{s,p}(E, F)`, a linear
isometry equivalence for every real order `s` and `1 ≤ p ≤ ∞`. -/
def reflection : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{s, p}(E, F) :=
  compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ)

/-- The reflection is the action of the linear isometry `x ↦ -x`. -/
theorem reflection_eq_compLinearIsometryEquiv :
    reflection E F s p = compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ) :=
  (rfl)

/-- On the underlying tempered distributions, the reflection is the pullback along `x ↦ -x`. -/
@[simp]
theorem toDistr_reflection (f : H^{s, p}(E, F)) :
    (reflection E F s p f).toDistr =
      compCLM F (LinearIsometryEquiv.neg ℝ (E := E)).toHomeomorph.toEquiv
        (LinearIsometryEquiv.neg ℝ).hasTemperateGrowth_toHomeomorph_toEquiv
        (LinearIsometryEquiv.neg ℝ).hasTemperateGrowth_toHomeomorph_toEquiv_symm f.toDistr := by
  rw [reflection_eq_compLinearIsometryEquiv, toDistr_compLinearIsometryEquiv]

/-- On the `Lᵖ` representatives `J^s u`, the reflection is composition with `x ↦ -x`. -/
@[simp]
theorem toLp_reflection (f : H^{s, p}(E, F)) :
    (reflection E F s p f).toLp =
      Lp.compMeasurePreserving (LinearIsometryEquiv.neg ℝ)
        (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).measurePreserving f.toLp := by
  rw [reflection_eq_compLinearIsometryEquiv, toLp_compLinearIsometryEquiv]

/-- The reflection is an involution. -/
@[simp]
theorem reflection_reflection (f : H^{s, p}(E, F)) :
    reflection E F s p (reflection E F s p f) = f :=
  (compLinearIsometryEquiv s p (LinearIsometryEquiv.neg ℝ)).symm_apply_apply f

@[simp]
theorem reflection_symm : (reflection E F s p).symm = reflection E F s p := by
  rw [reflection_eq_compLinearIsometryEquiv, compLinearIsometryEquiv_symm,
    LinearIsometryEquiv.symm_neg]

theorem reflection_involutive : Function.Involutive (reflection E F s p) :=
  reflection_reflection

/-- On Schwartz functions the reflection is `u ↦ u (-·)`. -/
theorem reflection_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    reflection E F s p (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
      SchwartzMap.toBesselPotentialSpaceCLM s p
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (.neg ℝ) u) :=
  compLinearIsometryEquiv_toBesselPotentialSpaceCLM _ u

end BesselPotentialSpace
