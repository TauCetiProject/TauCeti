/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.OperatorIdentities
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.DiagonalMeasure
public import TauCeti.MeasureTheory.VectorMeasure.Uniqueness
public import TauCeti.MeasureTheory.VectorMeasure.WithDensity

/-!
# Polarized complex measures of a continuous-function representation

Let `π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` be a unital star representation on a complex Hilbert space,
with `K` compact Hausdorff. Each vector `ξ` has a finite regular diagonal measure `μ_ξ`, with
`∫ f dμ_ξ = ⟪ξ, π f ξ⟫` for continuous `f` (`StarAlgHom.representationDiagMeasure`). Complex
polarization of these diagonal measures gives, for every pair of vectors, a complex measure

`μ_(ψ,ξ) = ¼ (μ_(ξ+ψ) + i μ_(ξ+iψ) - μ_(ξ-ψ) - i μ_(ξ-iψ))`

with `∫ f dμ_(ψ,ξ) = ⟪ψ, π f ξ⟫` for every continuous `f`, the integral being taken through the
multiplication pairing `ℂ × ℂ → ℂ`. Its variation is dominated by the average of the four
diagonal measures, so it is finite and regular. By the uniqueness theorem for scalar measures of
regular variation on a compact Hausdorff space
(`MeasureTheory.VectorMeasure.ext_of_integral_eq_on_continuousMap`), `μ_(ψ,ξ)` is the only such
measure. Uniqueness gives its algebraic laws: it is conjugate-linear in `ψ`, linear in `ξ`,
conjugate-symmetric, and on the diagonal it is `μ_ξ` regarded as a complex measure.

Integrating a bounded Borel symbol `f` against these measures defines the matrix elements
`⟪ψ, T_f ξ⟫ = ∫ f dμ_(ψ,ξ)` of an operator `T_f` that extends `π` from continuous to bounded Borel
symbols (`StarAlgHom.representationBorelOperator`). The total variation bound
`|μ_(ψ,ξ)|(K) ≤ 2 ‖ψ‖ ‖ξ‖` makes this sesquilinear form bounded.

## Main declarations

* `StarAlgHom.representationPolarizedMeasure π ψ ξ`: the polarized complex measure `μ_(ψ,ξ)`.
* `StarAlgHom.integral_representationPolarizedMeasure`: `∫ f dμ_(ψ,ξ) = ⟪ψ, π f ξ⟫` for continuous
  `f`.
* `StarAlgHom.eq_representationPolarizedMeasure_iff`: characterization among complex measures of
  regular variation.
* `StarAlgHom.variation_representationPolarizedMeasure_le`: domination of the variation by the
  diagonal measures, with the instance of regular variation.
* `StarAlgHom.variation_representationPolarizedMeasure_univ_le`: the total variation is at most
  `2 ‖ψ‖ ‖ξ‖`.
* `StarAlgHom.representationPolarizedMeasure_self`: the diagonal case.
* `StarAlgHom.representationPolarizedMeasure_add_left` and its companions: sesquilinearity.
* `StarAlgHom.representationPolarizedMeasure_swap_apply`: conjugate symmetry.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill (1987), Theorem 6.19.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.1.
-/

public section

noncomputable section

open MeasureTheory MeasureTheory.VectorMeasure ContinuousMap
open scoped InnerProductSpace ENNReal NNReal

namespace StarAlgHom

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [BorelSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The diagonal measure at `v`, regarded as a complex measure with constant density `1`. -/
private abbrev diagComplex (v : H) : ComplexMeasure K :=
  (representationDiagMeasure π v).withDensityᵥ fun _ => (1 : ℂ)

/-- The **polarized complex measure** `μ_(ψ,ξ)` of a representation of `C(K, ℂ)`, the complex
polarization `¼ (μ_(ξ+ψ) + i μ_(ξ+iψ) - μ_(ξ-ψ) - i μ_(ξ-iψ))` of the diagonal measures. It is
the unique complex measure of regular variation with `∫ f dμ_(ψ,ξ) = ⟪ψ, π f ξ⟫` for every
continuous `f` (`eq_representationPolarizedMeasure_iff`). It is conjugate-linear in `ψ` and linear
in `ξ`. -/
def representationPolarizedMeasure (ψ ξ : H) : ComplexMeasure K :=
  (1 / 4 : ℂ) • (diagComplex π (ξ + ψ) + Complex.I • diagComplex π (ξ + Complex.I • ψ) -
    diagComplex π (ξ - ψ) - Complex.I • diagComplex π (ξ - Complex.I • ψ))

/-- The value of the polarized measure on a measurable set, by the polarization formula. -/
theorem representationPolarizedMeasure_apply (ψ ξ : H) {B : Set K} (hB : MeasurableSet B) :
    representationPolarizedMeasure π ψ ξ B =
      (1 / 4 : ℂ) * ((representationDiagMeasure π (ξ + ψ)).real B +
        Complex.I * (representationDiagMeasure π (ξ + Complex.I • ψ)).real B -
        (representationDiagMeasure π (ξ - ψ)).real B -
        Complex.I * (representationDiagMeasure π (ξ - Complex.I • ψ)).real B) := by
  simp [representationPolarizedMeasure, withDensityᵥ_one_apply hB]

/-- The variation of the polarized measure is dominated by the average of the four diagonal
measures in the polarization formula. -/
theorem variation_representationPolarizedMeasure_le (ψ ξ : H) :
    (representationPolarizedMeasure π ψ ξ).variation ≤
      (4⁻¹ : ℝ≥0) • (representationDiagMeasure π (ξ + ψ) +
        representationDiagMeasure π (ξ + Complex.I • ψ) + representationDiagMeasure π (ξ - ψ) +
        representationDiagMeasure π (ξ - Complex.I • ψ)) := by
  have h4 : ‖(1 / 4 : ℂ)‖₊ = 4⁻¹ := by
    ext
    simp
  rw [representationPolarizedMeasure, variation_smul, h4]
  gcongr
  grw [variation_sub_le, variation_sub_le, variation_add_le]
  simp [variation_smul]

/-- The polarized measure has regular variation. -/
instance regular_variation_representationPolarizedMeasure (ψ ξ : H) :
    (representationPolarizedMeasure π ψ ξ).variation.Regular :=
  (Measure.absolutelyContinuous_of_le_smul
    (variation_representationPolarizedMeasure_le π ψ ξ)).regular

/-- Integration of a continuous function against the diagonal measure regarded as a complex
measure gives the diagonal matrix coefficient. -/
private theorem integral_diagComplex (v : H) (f : C(K, ℂ)) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; diagComplex π v] = ⟪v, π f v⟫_ℂ := by
  rw [integral_mul_withDensityᵥ_one, integral_representationDiagMeasure]

/-- Integrating a continuous function against the polarized measure gives the matrix coefficient
`⟪ψ, π f ξ⟫`. -/
theorem integral_representationPolarizedMeasure (ψ ξ : H) (f : C(K, ℂ)) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; representationPolarizedMeasure π ψ ξ] =
      ⟪ψ, π f ξ⟫_ℂ := by
  have hf (μ : ComplexMeasure K) : μ.Integrable f := f.integrable _
  rw [representationPolarizedMeasure, integral_smul_vectorMeasure_mul,
    integral_sub_vectorMeasure (hf _) (hf _), integral_sub_vectorMeasure (hf _) (hf _),
    integral_add_vectorMeasure (hf _) (hf _)]
  simp only [integral_smul_vectorMeasure_mul, integral_diagComplex]
  exact (π f).inner_polarization ψ ξ

/-- A complex measure of regular variation equals the polarized measure `μ_(ψ,ξ)` iff its
integral of every continuous `f` is `⟪ψ, π f ξ⟫`. -/
theorem eq_representationPolarizedMeasure_iff (ψ ξ : H) (μ : ComplexMeasure K)
    [μ.variation.Regular] :
    μ = representationPolarizedMeasure π ψ ξ ↔
      ∀ f : C(K, ℂ), ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = ⟪ψ, π f ξ⟫_ℂ :=
  ⟨fun h => h ▸ integral_representationPolarizedMeasure π ψ ξ, fun h =>
    ext_of_integral_eq_on_continuousMap fun f => by
      rw [h, integral_representationPolarizedMeasure]⟩

/-- On the diagonal, the polarized measure is the diagonal measure `μ_ξ` regarded as a complex
measure, that is, with constant complex density `1`. -/
theorem representationPolarizedMeasure_self (ξ : H) :
    representationPolarizedMeasure π ξ ξ =
      (representationDiagMeasure π ξ).withDensityᵥ fun _ => (1 : ℂ) := by
  have : ((representationDiagMeasure π ξ).withDensityᵥ fun _ => (1 : ℂ)).variation.Regular := by
    rw [Measure.variation_withDensityᵥ_one]
    infer_instance
  exact ((eq_representationPolarizedMeasure_iff π ξ ξ _).2 (integral_diagComplex π ξ)).symm

/-- On the diagonal, the polarized measure takes the real values of the diagonal measure. -/
theorem representationPolarizedMeasure_self_apply (ξ : H) {B : Set K} (hB : MeasurableSet B) :
    representationPolarizedMeasure π ξ ξ B = (representationDiagMeasure π ξ).real B := by
  simp [representationPolarizedMeasure_self, withDensityᵥ_one_apply hB]

/-- On the diagonal, the variation of the polarized measure is the diagonal measure. -/
@[simp]
theorem variation_representationPolarizedMeasure_self (ξ : H) :
    (representationPolarizedMeasure π ξ ξ).variation = representationDiagMeasure π ξ := by
  rw [representationPolarizedMeasure_self, Measure.variation_withDensityᵥ_one]

/-- The polarized measure is additive in its first argument. -/
theorem representationPolarizedMeasure_add_left (ψ ψ' ξ : H) :
    representationPolarizedMeasure π (ψ + ψ') ξ =
      representationPolarizedMeasure π ψ ξ + representationPolarizedMeasure π ψ' ξ :=
  ((eq_representationPolarizedMeasure_iff π _ _ _).2 fun f => by
    rw [integral_add_vectorMeasure (f.integrable _) (f.integrable _),
      integral_representationPolarizedMeasure, integral_representationPolarizedMeasure,
      inner_add_left]).symm

/-- The polarized measure is additive in its second argument. -/
theorem representationPolarizedMeasure_add_right (ψ ξ ξ' : H) :
    representationPolarizedMeasure π ψ (ξ + ξ') =
      representationPolarizedMeasure π ψ ξ + representationPolarizedMeasure π ψ ξ' :=
  ((eq_representationPolarizedMeasure_iff π _ _ _).2 fun f => by
    rw [integral_add_vectorMeasure (f.integrable _) (f.integrable _),
      integral_representationPolarizedMeasure, integral_representationPolarizedMeasure,
      _root_.map_add, inner_add_right]).symm

/-- The polarized measure is conjugate-homogeneous in its first argument. -/
theorem representationPolarizedMeasure_smul_left (c : ℂ) (ψ ξ : H) :
    representationPolarizedMeasure π (c • ψ) ξ =
      star c • representationPolarizedMeasure π ψ ξ :=
  ((eq_representationPolarizedMeasure_iff π _ _ _).2 fun f => by
    rw [integral_smul_vectorMeasure_mul, integral_representationPolarizedMeasure,
      inner_smul_left, starRingEnd_apply]).symm

/-- The polarized measure is homogeneous in its second argument. -/
theorem representationPolarizedMeasure_smul_right (c : ℂ) (ψ ξ : H) :
    representationPolarizedMeasure π ψ (c • ξ) = c • representationPolarizedMeasure π ψ ξ :=
  ((eq_representationPolarizedMeasure_iff π _ _ _).2 fun f => by
    rw [integral_smul_vectorMeasure_mul, integral_representationPolarizedMeasure, _root_.map_smul,
      inner_smul_right]).symm

/-- The polarized measure vanishes when its first argument is zero. -/
@[simp]
theorem representationPolarizedMeasure_zero_left (ξ : H) :
    representationPolarizedMeasure π 0 ξ = 0 := by
  simpa using representationPolarizedMeasure_add_left π 0 0 ξ

/-- The polarized measure vanishes when its second argument is zero. -/
@[simp]
theorem representationPolarizedMeasure_zero_right (ψ : H) :
    representationPolarizedMeasure π ψ 0 = 0 := by
  simpa using representationPolarizedMeasure_add_right π ψ 0 0

/-- The total variation of the polarized measure is at most `‖ψ‖² + ‖ξ‖²`, the average of the
masses `‖ξ + iᵏ ψ‖²` of the four diagonal measures. -/
private theorem variation_real_univ_le_add (ψ ξ : H) :
    (representationPolarizedMeasure π ψ ξ).variation.real Set.univ ≤ ‖ψ‖ ^ 2 + ‖ξ‖ ^ 2 := by
  refine (ENNReal.toReal_mono (measure_ne_top _ Set.univ)
    (Measure.le_iff'.1 (variation_representationPolarizedMeasure_le π ψ ξ) Set.univ)).trans_eq ?_
  have h1 := parallelogram_law_with_norm ℂ ξ ψ
  have h2 := parallelogram_law_with_norm ℂ ξ (Complex.I • ψ)
  rw [norm_smul, Complex.norm_I, one_mul] at h2
  rw [← measureReal_def, measureReal_nnreal_smul_apply, measureReal_add_apply,
    measureReal_add_apply, measureReal_add_apply]
  simp only [representationDiagMeasure_real_univ, NNReal.coe_inv, NNReal.coe_ofNat]
  linear_combination (1 / 4 : ℝ) * h1 + (1 / 4 : ℝ) * h2

/-- The total variation of the polarized measure `μ_(ψ,ξ)` is at most `2 ‖ψ‖ ‖ξ‖`. This follows
from the domination by the diagonal measures, after rescaling `ψ` and `ξ` by reciprocal positive
factors, which does not change `μ_(ψ,ξ)`. -/
theorem variation_representationPolarizedMeasure_univ_le (ψ ξ : H) :
    (representationPolarizedMeasure π ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (2 * ‖ψ‖ * ‖ξ‖) := by
  rcases eq_or_ne ψ 0 with rfl | hψ
  · simp
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  set t := Real.sqrt (‖ξ‖ / ‖ψ‖)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = ‖ξ‖ / ‖ψ‖ := Real.sq_sqrt (by positivity)
  have hμ : representationPolarizedMeasure π ψ ξ =
      representationPolarizedMeasure π ((t : ℂ) • ψ) (((t⁻¹ : ℝ) : ℂ) • ξ) := by
    rw [representationPolarizedMeasure_smul_left, representationPolarizedMeasure_smul_right,
      smul_smul]
    simp [ht.ne']
  rw [← ofReal_measureReal, hμ]
  refine ENNReal.ofReal_le_ofReal ((variation_real_univ_le_add π _ _).trans_eq ?_)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, abs_inv, mul_pow,
    inv_pow, ht2]
  field_simp
  ring

/-- **Conjugate symmetry.** Exchanging the two vectors conjugates the polarized measure. -/
theorem representationPolarizedMeasure_swap_apply (ψ ξ : H) (B : Set K) :
    representationPolarizedMeasure π ξ ψ B =
      starRingEnd ℂ (representationPolarizedMeasure π ψ ξ B) := by
  by_cases hB : MeasurableSet B
  swap
  · simp [VectorMeasure.not_measurable _ hB]
  have h1 : ψ + ξ = ξ + ψ := add_comm ψ ξ
  have h2 : ψ + Complex.I • ξ = Complex.I • (ξ - Complex.I • ψ) := by
    simp [smul_sub, smul_smul, add_comm]
  have h3 : ψ - ξ = -(ξ - ψ) := (neg_sub ξ ψ).symm
  have h4 : ψ - Complex.I • ξ = (-Complex.I) • (ξ + Complex.I • ψ) := by
    simp [smul_add, smul_smul, sub_eq_neg_add, add_comm]
  rw [representationPolarizedMeasure_apply π _ _ hB, representationPolarizedMeasure_apply π _ _ hB,
    h1, h2, h3, h4, representationDiagMeasure_smul_of_norm_eq_one π (by simp),
    representationDiagMeasure_smul_of_norm_eq_one π (by simp), representationDiagMeasure_neg]
  simp only [map_mul, map_sub, _root_.map_add, Complex.conj_ofReal, Complex.conj_I, map_div₀,
    map_one, map_ofNat]
  ring

end StarAlgHom
