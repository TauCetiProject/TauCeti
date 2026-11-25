/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Polar.Vector
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Distribution.TestFunction.Integral

/-!
# Examples of the Riesz representation for vector fields

The Riesz representation theorem for vector fields
(`Distribution.massMeasure_eq_of_apply_eq_integral_inner`, `Distribution.ae_eq_polarVector`)
computes the mass measure `‖L‖` and the polar field `η` of a functional `L` on compactly supported
vector fields from any representation `L(X) = ∫ ⟪η, X⟫ dμ` with `|η| = 1` almost everywhere.
Two families of examples:

* `L(X) = ⟪X(a), v⟫` (`evalInner`): `‖L‖ = |v| δ_a` (`massMeasure_evalInner`) and, for `v ≠ 0`,
  `η(a) = v / |v|` (`polarVector_evalInner`). On `ℝ^N` with `v = 2eᵢ` this is `‖L‖ = 2δ₀` and
  `η(0) = eᵢ` (`massMeasure_evalInner_single_two`, `polarVector_evalInner_single_two`);
  for `v = 0`, `L = 0` and `‖L‖ = 0` (`massMeasure_evalInner_zero`), so no value of `η` is
  determined.
* `L(X) = ∫ ⟪u, X⟫ dμ` (`integralInner`): `‖L‖ = |u| μ` (`massMeasure_integralInner`) and
  `η = u / |u|` almost everywhere (`polarVector_integralInner`). On `ℝ²` with `u = (1, 1)`,
  `L(X) = ∫ (X¹ + X²) dy` has `‖L‖ = √2` times Lebesgue measure and `η = (e₁ + e₂) / √2`
  (`massMeasure_integralInner_oneOne`, `polarVector_integralInner_oneOne`), not the `2 vol` that
  a coordinatewise total variation would give.
-/

@[expose] public section

noncomputable section

namespace TauCeti.Examples.PolarVector

open MeasureTheory TopologicalSpace Distribution
open scoped ENNReal NNReal Distributions RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {Ω : Opens E} {n : ℕ∞}

/-! ### Point evaluation -/

/-- The functional `L(X) = ⟪X(a), v⟫` on the `F`-valued test functions of class `C^n` on `Ω`. -/
def evalInner (n : ℕ∞) (a : Ω) (v : F) : 𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ where
  toFun φ := ⟪φ a, v⟫
  map_add' φ ψ := by simp [inner_add_left]
  map_smul' c φ := by simp [real_inner_smul_left]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
theorem evalInner_apply (a : Ω) (v : F) (φ : 𝓓^{n}(Ω, F)) : evalInner n a v φ = ⟪φ a, v⟫ :=
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The evaluation `⟪X(a), v⟫` is `∫ ⟪v / |v|, X⟫ d(|v| δ_a)`. -/
private theorem evalInner_eq_integral_inner_normalize (a : Ω) (v : F) (φ : 𝓓^{n}(Ω, F)) :
    evalInner n a v φ = ∫ x, ⟪‖v‖⁻¹ • v, φ x⟫ ∂(‖v‖₊ • Measure.dirac a) := by
  rw [integral_smul_nnreal_measure, integral_dirac, evalInner_apply, NNReal.smul_def,
    coe_nnNorm, smul_eq_mul, real_inner_smul_left, ← mul_assoc]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_mul, real_inner_comm]

/-- The functional `L(X) = ⟪X(a), v⟫` has mass measure `|v| δ_a`. -/
theorem massMeasure_evalInner (a : Ω) (v : F) :
    massMeasure (evalInner n a v) = ‖v‖₊ • Measure.dirac a := by
  refine massMeasure_eq_of_apply_eq_integral_inner (η := fun _ => ‖v‖⁻¹ • v)
    aestronglyMeasurable_const ?_ (evalInner_eq_integral_inner_normalize a v)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact Filter.Eventually.of_forall fun _ => norm_smul_inv_norm hv

/-- For `v ≠ 0`, the polar vector field of `L(X) = ⟪X(a), v⟫` at `a` is `v / |v|`. -/
theorem polarVector_evalInner (a : Ω) {v : F} (hv : v ≠ 0) :
    polarVector (evalInner n a v) a = ‖v‖⁻¹ • v := by
  have h : ∀ᵐ x ∂massMeasure (evalInner n a v),
      (fun _ => ‖v‖⁻¹ • v) x = polarVector (evalInner n a v) x :=
    ae_eq_polarVector (by rw [massMeasure_evalInner]; exact locallyIntegrable_const _) fun φ => by
      rw [massMeasure_evalInner]; exact evalInner_eq_integral_inner_normalize a v φ
  rw [massMeasure_evalInner, Measure.ae_smul_measure_iff (by simpa using hv), ae_dirac_eq] at h
  exact (Filter.eventually_pure.1 h).symm

/-- For `v = 0` the functional is zero and so is its mass measure. -/
theorem massMeasure_evalInner_zero (a : Ω) :
    massMeasure (evalInner n a (0 : F)) = 0 := by
  simp [massMeasure_evalInner]

/-- On `ℝ^N` with `v = 2eᵢ`, `‖L‖ = 2δ₀`. -/
theorem massMeasure_evalInner_single_two {N : ℕ} (i : Fin N) :
    massMeasure (evalInner n (⟨0, trivial⟩ : (⊤ : Opens (EuclideanSpace ℝ (Fin N))))
      (EuclideanSpace.single i (2 : ℝ))) = (2 : ℝ≥0) • Measure.dirac ⟨0, trivial⟩ := by
  rw [massMeasure_evalInner]
  congr 1
  ext
  simp

/-- On `ℝ^N` with `v = 2eᵢ`, `η(0) = eᵢ`. -/
theorem polarVector_evalInner_single_two {N : ℕ} (i : Fin N) :
    polarVector (evalInner n (⟨0, trivial⟩ : (⊤ : Opens (EuclideanSpace ℝ (Fin N))))
      (EuclideanSpace.single i (2 : ℝ))) ⟨0, trivial⟩ = EuclideanSpace.single i 1 := by
  rw [polarVector_evalInner _ (by simp)]
  ext j
  by_cases hj : j = i <;> simp [hj]

/-! ### Integration against a constant vector -/

variable [OpensMeasurableSpace E]

/-- The functional `L(X) = ∫ ⟪u, X⟫ dμ` on the `F`-valued test functions of class `C^n` on `Ω`. -/
def integralInner (n : ℕ∞) (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] (u : F) :
    𝓓^{n}(Ω, F) →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, ⟪u, φ x⟫ ∂μ
  map_add' φ ψ := by
    have := Ω.isOpen.locallyCompactSpace
    simp only [FunLike.coe_add, Pi.add_apply, inner_add_right]
    exact integral_add
      ((φ.integrable_inner_subtype (locallyIntegrable_const u)).congr
        (Filter.Eventually.of_forall fun _ => real_inner_comm _ _))
      ((ψ.integrable_inner_subtype (locallyIntegrable_const u)).congr
        (Filter.Eventually.of_forall fun _ => real_inner_comm _ _))
  map_smul' c φ := by
    simp [inner_smul_right, integral_const_mul]

omit [BorelSpace E] [FiniteDimensional ℝ F] in
theorem integralInner_apply (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] (u : F)
    (φ : 𝓓^{n}(Ω, F)) :
    integralInner n μ u φ = ∫ x, ⟪u, φ x⟫ ∂μ :=
  rfl

omit [BorelSpace E] [FiniteDimensional ℝ F] in
/-- The pairing `∫ ⟪u, X⟫ dμ` is `∫ ⟪u / |u|, X⟫ d(|u| μ)`. -/
private theorem integralInner_eq_integral_inner_normalize (μ : Measure Ω)
    [IsFiniteMeasureOnCompacts μ] (u : F) (φ : 𝓓^{n}(Ω, F)) :
    integralInner n μ u φ = ∫ x, ⟪‖u‖⁻¹ • u, φ x⟫ ∂(‖u‖₊ • μ) := by
  rw [integral_smul_nnreal_measure, integralInner_apply, NNReal.smul_def, coe_nnNorm]
  simp only [real_inner_smul_left, integral_const_mul, smul_eq_mul, ← mul_assoc]
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hu), one_mul]

/-- The functional `L(X) = ∫ ⟪u, X⟫ dμ`, for a measure `μ` finite on compact sets, has mass
measure `|u| μ`. -/
theorem massMeasure_integralInner (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] (u : F) :
    massMeasure (integralInner n μ u) = ‖u‖₊ • μ := by
  refine massMeasure_eq_of_apply_eq_integral_inner (η := fun _ => ‖u‖⁻¹ • u)
    aestronglyMeasurable_const ?_ (integralInner_eq_integral_inner_normalize μ u)
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact Filter.Eventually.of_forall fun _ => norm_smul_inv_norm hu

/-- The polar vector field of `L(X) = ∫ ⟪u, X⟫ dμ` is `u / |u|` at `‖L‖`-almost every point. -/
theorem polarVector_integralInner (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] (u : F) :
    ∀ᵐ x ∂massMeasure (integralInner n μ u),
      polarVector (integralInner n μ u) x = ‖u‖⁻¹ • u := by
  have := Ω.isOpen.locallyCompactSpace
  refine (ae_eq_polarVector (by rw [massMeasure_integralInner]; exact locallyIntegrable_const _)
    fun φ => ?_).mono fun _ hx => hx.symm
  rw [integralInner_eq_integral_inner_normalize, massMeasure_integralInner]

/-- The vector `(1, 1)` of `ℝ²`. -/
def oneOne : EuclideanSpace ℝ (Fin 2) := !₂[1, 1]

/-- The vector `(1, 1)` of `ℝ²` has norm `√2`. -/
theorem norm_oneOne : ‖oneOne‖ = √2 := by
  rw [oneOne, EuclideanSpace.norm_eq]
  norm_num [Fin.sum_univ_two]

/-- The pairing with `(1, 1)` is the sum of the coordinates. -/
theorem inner_oneOne (y : EuclideanSpace ℝ (Fin 2)) :
    ⟪oneOne, y⟫ = y 0 + y 1 := by
  simp [oneOne, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

/-- On `ℝ²`, `L(X) = ∫ (X¹ + X²) dy` against a measure `μ` finite on compact sets has mass measure
`√2 μ`; for Lebesgue measure this is `√2` times Lebesgue measure, not `2` times it. -/
theorem massMeasure_integralInner_oneOne {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] :
    massMeasure (integralInner n μ oneOne) = NNReal.sqrt 2 • μ := by
  rw [massMeasure_integralInner]
  congr 1
  ext
  simp [norm_oneOne]

/-- On `ℝ²`, the polar vector field of `L(X) = ∫ (X¹ + X²) dy` is `(e₁ + e₂) / √2` almost
everywhere. -/
theorem polarVector_integralInner_oneOne {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] :
    ∀ᵐ x ∂massMeasure (integralInner n μ oneOne),
      polarVector (integralInner n μ oneOne) x = (√2)⁻¹ • oneOne := by
  simpa [norm_oneOne] using polarVector_integralInner (n := n) μ oneOne

end TauCeti.Examples.PolarVector
