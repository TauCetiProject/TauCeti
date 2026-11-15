/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import TauCeti.Probability.Distributions.Beta.Symmetric

/-!
# Determinant moments of independent Beta partial correlations

Construct a correlation matrix from independent partial correlations `Zᵢⱼ`, each obtained by
centering a symmetric `Beta(aᵢⱼ, aᵢⱼ)` variable on `(-1, 1)`. Its determinant is the product of
the residual factors `1 - Zᵢⱼ²`. A real power `q` of this determinant is integrable exactly when
every shifted shape `aᵢⱼ + q` is positive; its expectation is a product of beta quotients.

For the column-dependent shapes `aᵢⱼ = η + (p - j - 2) / 2`, using zero-based indices, this
gives the sharp threshold `q > -η` in dimensions at least two. In dimensions zero and one
there are no partial correlations and every determinant power has expectation one.
These results provide the determinant-moment calculation for the independent-Beta
construction of random correlation matrices, including divergence at the endpoint.

The calculation uses `det_partialCorrelationGram` and the weighted moments of centered
symmetric Beta laws from `TauCeti.Probability.Distributions.Beta.Symmetric`.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {p : ℕ} {a : strictLowerTriangle p → ℝ} {q : ℝ}

private theorem ae_partialCorrelation_cube (ha : ∀ ij, 0 < a ij) :
    ∀ᵐ z ∂Measure.pi (fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)),
      ∀ ij, |z ij| < 1 := by
  let _ (ij) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  refine Filter.eventually_all.2 fun ij ↦ ?_
  have hij : ∀ᵐ z ∂(betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x), |z| < 1 := by
    apply (ae_map_iff (by fun_prop) (by measurability)).2
    filter_upwards [ae_mem_Ioo_betaMeasure (a ij) (a ij)] with x hx
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact (Measure.tendsto_eval_ae_ae (i := ij) (μ := fun ij : strictLowerTriangle p ↦
    (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x))).eventually hij

private theorem ae_rpow_det_partialCorrelationGram (ha : ∀ ij, 0 < a ij) (q : ℝ) :
    (fun z ↦ (partialCorrelationGram z).det ^ q) =ᵐ[
      Measure.pi (fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x))]
      fun z ↦ ∏ ij, (1 - z ij ^ 2) ^ q := by
  filter_upwards [ae_partialCorrelation_cube ha] with z hz
  rw [det_partialCorrelationGram (fun ij ↦ (hz ij).le),
    Real.finsetProd_rpow _ _ (fun ij _ ↦
      (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))).le)]

/-- The determinant power of a correlation matrix built from independent centered symmetric
Beta variables is integrable exactly when every shifted shape is positive. This includes
empty coordinate types and divergence when any shifted shape is zero. -/
@[simp]
theorem integrable_rpow_det_partialCorrelationGram_pi_betaMeasure_iff (ha : ∀ ij, 0 < a ij) :
    Integrable (fun z ↦ (partialCorrelationGram z).det ^ q)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) ↔
      ∀ ij, 0 < a ij + q := by
  let μ := fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)
  let _ (ij) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  rw [integrable_congr (ae_rpow_det_partialCorrelationGram ha q)]
  constructor
  · intro h ij
    by_cases hq : 0 ≤ q
    · linarith [ha ij]
    have hfactor : Integrable (fun z : strictLowerTriangle p → ℝ ↦ (1 - z ij ^ 2) ^ q)
        (Measure.pi μ) := by
      apply h.mono' (by fun_prop : Measurable _).aestronglyMeasurable
      filter_upwards [ae_partialCorrelation_cube ha] with z hz
      have hpos (k) : 0 < 1 - z k ^ 2 :=
        sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hz k))
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hpos ij) q)]
      simpa using Finset.prod_le_prod_of_subset_of_one_le₀
        (f := fun k ↦ (1 - z k ^ 2) ^ q)
        (Finset.singleton_subset_iff.mpr (Finset.mem_univ ij))
        (fun k _ ↦ (Real.rpow_pos_of_pos (hpos k) q).le) (fun k _ _ ↦
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hpos k)
            (by nlinarith [sq_nonneg (z k)]) (le_of_not_ge hq))
    have hi : Integrable (fun z : ℝ ↦ (1 - z ^ 2) ^ q) (μ ij) := by
      rw [← (measurePreserving_eval μ ij).map_eq]
      exact (integrable_map_measure (g := fun z : ℝ ↦ (1 - z ^ 2) ^ q)
        (by fun_prop : Measurable _).aestronglyMeasurable
        (measurable_pi_apply ij).aemeasurable).2 hfactor
    simpa using (integrable_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff
      (ha ij) 0).1 (by simpa using hi)
  · intro hq
    simpa using integrable_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
      a (fun _ ↦ q) (fun _ ↦ 0) ha hq

/-- The determinant-power moment of the independent symmetric-Beta construction factors
into beta quotients on its exact absolute-integrability domain. -/
theorem integral_rpow_det_partialCorrelationGram_pi_betaMeasure (ha : ∀ ij, 0 < a ij)
    (hq : ∀ ij, 0 < a ij + q) :
    ∫ z, (partialCorrelationGram z).det ^ q
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∏ ij, beta (1 / 2) (a ij + q) / beta (1 / 2) (a ij) := by
  rw [integral_congr_ae (ae_rpow_det_partialCorrelationGram ha q)]
  simpa using integral_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    a (fun _ ↦ q) (fun _ ↦ 0) ha hq

/-- In dimensions zero and one the independent-Beta construction has determinant one,
so every real-power determinant moment is one without restrictions on the exponent. -/
theorem integral_rpow_det_partialCorrelationGram_pi_betaMeasure_of_le_one (hp : p ≤ 1)
    (a : strictLowerTriangle p → ℝ) (q : ℝ) :
    ∫ z, (partialCorrelationGram z).det ^ q
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) = 1 := by
  let _ : IsEmpty (strictLowerTriangle p) := ⟨fun ij ↦ by
    have := ij.2
    have := ij.1.1.isLt
    omega⟩
  simpa using integral_rpow_det_partialCorrelationGram_pi_betaMeasure
    (a := a) (q := q) (fun ij ↦ isEmptyElim ij) (fun ij ↦ isEmptyElim ij)

/-- At the column-dependent shapes of the LKJ construction, determinant powers are
integrable precisely above `-η`, except in dimensions zero and one where every power is
integrable. The least shape occurs at the final strictly lower coordinate. -/
@[simp]
theorem integrable_rpow_det_partialCorrelationGram_pi_betaMeasure_lkj_iff
    {η : ℝ} (hη : 0 < η) :
    Integrable (fun z ↦ (partialCorrelationGram z).det ^ q)
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (η + ((p : ℝ) - ij.1.2 - 2) / 2)
          (η + ((p : ℝ) - ij.1.2 - 2) / 2)).map (fun x ↦ -1 + 2 * x)) ↔
      p ≤ 1 ∨ -η < q := by
  have hcol (ij : strictLowerTriangle p) : (ij.1.2 : ℝ) + 2 ≤ p := by
    have hnat : ij.1.2.val + 2 ≤ p := by have := ij.2; have := ij.1.1.isLt; omega
    exact_mod_cast hnat
  rw [integrable_rpow_det_partialCorrelationGram_pi_betaMeasure_iff
    (fun ij ↦ by linarith [hcol ij])]
  constructor
  · intro h
    by_cases hp : p ≤ 1
    · exact Or.inl hp
    right
    let ij : strictLowerTriangle p :=
      ⟨(⟨p - 1, by omega⟩, ⟨p - 2, by omega⟩), by simp only [Fin.lt_def]; omega⟩
    have hlast := h ij
    have hval : (ij.1.2 : ℝ) = (p : ℝ) - 2 := by
      dsimp [ij]
      rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
    rw [hval] at hlast
    linarith
  · rintro (hp | hq) ij
    · have := ij.2
      have := ij.1.1.isLt
      omega
    · linarith [hcol ij]

end TauCeti.Probability
