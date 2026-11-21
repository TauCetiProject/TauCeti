/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Hermite beta ensemble

For a real parameter `β > 0` and a size `n`, the Hermite (Gaussian) beta ensemble is the
probability measure on `Fin n → ℝ` whose density with respect to Lebesgue measure is proportional
to the weight
`exp (-(β n / 4) ∑ᵢ xᵢ²) ∏_{i<j} |xᵢ - xⱼ| ^ β`.
This is the normalization of Anderson–Guionnet–Zeitouni, Theorem 2.5.2, rescaled by `√n`: for
`β = 1, 2` that theorem identifies it with the unordered eigenvalue law of the GOE and GUE whose
off-diagonal entries have variance `1 / n`. Its logarithmic gradient is `β n` times the drift
`n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹ - xᵢ / 2` of the Ornstein–Uhlenbeck version of Dyson Brownian motion
with parameter `β`, which is why it is the candidate invariant law of that system. Neither
identification is proved in this file.

The weight is bounded by a product of one-dimensional Gaussians, because
`|xᵢ - xⱼ| ^ β ≤ exp (β (|xᵢ| + |xⱼ|))`; so it is integrable, and it is continuous and positive off
the collision hyperplanes, so its integral, the partition function, is positive. Dividing by it
gives a probability density for every `β > 0` and every `n`, without the explicit value of the
partition function (the Gaussian Selberg integral). The weight is the Gaussian factor times the
`β`-th power of the absolute Vandermonde determinant, so it vanishes exactly on collisions when
`β ≠ 0` and the ensemble is invariant under permutations of the coordinates. For `n = 1` the
ensemble is the centred Gaussian of variance `2 / β`.

## Main definitions

* `TauCeti.Probability.hermiteBetaWeight`: the unnormalized weight.
* `TauCeti.Probability.hermiteBetaPartition`: its integral, the partition function.
* `TauCeti.Probability.hermiteBetaPDFReal`, `TauCeti.Probability.hermiteBetaPDF`: the normalized
  density, real- and `ℝ≥0∞`-valued.
* `TauCeti.Probability.hermiteBetaEnsemble`: the measure with that density.

## Main results

* `TauCeti.Probability.hermiteBetaWeight_eq`: the weight in terms of the Vandermonde determinant.
* `TauCeti.Probability.hermiteBetaWeight_le`: domination by a product of Gaussians.
* `TauCeti.Probability.integrable_hermiteBetaWeight` and
  `TauCeti.Probability.hermiteBetaPartition_pos`: the partition function is finite and positive.
* `TauCeti.Probability.isProbabilityMeasure_hermiteBetaEnsemble`.
* `TauCeti.Probability.integral_hermiteBetaEnsemble_eq_integral_smul`: integrals against the
  ensemble are integrals against its real density.
* `TauCeti.Probability.measurePreserving_comp_perm_hermiteBetaEnsemble`: permutation invariance.
* `TauCeti.Probability.hermiteBetaEnsemble_one_map_eval_zero`: for `n = 1` the ensemble is
  `gaussianReal 0 (2 / β)`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §2.5 and §4.5.1.
* I. Dumitriu, A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {β : ℝ} {n : ℕ}

/-! ### The weight -/

/-- The **unnormalized Hermite beta weight** `exp (-(β n / 4) ∑ᵢ xᵢ²) ∏_{i<j} |xᵢ - xⱼ| ^ β` on
`Fin n → ℝ`. -/
def hermiteBetaWeight (β : ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  rexp (-(β * n / 4) * ∑ i, x i ^ 2) * ∏ i, ∏ j ∈ Finset.Ioi i, |x i - x j| ^ β

/-- Defining formula for `TauCeti.Probability.hermiteBetaWeight`. -/
theorem hermiteBetaWeight_def (β : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaWeight β n x =
      rexp (-(β * n / 4) * ∑ i, x i ^ 2) * ∏ i, ∏ j ∈ Finset.Ioi i, |x i - x j| ^ β := (rfl)

/-- The Hermite beta weight is the Gaussian factor times the `β`-th power of the absolute
Vandermonde determinant. -/
theorem hermiteBetaWeight_eq (β : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaWeight β n x =
      rexp (-(β * n / 4) * ∑ i, x i ^ 2) * |(Matrix.vandermonde x).det| ^ β := by
  rw [hermiteBetaWeight_def, Matrix.det_vandermonde, Finset.abs_prod,
    ← Real.finsetProd_rpow _ _ fun _ _ ↦ abs_nonneg _]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.abs_prod, ← Real.finsetProd_rpow _ _ fun _ _ ↦ abs_nonneg _]
  exact Finset.prod_congr rfl fun j _ ↦ by rw [abs_sub_comm]

/-- The Hermite beta weight is nonnegative. -/
theorem hermiteBetaWeight_nonneg (β : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ hermiteBetaWeight β n x := by
  rw [hermiteBetaWeight_eq]
  positivity

/-- The Hermite beta weight is positive at configurations without collisions. -/
theorem hermiteBetaWeight_pos {x : Fin n → ℝ} (hx : Function.Injective x) :
    0 < hermiteBetaWeight β n x := by
  rw [hermiteBetaWeight_eq]
  exact mul_pos (exp_pos _)
    (rpow_pos_of_pos (abs_pos.2 (Matrix.det_vandermonde_ne_zero_iff.2 hx)) _)

/-- For `β ≠ 0` the Hermite beta weight vanishes exactly at the configurations with a
collision. -/
theorem hermiteBetaWeight_eq_zero_iff (hβ : β ≠ 0) {x : Fin n → ℝ} :
    hermiteBetaWeight β n x = 0 ↔ ¬Function.Injective x := by
  refine ⟨fun h hx ↦ (hermiteBetaWeight_pos hx).ne' h, fun hx ↦ ?_⟩
  have hdet : (Matrix.vandermonde x).det = 0 :=
    by_contra fun h ↦ hx (Matrix.det_vandermonde_ne_zero_iff.1 h)
  rw [hermiteBetaWeight_eq, hdet, abs_zero, zero_rpow hβ, mul_zero]

/-- The Hermite beta weight is invariant under permutations of the coordinates. -/
@[simp]
theorem hermiteBetaWeight_comp_perm (β : ℝ) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) : hermiteBetaWeight β n (x ∘ σ) = hermiteBetaWeight β n x := by
  have hV : Matrix.vandermonde (x ∘ σ) = (Matrix.vandermonde x).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [hermiteBetaWeight_eq, hermiteBetaWeight_eq, hV, Matrix.det_permute, abs_mul]
  simp only [Function.comp_apply, Equiv.sum_comp σ fun i ↦ x i ^ 2]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- The Hermite beta weight is measurable. -/
theorem measurable_hermiteBetaWeight (β : ℝ) (n : ℕ) : Measurable (hermiteBetaWeight β n) := by
  simp_rw [funext (hermiteBetaWeight_def β n)]
  fun_prop

/-- For `β ≥ 0` the Hermite beta weight is continuous. -/
theorem continuous_hermiteBetaWeight (hβ : 0 ≤ β) (n : ℕ) :
    Continuous (hermiteBetaWeight β n) := by
  simp_rw [funext (hermiteBetaWeight_def β n)]
  refine (continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).pow 2))).mul
      (continuous_finsetProd _ fun i _ ↦ continuous_finsetProd _ fun j _ ↦ ?_)
  exact (continuous_rpow_const hβ).comp ((continuous_apply i).sub (continuous_apply j)).abs

/-- **Gaussian domination of the Hermite beta weight**: for `β ≥ 0` the weight is at most a
product of one-dimensional Gaussian factors, one for each coordinate. -/
theorem hermiteBetaWeight_le (hβ : 0 ≤ β) (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaWeight β n x ≤ ∏ i, (rexp (8 * β * n) * rexp (-(β * n / 8) * x i ^ 2)) := by
  -- each repulsion factor is at most `exp (β (|xᵢ| + |xⱼ|))`
  have hpair (i j : Fin n) : |x i - x j| ^ β ≤ rexp (β * (|x i| + |x j|)) := by
    calc |x i - x j| ^ β ≤ rexp |x i - x j| ^ β := by
          gcongr
          linarith [add_one_le_exp |x i - x j|]
      _ = rexp (β * |x i - x j|) := by rw [← exp_mul, mul_comm]
      _ ≤ rexp (β * (|x i| + |x j|)) := by gcongr; exact abs_sub _ _
  -- the sum over pairs `i < j` is at most the sum over all pairs, `2 n ∑ᵢ |xᵢ|`
  have hsum : ∑ i, ∑ j ∈ Finset.Ioi i, β * (|x i| + |x j|) ≤ ∑ i, 2 * β * n * |x i| := by
    calc ∑ i, ∑ j ∈ Finset.Ioi i, β * (|x i| + |x j|)
        ≤ ∑ i, ∑ j, β * (|x i| + |x j|) := Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ by positivity
      _ = ∑ i, 2 * β * n * |x i| := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  calc hermiteBetaWeight β n x
      ≤ rexp (-(β * n / 4) * ∑ i, x i ^ 2) *
          ∏ i, ∏ j ∈ Finset.Ioi i, rexp (β * (|x i| + |x j|)) := by
        rw [hermiteBetaWeight_def]
        gcongr with i _ j _
        exact hpair i j
    _ ≤ rexp (∑ i, (8 * β * n + -(β * n / 8) * x i ^ 2)) := by
        simp only [← exp_sum, ← exp_add]
        gcongr
        rw [Finset.mul_sum]
        refine (add_le_add le_rfl hsum).trans ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hβn : 0 ≤ β * n := by positivity
        nlinarith [mul_nonneg hβn (sq_nonneg (|x i| - 8)), sq_abs (x i)]
    _ = ∏ i, (rexp (8 * β * n) * rexp (-(β * n / 8) * x i ^ 2)) := by
        simp only [exp_sum, exp_add]

/-- For `β > 0` the Hermite beta weight is integrable. -/
theorem integrable_hermiteBetaWeight (hβ : 0 < β) (n : ℕ) :
    Integrable (hermiteBetaWeight β n) := by
  refine Integrable.mono' (Integrable.fintype_prod (f := fun _ y ↦
      rexp (8 * β * n) * rexp (-(β * n / 8) * y ^ 2)) fun i ↦ ?_)
    (measurable_hermiteBetaWeight β n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  · have := i.pos
    exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  · rw [Real.norm_of_nonneg (hermiteBetaWeight_nonneg β n x)]
    exact hermiteBetaWeight_le hβ.le n x

/-! ### The partition function and the normalized density -/

/-- The **partition function** of the Hermite beta ensemble, the integral of
`TauCeti.Probability.hermiteBetaWeight` over `Fin n → ℝ`. -/
def hermiteBetaPartition (β : ℝ) (n : ℕ) : ℝ :=
  ∫ x, hermiteBetaWeight β n x

/-- Defining formula for `TauCeti.Probability.hermiteBetaPartition`. -/
theorem hermiteBetaPartition_def (β : ℝ) (n : ℕ) :
    hermiteBetaPartition β n = ∫ x, hermiteBetaWeight β n x := (rfl)

/-- For `β > 0` the partition function of the Hermite beta ensemble is positive. -/
theorem hermiteBetaPartition_pos (hβ : 0 < β) (n : ℕ) : 0 < hermiteBetaPartition β n := by
  rw [hermiteBetaPartition_def, integral_pos_iff_support_of_nonneg
    (hermiteBetaWeight_nonneg β n) (integrable_hermiteBetaWeight hβ n)]
  refine (continuous_hermiteBetaWeight hβ.le n).isOpen_support.measure_pos volume
    ⟨fun i ↦ (i : ℝ), (hermiteBetaWeight_pos fun i j h ↦ ?_).ne'⟩
  exact Fin.ext (Nat.cast_injective h)

/-- The one-point Hermite beta weight is the Gaussian factor `exp (-β x² / 4)`. -/
@[simp]
theorem hermiteBetaWeight_one (β : ℝ) (x : Fin 1 → ℝ) :
    hermiteBetaWeight β 1 x = rexp (-(β / 4) * x 0 ^ 2) := by
  simp [hermiteBetaWeight_eq, Matrix.det_unique, Matrix.vandermonde_apply]

/-- The partition function of the one-point Hermite beta ensemble is `√(4π / β)`. -/
@[simp]
theorem hermiteBetaPartition_one (β : ℝ) : hermiteBetaPartition β 1 = √(4 * π / β) := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
    (g := fun y ↦ rexp (-(β / 4) * y ^ 2))
  rw [integral_gaussian, div_div_eq_mul_div, mul_comm π 4] at h
  rw [hermiteBetaPartition_def, funext (hermiteBetaWeight_one β)]
  exact h

/-- The **normalized Hermite beta density**, the weight divided by the partition function. -/
def hermiteBetaPDFReal (β : ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (hermiteBetaPartition β n)⁻¹ * hermiteBetaWeight β n x

/-- Defining formula for `TauCeti.Probability.hermiteBetaPDFReal`. -/
theorem hermiteBetaPDFReal_def (β : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaPDFReal β n x = (hermiteBetaPartition β n)⁻¹ * hermiteBetaWeight β n x := (rfl)

/-- The `ℝ≥0∞`-valued normalized Hermite beta density. -/
def hermiteBetaPDF (β : ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (hermiteBetaPDFReal β n x)

/-- Defining formula for `TauCeti.Probability.hermiteBetaPDF`. -/
theorem hermiteBetaPDF_def (β : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    hermiteBetaPDF β n x = ENNReal.ofReal (hermiteBetaPDFReal β n x) := (rfl)

/-- The normalized Hermite beta density is nonnegative. -/
theorem hermiteBetaPDFReal_nonneg (β : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ hermiteBetaPDFReal β n x :=
  mul_nonneg (inv_nonneg.2 (integral_nonneg (hermiteBetaWeight_nonneg β n)))
    (hermiteBetaWeight_nonneg β n x)

/-- The normalized Hermite beta density is measurable. -/
theorem measurable_hermiteBetaPDFReal (β : ℝ) (n : ℕ) : Measurable (hermiteBetaPDFReal β n) :=
  (measurable_hermiteBetaWeight β n).const_mul _

/-- The `ℝ≥0∞`-valued normalized Hermite beta density is measurable. -/
theorem measurable_hermiteBetaPDF (β : ℝ) (n : ℕ) : Measurable (hermiteBetaPDF β n) :=
  (measurable_hermiteBetaPDFReal β n).ennreal_ofReal

/-- The real normalized Hermite beta density is invariant under permutations of the
coordinates. -/
@[simp]
theorem hermiteBetaPDFReal_comp_perm (β : ℝ) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) : hermiteBetaPDFReal β n (x ∘ σ) = hermiteBetaPDFReal β n x := by
  rw [hermiteBetaPDFReal_def, hermiteBetaWeight_comp_perm, hermiteBetaPDFReal_def]

/-- The normalized Hermite beta density is invariant under permutations of the coordinates. -/
@[simp]
theorem hermiteBetaPDF_comp_perm (β : ℝ) (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    hermiteBetaPDF β n (x ∘ σ) = hermiteBetaPDF β n x := by
  rw [hermiteBetaPDF_def, hermiteBetaPDFReal_comp_perm, hermiteBetaPDF_def]

/-- For `β > 0` the normalized Hermite beta density is integrable. -/
theorem integrable_hermiteBetaPDFReal (hβ : 0 < β) (n : ℕ) :
    Integrable (hermiteBetaPDFReal β n) :=
  (integrable_hermiteBetaWeight hβ n).const_mul _

/-- For `β > 0` the normalized Hermite beta density integrates to `1`. -/
theorem integral_hermiteBetaPDFReal (hβ : 0 < β) (n : ℕ) :
    ∫ x, hermiteBetaPDFReal β n x = 1 := by
  simp_rw [hermiteBetaPDFReal_def]
  rw [integral_const_mul, ← hermiteBetaPartition_def,
    inv_mul_cancel₀ (hermiteBetaPartition_pos hβ n).ne']

/-- For `β > 0` the `ℝ≥0∞`-valued Hermite beta density has total mass `1`. -/
theorem lintegral_hermiteBetaPDF (hβ : 0 < β) (n : ℕ) : ∫⁻ x, hermiteBetaPDF β n x = 1 := by
  simp_rw [hermiteBetaPDF_def]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_hermiteBetaPDFReal hβ n)
      (Filter.Eventually.of_forall (hermiteBetaPDFReal_nonneg β n)),
    integral_hermiteBetaPDFReal hβ n, ENNReal.ofReal_one]

/-! ### The ensemble -/

/-- The **Hermite beta ensemble** of size `n` and parameter `β`: the measure on `Fin n → ℝ` with
density `TauCeti.Probability.hermiteBetaPDF β n` with respect to Lebesgue measure. It is a
probability measure for `β > 0`
(`TauCeti.Probability.isProbabilityMeasure_hermiteBetaEnsemble`). -/
def hermiteBetaEnsemble (β : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.withDensity (hermiteBetaPDF β n)

/-- Defining formula for `TauCeti.Probability.hermiteBetaEnsemble`. -/
theorem hermiteBetaEnsemble_def (β : ℝ) (n : ℕ) :
    hermiteBetaEnsemble β n = volume.withDensity (hermiteBetaPDF β n) := (rfl)

/-- For `β > 0` the Hermite beta ensemble is a probability measure. -/
theorem isProbabilityMeasure_hermiteBetaEnsemble (hβ : 0 < β) (n : ℕ) :
    IsProbabilityMeasure (hermiteBetaEnsemble β n) :=
  ⟨by rw [hermiteBetaEnsemble_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_hermiteBetaPDF hβ n]⟩

/-- Integrating against the Hermite beta ensemble is integrating against its real density with
respect to Lebesgue measure. -/
theorem integral_hermiteBetaEnsemble_eq_integral_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (β : ℝ) (n : ℕ) (f : (Fin n → ℝ) → E) :
    ∫ x, f x ∂hermiteBetaEnsemble β n = ∫ x, hermiteBetaPDFReal β n x • f x := by
  rw [hermiteBetaEnsemble_def, integral_withDensity_eq_integral_toReal_smul
    (measurable_hermiteBetaPDF β n) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [hermiteBetaPDF_def, ENNReal.toReal_ofReal (hermiteBetaPDFReal_nonneg β n _)]

/-- The Hermite beta ensemble is invariant under permutations of the coordinates. -/
theorem measurePreserving_comp_perm_hermiteBetaEnsemble (β : ℝ) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ ↦ x ∘ σ) (hermiteBetaEnsemble β n)
      (hermiteBetaEnsemble β n) := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) := MeasurableEquiv.arrowCongr' σ.symm (.refl ℝ)
  have he : ⇑e = fun x ↦ x ∘ σ := by
    ext x i
    rw [← MeasurableEquiv.coe_toEquiv]
    exact Equiv.arrowCongr'_apply σ.symm (Equiv.refl ℝ) x i
  have hvol : MeasurePreserving e volume volume :=
    volume_preserving_arrowCongr' σ.symm (.refl ℝ) (.id volume)
  have hpdf : hermiteBetaPDF β n ∘ e = hermiteBetaPDF β n := by
    funext x
    simp [he]
  rw [← he]
  refine ⟨e.measurable, ?_⟩
  conv_lhs => rw [hermiteBetaEnsemble_def, ← hpdf]
  rw [e.measurableEmbedding.map_withDensity_comp, hvol.map_eq, hermiteBetaEnsemble_def]

/-- **The one-point Hermite beta ensemble is Gaussian**: for `β > 0` and `n = 1` the ensemble is
the centred Gaussian of variance `2 / β`, whose density is proportional to `exp (-β x² / 4)`. -/
theorem hermiteBetaEnsemble_one_map_eval_zero (hβ : 0 < β) :
    (hermiteBetaEnsemble β 1).map (fun x ↦ x 0) = gaussianReal 0 (2 / β).toNNReal := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have he : ⇑e = fun x ↦ x 0 := by
    rw [MeasurableEquiv.funUnique_apply, Fin.default_eq_zero]
  have hvol : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have hv : (2 / β).toNNReal ≠ 0 := by simpa using hβ
  have hpdf : hermiteBetaPDF β 1 = gaussianPDF 0 (2 / β).toNNReal ∘ e := by
    funext x
    simp only [Function.comp_apply, hermiteBetaPDF_def, gaussianPDF_def, gaussianPDFReal_def,
      hermiteBetaPDFReal_def, hermiteBetaPartition_one, hermiteBetaWeight_one, he,
      Real.coe_toNNReal _ (by positivity : 0 ≤ 2 / β)]
    congr 1
    field_simp
    ring_nf
  rw [← he, hermiteBetaEnsemble_def, hpdf, e.measurableEmbedding.map_withDensity_comp,
    hvol.map_eq, gaussianReal_of_var_ne_zero 0 hv]

end TauCeti.Probability
