/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.QuadraticForm
public import TauCeti.Probability.Distributions.Wishart.Basic
public import TauCeti.Probability.Distributions.Wishart.Nonsingular

import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Divergence
import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral
import TauCeti.LinearAlgebra.Matrix.InvSub
import TauCeti.Probability.Moments.Pi

/-!
# Exponential moments of the Wishart families

A symmetric matrix `Θ` pairs with a Wishart matrix `A` through the real trace statistic
`A ↦ trace (Θ * A)`; by `selfAdjoint.inner_eq_trace_mul` this is the Frobenius inner product of
the symmetric subspace, so it is the pairing that `MeasureTheory.charFun` uses there. This file
determines exactly when that statistic has finite exponential moments under each of the two
Wishart families, and computes its moment- and cumulant-generating functions. Both answers are
governed by one matrix, the pencil `1 - (2 * t) • (√S * Θ * √S)`: at a positive Gaussian-Gram
degree, and for the density family at a positive-definite scale and a degree in the classical
range `p - 1 < n`, the moment is finite exactly when that pencil is positive definite, and there
the transform is a negative half-power of its determinant, with the degree as exponent.
Gaussian-Gram degree zero is the one exception, where the law is a Dirac mass and every order has
a finite moment whether or not the pencil is positive definite.

For the Gaussian-Gram family, writing the law as the image of a product of `ν` centred Gaussian
factors turns the trace statistic into a sum of `ν` independent Gaussian quadratic forms, which
reduces all three answers to the one-factor answers of
`TauCeti.Probability.Distributions.Gaussian.QuadraticForm`. The factors being identically
distributed, the domain of the sum is their common domain; the moment-generating function is the
`ν`-th power of the one-factor one; and the cumulant-generating function is `ν` times the
one-factor one. At degree zero the law is a Dirac mass and the statistic vanishes identically, so
the domain is all of `ℝ` and the transforms are constant; those statements need no hypothesis and
are recorded separately.

For the nonsingular density family the computation is the multivariate Gamma integral instead.
Tilting the density by `exp (t * trace (Θ * A))` replaces the inverse scale `S⁻¹` in its
exponential weight by `S⁻¹ - (2 * t) • Θ`, which is the congruence of the pencil by
`(CFC.sqrt S)⁻¹` and so positive definite exactly when the pencil is. Where it is, the tilted
density is again a Wishart density, at the scale `(S⁻¹ - (2 * t) • Θ)⁻¹`, and the ratio of the
two normalizing constants is the determinant power; where it is not, the cone integral diverges.

## Main results

* `TauCeti.Probability.mem_integrableExpSet_trace_mul_wishartGramMeasure_iff` — at a positive
  degree, the
  exact exponential-integrability domain of the trace statistic;
* `TauCeti.Probability.mgf_trace_mul_wishartGramMeasure_sqrt` and
  `TauCeti.Probability.mgf_trace_mul_wishartGramMeasure` — its moment-generating function on that
  domain, in
  terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of `Θ * S`;
* `TauCeti.Probability.cgf_trace_mul_wishartGramMeasure_sqrt` and
  `TauCeti.Probability.cgf_trace_mul_wishartGramMeasure` — the matching cumulant-generating
  functions;
* `TauCeti.Probability.integral_exp_neg_trace_mul_wishartGramMeasure` — the Laplace transform over
  the
  positive-semidefinite cone, the specialization of the moment-generating function to `t = -1`;
* `TauCeti.Probability.mem_integrableExpSet_trace_mul_nonsingularWishartMeasure_iff`,
  `TauCeti.Probability.mgf_trace_mul_nonsingularWishartMeasure` with its sandwich form
  `TauCeti.Probability.mgf_trace_mul_nonsingularWishartMeasure_sqrt`,
  `TauCeti.Probability.cgf_trace_mul_nonsingularWishartMeasure` and
  `TauCeti.Probability.integral_exp_neg_trace_mul_nonsingularWishartMeasure` — the same four results
  for the
  nonsingular density family, with its real degree in place of the natural one.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti.Probability

variable {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
  {Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} {t : ℝ}

/-! ### Degree zero -/

/-- At degree zero the Gaussian-Gram law is a Dirac mass at the origin, so the trace statistic has
finite exponential moments of every order. -/
theorem integrableExpSet_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ) :
    integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) = Set.univ := by
  refine Set.eq_univ_of_forall fun t ↦ ?_
  rw [integrableExpSet, Set.mem_ofPred_eq, wishartGramMeasure_zero]
  exact integrable_dirac' (selfAdjoint.continuous_exp_trace_mul_coe Θ t).stronglyMeasurable
    enorm_lt_top

/-- At degree zero the trace statistic vanishes almost everywhere, so its moment-generating
function is constantly `1`. -/
theorem mgf_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) t = 1 := by
  rw [mgf, wishartGramMeasure_zero,
    integral_dirac' _ _ (selfAdjoint.continuous_exp_trace_mul_coe Θ t).stronglyMeasurable]
  simp

/-- At degree zero the cumulant-generating function is constantly `0`. -/
theorem cgf_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) t = 0 := by
  rw [cgf, mgf_trace_mul_wishartGramMeasure_zero, Real.log_one]

/-! ### The exponential-integrability domain -/

/-- **The exponential-integrability domain of a Wishart trace statistic.** At a positive degree
the exponential moment of order `t` of `A ↦ trace (Θ * A)` under the Gaussian-Gram law is finite
exactly when the pencil `1 - (2 * t) • (√S * Θ * √S)` of a single Gaussian factor is positive
definite: the statistic is a sum of `ν` independent copies of that factor's quadratic form, so
the domain of the sum is their common domain.

No hypothesis on the scale matrix `S` is needed. Where `S` is not positive semidefinite it is not
the covariance of the Gaussian factors: Mathlib totalizes them to Dirac masses, `CFC.sqrt S` is
zero, and the pencil is the identity. -/
theorem mem_integrableExpSet_trace_mul_wishartGramMeasure_iff (hν : 0 < ν)
    (S : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    t ∈ integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) ↔
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef := by
  have hne : Nonempty (Fin ν) := ⟨⟨0, hν⟩⟩
  have hfactor := integrableExpSet_sum_pi
    (μ := fun _ : Fin ν ↦ multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)
    fun _ : Fin ν ↦ fun x : EuclideanSpace ℝ (Fin p) ↦
      ⟪x, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin x⟫
  have htransport : t ∈ integrableExpSet
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
        (wishartGramMeasure ν S) ↔
      t ∈ integrableExpSet
        (fun X : Fin ν → EuclideanSpace ℝ (Fin p) ↦
          ∑ r, ⟪X r, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin (X r)⟫)
        (Measure.pi fun _ : Fin ν ↦ multivariateGaussian 0 S) := by
    rw [wishartGramMeasure_eq_map_pi]
    simp only [integrableExpSet, Set.mem_ofPred_eq]
    rw [integrable_map_measure (selfAdjoint.continuous_exp_trace_mul_coe Θ t).aestronglyMeasurable
      measurable_wishartGram.aemeasurable, Function.comp_def]
    simp only [trace_mul_coe_wishartGram]
  rw [htransport, hfactor, Set.mem_iInter,
    ← mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff S
      (selfAdjoint.isHermitian_coe Θ) t]
  exact ⟨fun h ↦ h (Classical.arbitrary _), fun h _ ↦ h⟩

/-! ### The moment- and cumulant-generating functions -/

/-- **The moment-generating function of a Wishart trace statistic.** On its
exponential-integrability domain it is the `-ν / 2` power of the determinant of the pencil
`1 - (2 * t) • (√S * Θ * √S)`, for every degree and every scale matrix. -/
theorem mgf_trace_mul_wishartGramMeasure_sqrt (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
        ^ (-(ν : ℝ) / 2 : ℝ) := by
  have hexponent : (-(ν : ℝ) / 2 : ℝ) = -1 / 2 * (ν : ℝ) := by ring
  rw [wishartGramMeasure_eq_map_pi, mgf_map measurable_wishartGram.aemeasurable
      (selfAdjoint.continuous_exp_trace_mul_coe Θ t).aestronglyMeasurable, Function.comp_def]
  simp only [trace_mul_coe_wishartGram]
  rw [mgf_sum_pi (fun _ : Fin ν ↦ fun x : EuclideanSpace ℝ (Fin p) ↦
      ⟪x, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin x⟫) t,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mgf_inner_toEuclideanLin_multivariateGaussian_sqrt S (selfAdjoint.isHermitian_coe Θ) ht,
    hexponent, Real.rpow_mul ht.det_pos.le, Real.rpow_natCast]

/-- **The cumulant-generating function of a Wishart trace statistic**, the real logarithm of the
moment-generating function on the same domain. -/
theorem cgf_trace_mul_wishartGramMeasure_sqrt (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      -(ν : ℝ) / 2 *
        Real.log
          (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det := by
  rw [cgf, mgf_trace_mul_wishartGramMeasure_sqrt ν S ht, Real.log_rpow ht.det_pos]

/-- For a positive-semidefinite scale matrix the pencil of the sandwich may be replaced by the
pencil of the product `Θ * S`, which is the classical form of the Wishart moment-generating
function. -/
theorem mgf_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det ^ (-(ν : ℝ) / 2 : ℝ) := by
  rw [mgf_trace_mul_wishartGramMeasure_sqrt ν S ht,
    hS.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul _ (2 * t)]

/-- For a positive-semidefinite scale matrix the cumulant-generating function is `-ν / 2` times
the real logarithm of the determinant of the pencil of `Θ * S`. -/
theorem cgf_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      -(ν : ℝ) / 2 * Real.log (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det := by
  rw [cgf_trace_mul_wishartGramMeasure_sqrt ν S ht,
    hS.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul _ (2 * t)]

/-! ### The Laplace transform on the positive-semidefinite cone -/

/-- **The Laplace transform of the Gaussian-Gram Wishart law over the positive-semidefinite
cone**, the specialization of the moment-generating function to `t = -1`. For a
positive-semidefinite `Θ` the exponent `-trace (Θ * A)` is nonpositive on the support of the law,
so the integral is finite at every degree and every positive-semidefinite scale. -/
theorem integral_exp_neg_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (hΘ : (Θ : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        Real.exp (-((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      ∂wishartGramMeasure ν S =
      (1 + (2 : ℝ) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det ^ (-(ν : ℝ) / 2 : ℝ) := by
  have hsqrt : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).isHermitian.eq
  have hB : (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S).PosSemidef := by
    simpa only [hsqrt] using hΘ.conjTranspose_mul_mul_same (CFC.sqrt S)
  have ht : (1 - (2 * (-1 : ℝ)) •
      (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef := by
    rw [hB.1.posDef_one_sub_smul_iff]
    exact fun j ↦ by nlinarith [hB.eigenvalues_nonneg j]
  have hpencil : (1 : Matrix (Fin p) (Fin p) ℝ) -
      (2 * (-1 : ℝ)) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S) =
      1 + (2 : ℝ) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S) := by
    have hcoeff : (2 * (-1 : ℝ)) = -2 := by norm_num
    rw [hcoeff, neg_smul, sub_neg_eq_add]
  rw [← hpencil, ← mgf_trace_mul_wishartGramMeasure ν hS ht, mgf]
  exact integral_congr_ae (Filter.Eventually.of_forall fun A ↦ by simp only [neg_one_mul])

/-! ### The nonsingular density family -/

variable {n : ℝ}

/-- Tilting the Wishart density by `exp (t * trace (Θ * A))` replaces the inverse scale `S⁻¹` in
its exponential weight by the pencil `S⁻¹ - (2 * t) • Θ`, leaving the determinant factor and the
normalizing constant untouched. -/
private theorem nonsingularWishartPDFReal_mul_exp_trace_mul (n t : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        nonsingularWishartPDFReal n S A *
          Real.exp (t * ((Θ : Matrix (Fin p) (Fin p) ℝ) *
            (A : Matrix (Fin p) (Fin p) ℝ)).trace)) =
      Set.indicator {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}
        fun A ↦ ((2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) *
            multivariateGamma p (n / 2))⁻¹ *
          ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (n / 2 - ((p : ℝ) + 1) / 2) *
            Real.exp (-((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)) *
              (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2)) := by
  funext A
  by_cases hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef
  · have hsplit : -((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)) *
        (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2 =
        -(S⁻¹ * (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2 +
          t * ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace := by
      rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      ring
    have hcone : (n - (p : ℝ) - 1) / 2 = n / 2 - ((p : ℝ) + 1) / 2 := by ring
    rw [Set.indicator_of_mem (s := {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}) hA,
      nonsingularWishartPDFReal_of_posDef n S hA, hsplit, Real.exp_add, hcone]
    ring
  · rw [Set.indicator_of_notMem (s := {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}) hA,
      nonsingularWishartPDFReal_of_not_posDef n S hA, zero_mul]

/-- The tilted Wishart integrand is the cone integrand of the multivariate Gamma integral with
the scale matrix `(S⁻¹ - (2 * t) • Θ)⁻¹`, so on the positive-definite pencil its integral is that
scale's determinant power. -/
private theorem integral_posDef_det_rpow_mul_exp_neg_trace_pencil (hn : (p : ℝ) - 1 < n)
    (hB : (S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)).PosDef) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (A : Matrix (Fin p) (Fin p) ℝ).det ^ (n / 2 - ((p : ℝ) + 1) / 2) *
        Real.exp (-((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)) *
          (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2) ∂symmetricLebesgue p =
      (2 : ℝ) ^ ((p : ℝ) * (n / 2)) *
        ((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ))⁻¹).det ^ (n / 2) *
        multivariateGamma p (n / 2) := by
  have key := hB.inv.integral_det_rpow_mul_exp_neg_trace_inv_mul_div_two (n / 2)
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hB.det_pos.ne'),
    integral_posDef_multivariateGamma (by linarith)] at key
  exact key

/-- The exponential moment of the trace statistic under the Wishart law is the integral of the
tilted cone integrand against `TauCeti.symmetricLebesgue`, up to the Wishart constant. -/
private theorem integrable_exp_trace_mul_nonsingularWishartMeasure_iff_integrableOn
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) (t : ℝ) :
    Integrable (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        Real.exp (t * ((Θ : Matrix (Fin p) (Fin p) ℝ) *
          (A : Matrix (Fin p) (Fin p) ℝ)).trace)) (nonsingularWishartMeasure n S) ↔
      IntegrableOn (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (A : Matrix (Fin p) (Fin p) ℝ).det ^ (n / 2 - ((p : ℝ) + 1) / 2) *
            Real.exp (-((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)) *
              (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2))
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef} (symmetricLebesgue p) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) *
      multivariateGamma p (n / 2) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos hS.det_pos _))
      (multivariateGamma_pos (by linarith))
  have hconst : IsUnit (((2 : ℝ) ^ (n * (p : ℝ) / 2) * S.det ^ (n / 2) *
      multivariateGamma p (n / 2))⁻¹) := isUnit_iff_ne_zero.2 (inv_ne_zero hpos.ne')
  rw [nonsingularWishartMeasure_of_posDef hS hn,
    integrable_withDensity_iff_integrable_smul' (measurable_nonsingularWishartPDF n S)
      (Filter.Eventually.of_forall fun A ↦ (nonsingularWishartPDF_ne_top n S A).lt_top)]
  simp only [smul_eq_mul, toReal_nonsingularWishartPDF hS hn]
  rw [nonsingularWishartPDFReal_mul_exp_trace_mul n t S Θ,
    integrable_indicator_iff (measurableSet_posDefMatrix p)]
  exact integrable_const_mul_iff hconst _

/-! #### The exponential-integrability domain -/

/-- **The exponential-integrability domain of a nonsingular Wishart trace statistic.** At a
positive-definite scale and a degree in the classical range, the exponential moment of order `t`
of `A ↦ trace (Θ * A)` under the density family is finite exactly when the pencil
`1 - (2 * t) • (√S * Θ * √S)` is positive definite, the same condition as for the Gaussian-Gram
family.

Tilting the density by `exp (t * trace (Θ * A))` turns its exponential weight into
`exp (-trace ((S⁻¹ - (2 * t) • Θ) * A) / 2)`, and the cone integral of such a weight converges
exactly when its matrix is positive definite; that matrix is the congruence of the pencil by
`(CFC.sqrt S)⁻¹`. -/
theorem mem_integrableExpSet_trace_mul_nonsingularWishartMeasure_iff (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (t : ℝ) :
    t ∈ integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (nonsingularWishartMeasure n S) ↔
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef := by
  rw [integrableExpSet, Set.mem_ofPred_eq,
    integrable_exp_trace_mul_nonsingularWishartMeasure_iff_integrableOn hS hn t,
    ← hS.posDef_inv_sub_smul_iff (Θ : Matrix (Fin p) (Fin p) ℝ) (2 * t)]
  -- The halved weight of the Wishart density is the plain weight of the halved pencil.
  have hhalf : ∀ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      -(((2 : ℝ)⁻¹ • (S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ))) *
          (A : Matrix (Fin p) (Fin p) ℝ)).trace =
        -((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)) *
          (A : Matrix (Fin p) (Fin p) ℝ)).trace / 2 := fun A ↦ by
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  refine ⟨fun hint ↦ ?_, fun hB ↦ ?_⟩
  · -- Off the positive-definite pencil the cone integral diverges.
    by_contra hB
    have hherm : (((2 : ℝ)⁻¹ • (S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)))).IsHermitian :=
      ((hS.inv.isHermitian.sub ((selfAdjoint.isHermitian_coe Θ).smul
        (IsSelfAdjoint.all (2 * t : ℝ)))).smul (IsSelfAdjoint.all ((2 : ℝ)⁻¹)))
    refine not_integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul (a := n / 2) hherm
      (fun hhalfpd ↦ hB ?_) (by linarith) ?_
    · have hdouble := hhalfpd.smul (by norm_num : (0 : ℝ) < 2)
      rwa [smul_smul, mul_inv_cancel₀ (two_ne_zero' ℝ), one_smul] at hdouble
    · simpa only [hhalf] using hint
  · have hint := Matrix.PosDef.integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul
      (hB.smul (by norm_num : (0 : ℝ) < 2⁻¹)) (a := n / 2) (by linarith)
    simpa only [hhalf] using hint

/-! #### The moment- and cumulant-generating functions -/

/-- **The moment-generating function of a nonsingular Wishart trace statistic.** On its
exponential-integrability domain it is the `-n / 2` power of the determinant of the pencil
`1 - (2 * t) • (Θ * S)`.

The tilted density integrates to the multivariate Gamma integral at the scale
`(S⁻¹ - (2 * t) • Θ)⁻¹`, whose determinant power is exactly the Wishart constant divided by that
pencil determinant. -/
theorem mgf_trace_mul_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (nonsingularWishartMeasure n S) t =
      (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det ^ (-n / 2 : ℝ) := by
  have hB : (S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)).PosDef :=
    (hS.posDef_inv_sub_smul_iff _ _).2 ht
  have hpencil : (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det =
      S.det * (S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)).det :=
    (Matrix.det_mul_det_inv_sub_smul (isUnit_iff_ne_zero.2 hS.det_pos.ne') _ _).symm
  have hneg : (-n / 2 : ℝ) = -(n / 2) := by ring
  have htwo : (2 : ℝ) ^ ((p : ℝ) * (n / 2)) = 2 ^ (n * (p : ℝ) / 2) := by
    congr 1
    ring
  rw [mgf, nonsingularWishartMeasure_of_posDef hS hn,
    integral_withDensity_eq_integral_toReal_smul (measurable_nonsingularWishartPDF n S)
      (Filter.Eventually.of_forall fun A ↦ (nonsingularWishartPDF_ne_top n S A).lt_top)]
  simp only [smul_eq_mul, toReal_nonsingularWishartPDF hS hn]
  rw [nonsingularWishartPDFReal_mul_exp_trace_mul n t S Θ,
    integral_indicator (measurableSet_posDefMatrix p), integral_const_mul,
    integral_posDef_det_rpow_mul_exp_neg_trace_pencil hn hB, hpencil, hneg,
    Real.rpow_neg (mul_pos hS.det_pos hB.det_pos).le,
    Real.mul_rpow hS.det_pos.le hB.det_pos.le,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.inv_rpow hB.det_pos.le, htwo]
  have h2 : ((2 : ℝ) ^ (n * (p : ℝ) / 2)) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  have hs : (S.det ^ (n / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hS.det_pos _).ne'
  have hb : ((S⁻¹ - (2 * t) • (Θ : Matrix (Fin p) (Fin p) ℝ)).det ^ (n / 2) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hB.det_pos _).ne'
  have hg : multivariateGamma p (n / 2) ≠ 0 := multivariateGamma_ne_zero (by linarith)
  field_simp

/-- The moment-generating function in terms of the Hermitian sandwich `√S * Θ * √S`, the form
that the spectral characteristic function continues. -/
theorem mgf_trace_mul_nonsingularWishartMeasure_sqrt (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (nonsingularWishartMeasure n S) t =
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
        ^ (-n / 2 : ℝ) := by
  rw [hS.posSemidef.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul _ (2 * t),
    mgf_trace_mul_nonsingularWishartMeasure hS hn ht]

/-- **The cumulant-generating function of a nonsingular Wishart trace statistic**, the real
logarithm of the moment-generating function on the same domain. -/
theorem cgf_trace_mul_nonsingularWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (nonsingularWishartMeasure n S) t =
      -n / 2 * Real.log (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det := by
  have hdet : (0 : ℝ) < (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det := by
    rw [← hS.posSemidef.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul _ (2 * t)]
    exact ht.det_pos
  rw [cgf, mgf_trace_mul_nonsingularWishartMeasure hS hn ht, Real.log_rpow hdet]

/-! #### The Laplace transform on the positive-semidefinite cone -/

/-- **The Laplace transform of the nonsingular Wishart law over the positive-semidefinite cone**,
the specialization of the moment-generating function to `t = -1`. For a positive-semidefinite `Θ`
the exponent `-trace (Θ * A)` is nonpositive on the support of the law, so no further condition
on `Θ` is needed. -/
theorem integral_exp_neg_trace_mul_nonsingularWishartMeasure (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (hΘ : (Θ : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        Real.exp (-((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      ∂nonsingularWishartMeasure n S =
      (1 + (2 : ℝ) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det ^ (-n / 2 : ℝ) := by
  have hcoeff : (2 * (-1 : ℝ)) = -2 := by norm_num
  have hB : (S⁻¹ - (2 * (-1 : ℝ)) • (Θ : Matrix (Fin p) (Fin p) ℝ)).PosDef := by
    rw [hcoeff, neg_smul, sub_neg_eq_add]
    exact hS.inv.add_posSemidef (hΘ.smul (by norm_num))
  have ht := (hS.posDef_inv_sub_smul_iff (Θ : Matrix (Fin p) (Fin p) ℝ) (2 * (-1 : ℝ))).1 hB
  have hpencil : (1 : Matrix (Fin p) (Fin p) ℝ) -
      (2 * (-1 : ℝ)) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S) =
      1 + (2 : ℝ) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S) := by
    rw [hcoeff, neg_smul, sub_neg_eq_add]
  rw [← hpencil, ← mgf_trace_mul_nonsingularWishartMeasure hS hn ht, mgf]
  exact integral_congr_ae (Filter.Eventually.of_forall fun A ↦ by simp only [neg_one_mul])

end TauCeti.Probability
