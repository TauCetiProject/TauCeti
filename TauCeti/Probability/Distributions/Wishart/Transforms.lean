/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.QuadraticForm
public import TauCeti.Probability.Distributions.Wishart.Basic

import TauCeti.Probability.Moments.Pi

/-!
# Exponential moments of the Gaussian-Gram Wishart family

A symmetric matrix `Θ` pairs with a Wishart matrix `A` through the real trace statistic
`A ↦ trace (Θ * A)`; by `selfAdjoint.inner_eq_trace_mul` this is the Frobenius inner product of
the symmetric subspace, so it is the pairing that `MeasureTheory.charFun` uses there. This file
determines exactly when that statistic has finite exponential moments under
`TauCeti.wishartGramMeasure`, and computes its moment- and cumulant-generating functions.

Writing the Gaussian-Gram law as the image of a product of `ν` centred Gaussian factors turns the
trace statistic into a sum of `ν` independent Gaussian quadratic forms, so both answers are the
`ν`-th powers of the one-factor answers of
`TauCeti.Probability.Distributions.Gaussian.QuadraticForm`: the domain is the positive
definiteness of the single pencil `1 - (2 * t) • (√S * Θ * √S)`, and the moment-generating
function is the `-ν / 2` power of its determinant.

At degree zero the law is a Dirac mass and the statistic vanishes identically, so the domain is
all of `ℝ` and the transforms are constant; those statements need no hypothesis and are recorded
separately.

## Main results

* `TauCeti.trace_mul_coe_wishartGram` — the trace statistic of a Gram sum is the sum of the
  Gaussian quadratic forms of its vectors;
* `TauCeti.mem_integrableExpSet_trace_mul_wishartGramMeasure_iff` — at a positive degree, the
  exact exponential-integrability domain of the trace statistic;
* `TauCeti.mgf_trace_mul_wishartGramMeasure_sqrt` and
  `TauCeti.mgf_trace_mul_wishartGramMeasure` — its moment-generating function on that domain, in
  terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of `Θ * S`;
* `TauCeti.cgf_trace_mul_wishartGramMeasure_sqrt` and
  `TauCeti.cgf_trace_mul_wishartGramMeasure` — the matching cumulant-generating functions;
* `TauCeti.integral_exp_neg_trace_mul_wishartGramMeasure` — the Laplace transform over the
  positive-semidefinite cone, the specialization of the moment-generating function to `t = -1`.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti

variable {ι : Type*} [Fintype ι] {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
  {Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} {t : ℝ}

/-! ### The trace statistic -/

/-- The trace statistic of a Gram sum is the sum of the quadratic forms of `Θ` at the vectors.
This is what turns a Wishart trace statistic into a sum of Gaussian quadratic forms, one per
sampled vector. No symmetry of `Θ` is needed. -/
theorem trace_mul_coe_wishartGram (Θ : Matrix (Fin p) (Fin p) ℝ)
    (X : ι → EuclideanSpace ℝ (Fin p)) :
    (Θ * (wishartGram X : Matrix (Fin p) (Fin p) ℝ)).trace =
      ∑ r, ⟪X r, Θ.toEuclideanLin (X r)⟫ := by
  rw [coe_wishartGram, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  simp [PiLp.inner_apply, Matrix.toLin'_apply, dotProduct]

/-- The exponential of the trace statistic is continuous, hence strongly measurable; this is the
side condition of every transform computation below. -/
private theorem continuous_exp_trace_mul_coe
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (t : ℝ) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      Real.exp (t * ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) :=
  (continuous_const.mul (selfAdjoint.continuous_trace_mul_coe Θ)).rexp

/-- Transported to the Gaussian factors, the trace statistic of the Gaussian-Gram law is the sum
of the quadratic forms of `Θ` along the `ν` coordinates. -/
private theorem trace_mul_coe_comp_wishartGram
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ((fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) ∘
      wishartGram (p := p) (ι := ι)) =
      fun X => ∑ r, ⟪X r, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin (X r)⟫ :=
  funext fun X => trace_mul_coe_wishartGram _ X

/-! ### Degree zero -/

/-- At degree zero the Gaussian-Gram law is a Dirac mass at the origin, so the trace statistic has
finite exponential moments of every order. -/
theorem integrableExpSet_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ) :
    integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) = Set.univ := by
  refine Set.eq_univ_of_forall fun t => ?_
  rw [integrableExpSet, Set.mem_ofPred_eq, wishartGramMeasure_zero]
  exact integrable_dirac' (continuous_exp_trace_mul_coe Θ t).stronglyMeasurable enorm_lt_top

/-- At degree zero the trace statistic vanishes almost everywhere, so its moment-generating
function is constantly `1`. -/
theorem mgf_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) t = 1 := by
  rw [mgf, wishartGramMeasure_zero,
    integral_dirac' _ _ (continuous_exp_trace_mul_coe Θ t).stronglyMeasurable]
  simp

/-- At degree zero the cumulant-generating function is constantly `0`. -/
theorem cgf_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
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
    t ∈ integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) ↔
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef := by
  have hne : Nonempty (Fin ν) := ⟨⟨0, hν⟩⟩
  have hfactor := integrableExpSet_sum_pi
    (μ := fun _ : Fin ν => multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)
    fun _ : Fin ν => fun x : EuclideanSpace ℝ (Fin p) =>
      ⟪x, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin x⟫
  have htransport : t ∈ integrableExpSet
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
        (wishartGramMeasure ν S) ↔
      t ∈ integrableExpSet
        (fun X : Fin ν → EuclideanSpace ℝ (Fin p) =>
          ∑ r, ⟪X r, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin (X r)⟫)
        (Measure.pi fun _ : Fin ν => multivariateGaussian 0 S) := by
    rw [wishartGramMeasure_eq_map_pi]
    simp only [integrableExpSet, Set.mem_ofPred_eq]
    rw [integrable_map_measure (continuous_exp_trace_mul_coe Θ t).aestronglyMeasurable
      measurable_wishartGram.aemeasurable, Function.comp_def]
    simp only [trace_mul_coe_wishartGram]
  rw [htransport, hfactor, Set.mem_iInter,
    ← mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff S
      (selfAdjoint.isHermitian_coe Θ) t]
  exact ⟨fun h => h (Classical.arbitrary _), fun h _ => h⟩

/-! ### The moment- and cumulant-generating functions -/

/-- **The moment-generating function of a Wishart trace statistic.** On its
exponential-integrability domain it is the `-ν / 2` power of the determinant of the pencil
`1 - (2 * t) • (√S * Θ * √S)`, for every degree and every scale matrix. -/
theorem mgf_trace_mul_wishartGramMeasure_sqrt (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).det
        ^ (-(ν : ℝ) / 2 : ℝ) := by
  rw [wishartGramMeasure_eq_map_pi, mgf_map measurable_wishartGram.aemeasurable
      (continuous_exp_trace_mul_coe Θ t).aestronglyMeasurable,
    trace_mul_coe_comp_wishartGram,
    mgf_sum_pi (fun _ : Fin ν => fun x : EuclideanSpace ℝ (Fin p) =>
      ⟪x, (Θ : Matrix (Fin p) (Fin p) ℝ).toEuclideanLin x⟫) t,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mgf_inner_toEuclideanLin_multivariateGaussian_sqrt S (selfAdjoint.isHermitian_coe Θ) ht,
    show (-(ν : ℝ) / 2 : ℝ) = -1 / 2 * (ν : ℝ) by ring,
    Real.rpow_mul ht.det_pos.le, Real.rpow_natCast]

/-- **The cumulant-generating function of a Wishart trace statistic**, the real logarithm of the
moment-generating function on the same domain. -/
theorem cgf_trace_mul_wishartGramMeasure_sqrt (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
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
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      (1 - (2 * t) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S)).det ^ (-(ν : ℝ) / 2 : ℝ) := by
  rw [mgf_trace_mul_wishartGramMeasure_sqrt ν S ht,
    hS.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul _ (2 * t)]

/-- For a positive-semidefinite scale matrix the cumulant-generating function is `-ν / 2` times
the real logarithm of the determinant of the pencil of `Θ * S`. -/
theorem cgf_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (ht : (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
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
    exact fun j => by nlinarith [hB.eigenvalues_nonneg j]
  have hpencil : (1 : Matrix (Fin p) (Fin p) ℝ) -
      (2 * (-1 : ℝ)) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S) =
      1 + (2 : ℝ) • ((Θ : Matrix (Fin p) (Fin p) ℝ) * S) := by
    rw [show (2 * (-1 : ℝ)) = -2 by norm_num, neg_smul, sub_neg_eq_add]
  rw [← hpencil, ← mgf_trace_mul_wishartGramMeasure ν hS ht, mgf]
  exact integral_congr_ae (Filter.Eventually.of_forall fun A => by simp only [neg_one_mul])

end TauCeti
