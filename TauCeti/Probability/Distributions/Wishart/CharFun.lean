/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Transforms
public import TauCeti.Probability.Moments.ComplexMGF

/-!
# The characteristic function of the Gaussian-Gram Wishart law

The Frobenius pairing of the symmetric subspace is the trace pairing
(`selfAdjoint.inner_eq_trace_mul`), so the characteristic function of a symmetric-matrix law at a
symmetric `Θ` is the transform of the real trace statistic `A ↦ trace (Θ * A)`. Under the
Gaussian-Gram Wishart law of degree `ν` and scale `S` that statistic has, on its
exponential-integrability domain, the moment-generating function
`det (1 - (2 * t) • (√S * Θ * √S)) ^ (-ν / 2)`; writing the sandwich `B = √S * Θ * √S` through its
spectrum turns this into the product `∏ j, (1 - 2 * t * λ j) ^ (-ν / 2)` over the eigenvalues of
`B`, and analytic continuation of that product to the imaginary axis gives the characteristic
function.

The answer is stated as the exponential of a sum of principal logarithms, one for each eigenvalue,
rather than as a principal complex power of a determinant: collecting the factors before taking a
logarithm can cross the branch cut, and the two expressions then differ. The sandwich `B` is
Hermitian for every scale matrix (`Matrix.isHermitian_sqrt_mul_mul_sqrt`), so the formula needs no
hypothesis on `S`: at a scale that is not positive semidefinite the law is the Dirac mass at the
origin that Mathlib's totalization of the Gaussian factors produces, and the formula returns `1`
there.

## Main results

* `TauCeti.charFun_wishartGramMeasure` — the characteristic function of the Gaussian-Gram Wishart
  law, as an eigenvalue-wise principal-logarithm formula.

## References

* E. Mayerhofer, *Reforming the Wishart characteristic function*,
  [arXiv:1901.09347](https://arxiv.org/abs/1901.09347), for the branch ambiguity that forces the
  sum-of-logarithms form.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
-/

public section

noncomputable section

open Complex MeasureTheory ProbabilityTheory

open scoped Matrix MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {p : ℕ}

/-- The moment-generating function of the Wishart trace statistic, written through the spectrum
of the sandwich `√S * Θ * √S` as a product of real powers of the pencil `1 - 2 * t * λ j`.  This
is the shape that `TauCeti.complexMGF_I_eq_exp_of_mgf_eq_prod_rpow` continues to the imaginary
axis. -/
private theorem mgf_trace_mul_wishartGramMeasure_eq_prod_rpow (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) {t : ℝ}
    (ht : ∀ j, 0 < 1 - 2 * t *
      (Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)).eigenvalues j) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      ∏ j, (1 - 2 * t *
          (Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)).eigenvalues j)
        ^ (-((ν : ℝ) / 2)) := by
  set hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have hpencil :
      (1 - (2 * t) • (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S)).PosDef :=
    (hB.posDef_one_sub_smul_iff (2 * t)).2 fun j => by
      linarith [ht j, mul_assoc 2 t (hB.eigenvalues j)]
  have hdet := hB.det_one_sub_smul (2 * t)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
  rw [mgf_trace_mul_wishartGramMeasure_sqrt ν S hpencil, hdet, neg_div,
    ← Real.finsetProd_rpow _ _ (fun j _ => by linarith [ht j]) _]

/-- **The characteristic function of the Gaussian-Gram Wishart law.** For a symmetric matrix `Θ`
it is the exponential of `-ν / 2` times the sum of the principal logarithms of `1 - 2 * I * λ j`,
one for each eigenvalue `λ j` of the Hermitian sandwich `√S * Θ * √S`.

The formula holds for every degree and every scale matrix: at a scale that is not positive
semidefinite the law is a Dirac mass at the origin and both sides are `1`. -/
theorem charFun_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    charFun (wishartGramMeasure ν S) Θ =
      cexp (-(ν : ℂ) / 2 * ∑ j, Complex.log (1 - 2 * Complex.I *
        ((Matrix.isHermitian_sqrt_mul_mul_sqrt S
          (selfAdjoint.isHermitian_coe Θ)).eigenvalues j : ℂ))) := by
  set hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have hstat : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => ⟪A, Θ⟫) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace :=
    funext fun A => selfAdjoint.inner_eq_trace_mul A Θ
  rw [charFun_eq_complexMGF_inner, hstat,
    complexMGF_I_eq_exp_of_mgf_eq_prod_rpow hB.eigenvalues (fun _ => (ν : ℝ) / 2)
      fun t ht => mgf_trace_mul_wishartGramMeasure_eq_prod_rpow ν S Θ ht]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

end TauCeti
