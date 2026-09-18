/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Transforms
public import TauCeti.Probability.Moments.ComplexMGF

import Mathlib.MeasureTheory.Group.Convolution
import TauCeti.Probability.Distributions.Wishart.Congruence

/-!
# The characteristic functions of the Wishart families

A symmetric matrix `Θ` pairs with a symmetric matrix `A` through the trace statistic
`A ↦ trace (Θ * A)`, which by `selfAdjoint.inner_eq_trace_mul` is the Frobenius inner product of
the symmetric subspace. So `MeasureTheory.charFun` of a law on that subspace, evaluated at `Θ`,
is the value at `Complex.I` of `ProbabilityTheory.complexMGF` of the trace statistic, and a
closed form for the moment-generating function of that statistic determines the characteristic
function by analytic continuation.

The moment-generating function of the Wishart trace statistic is a real power of the determinant
of the pencil `1 - (2 * t) • B`, where `B` is the Hermitian sandwich `√S * Θ * √S`. Diagonalizing
`B` turns that determinant into the product `∏ j, (1 - 2 * t * λ j)` over the eigenvalues of `B`,
which is the shape that `TauCeti.complexMGF_I_eq_exp_of_mgf_eq_prod_rpow` continues. The answer
is therefore an exponential of a *sum* of principal logarithms, one per eigenvalue, and not a
principal complex power of the determinant: collecting the factors before taking the logarithm
can cross the branch cut.

## Main results

* `selfAdjoint.charFun_eq_complexMGF_trace_mul` — on the symmetric subspace, the characteristic
  function at `Θ` is the complex moment-generating function of the trace statistic at
  `Complex.I`.
* `TauCeti.charFun_eq_exp_of_mgf_trace_mul_eq_det_rpow` — the spectral characteristic function of
  any law on the symmetric subspace whose trace moment-generating function is a real power of a
  Hermitian pencil determinant.
* `TauCeti.charFun_wishartGramMeasure` — the characteristic function of the Gaussian-Gram Wishart
  law, at every degree and every scale matrix.
* `TauCeti.charFun_nonsingularWishartMeasure` — the characteristic function of the nonsingular
  density family, the same formula with the real degree in place of the natural one.
* `TauCeti.nonsingularWishartMeasure_conv_nonsingularWishartMeasure` — at a fixed scale the
  degrees of the nonsingular family add under convolution, since the exponent is linear in the
  degree.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
* E. Mayerhofer, *Reforming the Wishart characteristic function*,
  [arXiv:1901.09347](https://arxiv.org/abs/1901.09347), for the branch analysis that forces the
  sum-of-logarithms form.
-/

public section

noncomputable section

open Complex MeasureTheory ProbabilityTheory

namespace selfAdjoint

/-- On the symmetric subspace the Frobenius pairing with `Θ` is the trace statistic
`A ↦ trace (Θ * A)`, so the characteristic function of a law there, evaluated at `Θ`, is the
value of the complex moment-generating function of that statistic at `Complex.I`. -/
theorem charFun_eq_complexMGF_trace_mul {p : ℕ}
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) :
    charFun μ Θ =
      complexMGF (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ Complex.I := by
  simp only [MeasureTheory.charFun_eq_complexMGF_inner, inner_eq_trace_mul]

end selfAdjoint

namespace TauCeti

variable {p : ℕ}

/-- **The spectral characteristic function of a symmetric-matrix law with a determinant-power
trace transform.** If the moment-generating function of the trace statistic `A ↦ trace (Θ * A)`
is `det (1 - (2 * t) • B) ^ (-c)` wherever that Hermitian pencil is positive definite, then the
characteristic function at `Θ` is the exponential of `-c` times the sum of the principal
logarithms of `1 - 2 * I * λ` over the eigenvalues `λ` of `B`.

The Wishart trace transform has this shape, with `B` the Hermitian sandwich `√S * Θ * √S` of the
scale matrix. -/
theorem charFun_eq_exp_of_mgf_trace_mul_eq_det_rpow
    {μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))}
    {Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} {B : Matrix (Fin p) (Fin p) ℝ}
    (hB : B.IsHermitian) (c : ℝ)
    (hmgf : ∀ t : ℝ, (1 - (2 * t) • B).PosDef →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        (1 - (2 * t) • B).det ^ (-c)) :
    charFun μ Θ =
      cexp (-(c : ℂ) * ∑ j, Complex.log (1 - 2 * Complex.I * (hB.eigenvalues j : ℂ))) := by
  have hprod : ∀ t : ℝ, (∀ j, 0 < 1 - 2 * t * hB.eigenvalues j) →
      mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) μ t =
        ∏ j, (1 - 2 * t * hB.eigenvalues j) ^ (-c) := by
    intro t ht
    have hpd : (1 - (2 * t) • B).PosDef :=
      (hB.posDef_one_sub_smul_iff (2 * t)).2 fun j => by linarith [ht j]
    have hdet := hB.det_one_sub_smul (2 * t)
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
    rw [hmgf t hpd, hdet, Real.finsetProd_rpow _ _ fun j _ => (ht j).le]
  rw [selfAdjoint.charFun_eq_complexMGF_trace_mul,
    complexMGF_I_eq_exp_of_mgf_eq_prod_rpow hB.eigenvalues (fun _ => c) hprod]
  congr 1
  rw [neg_mul, Finset.mul_sum]

/-- **The characteristic function of the Gaussian-Gram Wishart law.** At the symmetric matrix
`Θ` it is the exponential of `-ν / 2` times the sum of the principal logarithms of
`1 - 2 * I * λ` over the eigenvalues `λ` of the Hermitian sandwich `√S * Θ * √S`.

No hypothesis on the scale matrix is needed. Where `S` is not positive semidefinite it is not the
covariance of the Gaussian factors: Mathlib totalizes them to Dirac masses, `CFC.sqrt S` is zero,
its sandwich has only zero eigenvalues, and the value is `1`, the characteristic function of the
Dirac mass at the origin. -/
theorem charFun_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    charFun (wishartGramMeasure ν S) Θ =
      cexp (-(ν : ℂ) / 2 * ∑ j, Complex.log (1 - 2 * Complex.I *
        ((Matrix.isHermitian_sqrt_mul_mul_sqrt S
          (selfAdjoint.isHermitian_coe Θ)).eigenvalues j : ℂ))) := by
  have hcast : (((ν : ℝ) / 2 : ℝ) : ℂ) = (ν : ℂ) / 2 := by push_cast; ring
  rw [charFun_eq_exp_of_mgf_trace_mul_eq_det_rpow
      (Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)) ((ν : ℝ) / 2)
      fun t ht => by rw [mgf_trace_mul_wishartGramMeasure_sqrt ν S ht, neg_div],
    hcast, neg_div]

/-- **The characteristic function of the nonsingular Wishart law.** At the symmetric matrix `Θ`
it is the exponential of `-n / 2` times the sum of the principal logarithms of `1 - 2 * I * λ`
over the eigenvalues `λ` of the Hermitian sandwich `√S * Θ * √S`.

This is the Gaussian-Gram formula of `TauCeti.charFun_wishartGramMeasure` with the natural degree
`ν` replaced by the real degree `n`. Agreeing on characteristic functions is one ingredient of an
identification of the two families where both are defined; that identification is not proved
here. -/
theorem charFun_nonsingularWishartMeasure {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    charFun (nonsingularWishartMeasure n S) Θ =
      cexp (-(n : ℂ) / 2 * ∑ j, Complex.log (1 - 2 * Complex.I *
        ((Matrix.isHermitian_sqrt_mul_mul_sqrt S
          (selfAdjoint.isHermitian_coe Θ)).eigenvalues j : ℂ))) := by
  have hcast : ((n / 2 : ℝ) : ℂ) = (n : ℂ) / 2 := by push_cast; ring
  rw [charFun_eq_exp_of_mgf_trace_mul_eq_det_rpow
      (Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)) (n / 2)
      fun t ht => by rw [mgf_trace_mul_nonsingularWishartMeasure_sqrt hS hn ht, neg_div],
    hcast, neg_div]

/-! ### Convolution -/

/-- **At a fixed scale the degrees of the nonsingular Wishart family add under convolution.**
No hypothesis on the scale is needed: away from positive definiteness all three laws are zero.

The hypothesis on the sum of the degrees is not implied by the other two. In dimension zero the
valid degrees are those above `-1`, and two of them can still sum to `-1` or less, where the law
is zero by definition while the convolution of the two Dirac laws is again Dirac. In positive
dimension the valid degrees are positive, so the hypothesis is automatic. -/
@[simp]
theorem nonsingularWishartMeasure_conv_nonsingularWishartMeasure {n₁ n₂ : ℝ}
    (S : Matrix (Fin p) (Fin p) ℝ) (hn₁ : (p : ℝ) - 1 < n₁) (hn₂ : (p : ℝ) - 1 < n₂)
    (hn : (p : ℝ) - 1 < n₁ + n₂) :
    nonsingularWishartMeasure n₁ S ∗ nonsingularWishartMeasure n₂ S =
      nonsingularWishartMeasure (n₁ + n₂) S := by
  by_cases hS : S.PosDef
  · have := isProbabilityMeasure_nonsingularWishartMeasure hS hn₁
    have := isProbabilityMeasure_nonsingularWishartMeasure hS hn₂
    have := isProbabilityMeasure_nonsingularWishartMeasure hS hn
    refine Measure.ext_of_charFun (funext fun Θ => ?_)
    rw [charFun_conv, charFun_nonsingularWishartMeasure hS hn₁,
      charFun_nonsingularWishartMeasure hS hn₂, charFun_nonsingularWishartMeasure hS hn,
      ← Complex.exp_add]
    push_cast
    ring_nf
  · simp [nonsingularWishartMeasure_of_not_posDef _ hS]

end TauCeti
