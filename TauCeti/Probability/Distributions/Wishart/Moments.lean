/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Transforms
public import TauCeti.Probability.Moments.PencilMGF

import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Matrix.Trace

/-!
# The mean and covariance of the Gaussian-Gram Wishart family

The trace statistics `A ↦ trace (Θ * A)` of a Gaussian-Gram Wishart matrix have finite
exponential moments on a neighbourhood of the origin, because the pencil
`1 - (2 * t) • (√S * Θ * √S)` that governs them is positive definite for small `t`. Their
cumulant-generating function, the logarithm of the moment-generating function, is therefore
differentiable at the origin, and this file reads its first two derivatives there: the mean
`ν * trace (Θ * S)` and the variance `2 * ν * trace (Θ * S * Θ * S)`.

Polarizing the variance gives the covariance of two trace statistics, and pairing with the
symmetrized matrix units `TauCeti.symmetricSingle` turns that into the classical entrywise
covariance `ν * (S i k * S j l + S i l * S j k)` of a Wishart matrix. Testing the mean against
every symmetric matrix identifies the Bochner mean of the law itself as `ν • S`.

The degrees of freedom enter only through the exponent of the determinant in the
moment-generating function, so nothing here needs `ν` to be at least the dimension: the singular
laws have the same mean and covariance as the nonsingular ones.

## Main results

* `TauCeti.integral_trace_mul_wishartGramMeasure` and
  `TauCeti.variance_trace_mul_wishartGramMeasure` — the mean and variance of a trace statistic;
* `TauCeti.covariance_trace_mul_wishartGramMeasure` — the covariance of two trace statistics;
* `TauCeti.integral_id_wishartGramMeasure` — the Bochner mean of the law is `ν • S`;
* `TauCeti.covariance_coe_apply_wishartGramMeasure` — the covariance of two entries.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti

variable {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
  {Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-! ### Moments of every order -/

/-- The origin is interior to the exponential-integrability domain of a Wishart trace statistic:
the pencil `1 - (2 * t) • (√S * Θ * √S)` is positive definite for every small `t`. The statistic
therefore has moments of every order, and its transforms are differentiable at the origin. -/
theorem zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure (ν : ℕ)
    (S : Matrix (Fin p) (Fin p) ℝ) (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    0 ∈ interior (integrableExpSet
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S)) := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  refine zero_mem_interior_integrableExpSet_of_forall_mul_lt_one hB.eigenvalues fun t ht => ?_
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · exact Set.eq_univ_iff_forall.1 (integrableExpSet_trace_mul_wishartGramMeasure_zero Θ S) t
  · exact (mem_integrableExpSet_trace_mul_wishartGramMeasure_iff hν S t).2
      ((hB.posDef_one_sub_smul_iff (2 * t)).2 ht)

/-- A Wishart trace statistic is square integrable, so it has a mean and a variance and pairs
with every other trace statistic in a covariance. -/
theorem memLp_trace_mul_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    MemLp (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) 2
      (wishartGramMeasure ν S) := by
  simpa using memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure ν S Θ) 2

/-- The moment-generating function of a Wishart trace statistic, written as the pencil product
whose factors are indexed by the eigenvalues of the sandwich `√S * Θ * √S`. -/
private theorem mgf_trace_mul_wishartGramMeasure_eq_prod (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ)
    (hB : (CFC.sqrt S * (Θ : Matrix (Fin p) (Fin p) ℝ) * CFC.sqrt S).IsHermitian) (t : ℝ)
    (ht : ∀ j, 2 * t * hB.eigenvalues j < 1) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure ν S) t =
      ∏ j, (1 - 2 * t * hB.eigenvalues j) ^ (-((ν : ℝ) / 2)) := by
  rw [mgf_trace_mul_wishartGramMeasure_sqrt ν S ((hB.posDef_one_sub_smul_iff (2 * t)).2 ht),
    hB.det_one_sub_smul (2 * t),
    Real.finsetProd_rpow _ _ (fun j _ => (sub_pos.2 (ht j)).le) (-((ν : ℝ) / 2))]
  simp [neg_div]

/-! ### The mean and the variance of a trace statistic -/

/-- **The mean of a Wishart trace statistic** is `ν * trace (Θ * S)`. -/
theorem integral_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace
      ∂wishartGramMeasure ν S = ν * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have htrace : ∑ i, hB.eigenvalues i = ((Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
    rw [← hS.trace_sqrt_mul_mul_sqrt]
    simpa using (hB.trace_eq_sum_eigenvalues (𝕜 := ℝ)).symm
  rw [integral_eq_of_mgf_eq_prod_rpow (a := fun _ => (ν : ℝ) / 2)
      (zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure ν S Θ)
      (mgf_trace_mul_wishartGramMeasure_eq_prod ν S hB),
    ← Finset.mul_sum, htrace]
  ring

/-- **The variance of a Wishart trace statistic** is `2 * ν * trace (Θ * S * Θ * S)`. -/
theorem variance_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    Var[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace;
      wishartGramMeasure ν S] =
      2 * ν * ((Θ : Matrix (Fin p) (Fin p) ℝ) * S * (Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S (selfAdjoint.isHermitian_coe Θ)
  have htrace : ∑ i, hB.eigenvalues i ^ 2 =
      ((Θ : Matrix (Fin p) (Fin p) ℝ) * S * (Θ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
    rw [← hS.trace_sqrt_mul_mul_sqrt_mul_self]
    simpa using (hB.trace_mul_self_eq_sum_eigenvalues_sq (𝕜 := ℝ)).symm
  rw [variance_eq_of_mgf_eq_prod_rpow (a := fun _ => (ν : ℝ) / 2)
      (zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure ν S Θ)
      (mgf_trace_mul_wishartGramMeasure_eq_prod ν S hB),
    ← Finset.mul_sum, htrace]
  ring

/-! ### Covariance -/

/-- **The covariance of two Wishart trace statistics** is `2 * ν * trace (Θ₁ * S * Θ₂ * S)`, the
polarization of `TauCeti.variance_trace_mul_wishartGramMeasure`. -/
theorem covariance_trace_mul_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef)
    (Θ₁ Θ₂ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ₁ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          ((Θ₂ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace;
      wishartGramMeasure ν S] =
      2 * ν *
        ((Θ₁ : Matrix (Fin p) (Fin p) ℝ) * S * (Θ₂ : Matrix (Fin p) (Fin p) ℝ) * S).trace := by
  have hadd : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      ((Θ₁ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace +
        ((Θ₂ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (((Θ₁ + Θ₂ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
          Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace := by
    funext A
    rw [Submodule.coe_add, Matrix.add_mul, Matrix.trace_add]
  have hvar := variance_fun_add (memLp_trace_mul_wishartGramMeasure ν S Θ₁)
    (memLp_trace_mul_wishartGramMeasure ν S Θ₂)
  rw [hadd, variance_trace_mul_wishartGramMeasure ν hS,
    variance_trace_mul_wishartGramMeasure ν hS, variance_trace_mul_wishartGramMeasure ν hS,
    Submodule.coe_add, Matrix.trace_add_mul_mul_add_mul] at hvar
  linarith

/-! ### The mean of the law and the covariance of its entries -/

/-- The identity is Bochner integrable for the Gaussian-Gram Wishart law: its entries are trace
statistics, which have moments of every order. -/
theorem integrable_id_wishartGramMeasure (ν : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Integrable id (wishartGramMeasure ν S) := by
  have hcoord : ∀ ij : upperTriangle p,
      Integrable (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (symmetricBasis p).repr A ij) (wishartGramMeasure ν S) := by
    intro ij
    have hint := integrable_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet_trace_mul_wishartGramMeasure ν S
        (symmetricSingle ij.1.1 ij.1.2))
    simp only [trace_symmetricSingle_mul] at hint
    simpa using hint
  have hrepr : (id : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → _) =
      fun A => ∑ ij, (symmetricBasis p).repr A ij • symmetricBasis p ij :=
    funext fun A => ((symmetricBasis p).sum_repr A).symm
  rw [hrepr]
  exact integrable_finsetSum _ fun ij _ => (hcoord ij).smul_const _

/-- **The mean of the Gaussian-Gram Wishart law** is `ν • S`. -/
theorem integral_id_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef) :
    ∫ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), A ∂wishartGramMeasure ν S =
      (ν : ℝ) • (⟨S, Matrix.isHermitian_iff_isSelfAdjoint.1 hS.isHermitian⟩ :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  refine ext_inner_left ℝ fun Θ => ?_
  have hinner : ∀ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      ⟪Θ, A⟫ = ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace :=
    fun A => by rw [real_inner_comm, selfAdjoint.inner_eq_trace_mul]
  rw [← integral_inner (f := fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) => A)
      (integrable_id_wishartGramMeasure ν S) Θ, real_inner_smul_right]
  simp only [hinner]
  rw [integral_trace_mul_wishartGramMeasure ν hS]

/-- **The entrywise covariance of the Gaussian-Gram Wishart law**: the entries at `(i, j)` and
at `(k, l)` have covariance `ν * (S i k * S j l + S i l * S j k)`. -/
theorem covariance_coe_apply_wishartGramMeasure (ν : ℕ) (hS : S.PosSemidef) (i j k l : Fin p) :
    cov[fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) i j,
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
          (A : Matrix (Fin p) (Fin p) ℝ) k l;
      wishartGramMeasure ν S] = ν * (S i k * S j l + S i l * S j k) := by
  have hij : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ) i j) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((symmetricSingle i j : Matrix (Fin p) (Fin p) ℝ) *
          (A : Matrix (Fin p) (Fin p) ℝ)).trace :=
    funext fun A => (trace_symmetricSingle_mul i j A).symm
  have hkl : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ) k l) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        ((symmetricSingle k l : Matrix (Fin p) (Fin p) ℝ) *
          (A : Matrix (Fin p) (Fin p) ℝ)).trace :=
    funext fun A => (trace_symmetricSingle_mul k l A).symm
  rw [hij, hkl, covariance_trace_mul_wishartGramMeasure ν hS,
    trace_symmetricSingle_mul_mul_symmetricSingle_mul hS.isHermitian]
  ring

end TauCeti
