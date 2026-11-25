/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.SubGaussian.Vector
import TauCeti.Analysis.Normed.Group.Real

/-!
# Linear forms of independent sub-Gaussian coordinates

For independent random variables `Xᵢ` with variance proxies `Kᵢ` and a deterministic vector `w`,
the dot product `X ⬝ᵥ w` has variance proxy `∑ᵢ ‖wᵢ‖₊² Kᵢ`. Consequently a random vector of
`EuclideanSpace ℝ ι` with independent coordinates of proxy `c` is a sub-Gaussian vector with
proxy `c`, and the dot products of independent real coordinates, or of the split real and
imaginary parts of independent directionally sub-Gaussian complex coordinates, satisfy the
exponential moment bound `exp (K r² ‖w‖² / 2)`.

## Main results

* `ProbabilityTheory.iIndepFun.hasSubgaussianMGF_dotProduct`: the variance proxy of a dot product
  of independent sub-Gaussian coordinates.
* `ProbabilityTheory.iIndepFun.isSubgaussianVector`: independent coordinates of proxy `c` form a
  sub-Gaussian vector (`TauCeti.IsSubgaussianVector`) with proxy `c`.
* `ProbabilityTheory.iIndepFun.integral_exp_mul_dotProduct_le`,
  `ProbabilityTheory.iIndepFun.integral_exp_mul_sum_elim_re_im_dotProduct_le`: exponential moment
  bounds for the real and the split complex dot products.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §2.6 and §3.4.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Matrix

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- The dot product of independent sub-Gaussian random variables with a deterministic vector `w`
is sub-Gaussian with variance proxy `∑ i, ‖w i‖₊ ^ 2 * K i`. -/
theorem hasSubgaussianMGF_dotProduct {X : ι → Ω → ℝ} (hindep : iIndepFun X P) {K : ι → ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) (K i) P) (w : ι → ℝ) :
    HasSubgaussianMGF (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ w) (∑ i, ‖w i‖₊ ^ 2 * K i) P := by
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i, w i * X i ω) (∑ i, ‖w i‖₊ ^ 2 * K i) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i x ↦ w i * x) fun i ↦ measurable_const_mul (w i))
      fun i _ ↦ Real.nnNorm_sq (w i) ▸ (hX i).const_mul (w i)
  simpa only [dotProduct, mul_comm] using hsum

/-- A random vector of `EuclideanSpace ℝ ι` with independent coordinates, each with variance
proxy `c`, is a sub-Gaussian vector (`TauCeti.IsSubgaussianVector`) with proxy `c`: the form
`⟪u, x⟫` has proxy `∑ i, ‖u i‖₊ ^ 2 * c = c * ‖u‖₊ ^ 2`. In particular every unit direction has
the same proxy `c` as the coordinates, so the coordinate bound passes to all linear forms. -/
theorem isSubgaussianVector {x : Ω → EuclideanSpace ℝ ι} {c : ℝ≥0}
    (hindep : iIndepFun (fun i ω ↦ x ω i) P) (hx : ∀ i, HasSubgaussianMGF (fun ω ↦ x ω i) c P) :
    TauCeti.IsSubgaussianVector x c P := by
  refine TauCeti.isSubgaussianVector_def.2 fun u ↦ ?_
  have hproxy : ∑ i, ‖u i‖₊ ^ 2 * c = c * ‖u‖₊ ^ 2 := by
    rw [← Finset.sum_mul, EuclideanSpace.nnNorm_eq]
    simp [mul_comm]
  rw [← hproxy]
  refine (hindep.hasSubgaussianMGF_dotProduct hx u).congr (ae_of_all _ fun ω ↦ ?_)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- Exponential moment bound for the dot product of independent `K`-sub-Gaussian random variables
with a deterministic vector `w`. -/
theorem integral_exp_mul_dotProduct_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P) {K : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) K P) (w : ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * ((fun i ↦ X i ω) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * ((fun i ↦ X i ω) ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ i, w i ^ 2) := by
  have hsub := hindep.hasSubgaussianMGF_dotProduct hX w
  refine ⟨hsub.integrable_exp_mul r, ?_⟩; rw [← mgf]; refine (hsub.mgf_le r).trans_eq ?_
  congr 1
  simp only [NNReal.coe_sum, NNReal.coe_mul, Real.coe_nnNorm_sq, ← Finset.sum_mul]; ring

/-- Exponential moment bound for the split-coordinate dot product of independent directionally
`K`-sub-Gaussian complex random variables with `w : ι ⊕ ι → ℝ`. -/
theorem integral_exp_mul_sum_elim_re_im_dotProduct_le {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (w : ι ⊕ ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)) ∂P ≤
        exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2) := by
  let u : ι → ℂ := fun i ↦ ⟨w (.inl i), w (.inr i)⟩
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i, (star (u i) * Z i ω).re)
      (∑ i, ‖u i‖₊ ^ 2 * K) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i z ↦ (star (u i) * z).re) fun _ ↦ by fun_prop) fun i _ ↦ hZ i (u i)
  have hdot (ω : Ω) : Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w =
      ∑ i, (star (u i) * Z i ω).re := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      ← Finset.sum_add_distrib, u, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hsub : HasSubgaussianMGF
      (fun ω ↦ Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)
      (∑ i, ‖u i‖₊ ^ 2 * K) P := by simpa only [hdot] using hsum
  refine ⟨hsub.integrable_exp_mul r, ?_⟩; rw [← mgf]; refine (hsub.mgf_le r).trans_eq ?_
  congr 1; push_cast
  simp only [Complex.sq_norm, Complex.normSq_apply, u, Fintype.sum_sum_type, ← sq,
    Finset.sum_add_distrib, ← Finset.sum_mul]; ring

end ProbabilityTheory.iIndepFun
