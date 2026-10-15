/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The multivariate Gamma function in Cholesky coordinates

Every positive-definite symmetric `p × p` matrix is `L * Lᵀ` for a unique lower-triangular `L`
with positive diagonal, and reading off the on-or-below-diagonal entries of `L` turns the
positive-definite cone into the region `TauCeti.posDiagLowerRegion p` of
`TauCeti.lowerTriangle p → ℝ` whose diagonal coordinates are positive.  This file evaluates, in
those coordinates, the integral whose value is `TauCeti.multivariateGamma p a` when
`(p - 1) / 2 < a` (a condition only in positive dimension):

`∫ (det (L * Lᵀ)) ^ (a - (p + 1) / 2) * exp (-trace (L * Lᵀ)) * (2 ^ p * ∏ i, (L i i) ^ (p - i))`

over that region, the last factor being the Jacobian of `L ↦ L * Lᵀ` computed in
`TauCeti/LinearAlgebra/Matrix/Cholesky/Jacobian.lean`.  The point of the coordinates is that the
integrand factorizes: the determinant and the trace of `L * Lᵀ` are a product and a sum over the
entries of `L`, so Fubini reduces the integral to one-dimensional Gamma and Gaussian integrals,
one for each entry.  The `p` diagonal entries produce the Gamma factors `Γ(a - i / 2)` and the
`p (p - 1) / 2` strictly lower entries produce the powers of `√π`.

Transported by the Cholesky change of variables, this integral is the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the cone of positive-definite symmetric
matrices against `TauCeti.symmetricLebesgue p`, which is the normalizing constant of the Wishart
density.

## Main results

* `TauCeti.integral_lowerTriangle_det_rpow_mul_exp_neg_trace` — the value of the integral;
* `TauCeti.integrableOn_lowerTriangle_det_rpow_mul_exp_neg_trace` — its integrand is
  integrable on the region.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Theorem 2.1.14.
* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Chapter 5.
-/

public section

noncomputable section

open MeasureTheory Real Set

open scoped Matrix

namespace TauCeti

variable {p : ℕ} {a : ℝ}

/-- The one-dimensional factor of the integrand attached to the coordinate `ij`.  A diagonal
coordinate contributes a Gamma integrand, restricted to the positive half-line because the
region constrains it; a strictly lower coordinate contributes a Gaussian integrand. -/
private def choleskyFactor (a : ℝ) (ij : lowerTriangle p) (t : ℝ) : ℝ :=
  if ij.1.1 = ij.1.2 then
    (Ioi (0 : ℝ)).indicator
      (fun s ↦ 2 * s ^ (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1) * exp (-s ^ 2)) t
  else exp (-t ^ 2)

/-- Each one-dimensional factor integrates to a Gamma value on the diagonal and to `√π` off it. -/
private theorem integral_choleskyFactor (ha : ((p : ℝ) - 1) / 2 < a) (ij : lowerTriangle p) :
    ∫ t, choleskyFactor a ij t =
      if ij.1.1 = ij.1.2 then Real.Gamma (a - ((ij.1.1 : ℕ) : ℝ) / 2) else √π := by
  simp only [choleskyFactor]
  split_ifs with h
  · have hlt : ((ij.1.1 : ℕ) : ℝ) < 2 * a := by
      have : ((ij.1.1 : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast ij.1.1.2
      linarith
    rw [integral_indicator measurableSet_Ioi,
      setIntegral_congr_fun measurableSet_Ioi (g := fun s ↦
        2 * (s ^ (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1) * exp (-s ^ (2 : ℝ))))
        (fun s _ ↦ by simp only [Real.rpow_two]; ring),
      integral_const_mul, integral_rpow_mul_exp_neg_rpow (by norm_num) (by linarith)]
    have hexp : (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1 + 1) / 2 = a - ((ij.1.1 : ℕ) : ℝ) / 2 := by ring
    rw [hexp]
    ring
  · simpa using integral_gaussian 1

/-- On the region the integrand is the product of the one-dimensional factors, and off it both
sides vanish: a nonpositive diagonal coordinate kills the corresponding factor. -/
private theorem indicator_eq_prod_choleskyFactor (a : ℝ) (x : lowerTriangle p → ℝ) :
    (posDiagLowerRegion p).indicator
        (fun y : lowerTriangle p → ℝ ↦
          ((lowerTriangleMatrix p y * (lowerTriangleMatrix p y)ᵀ).det ^
                (a - ((p : ℝ) + 1) / 2) *
              exp (-(lowerTriangleMatrix p y * (lowerTriangleMatrix p y)ᵀ).trace)) *
            (2 ^ p * ∏ i : Fin p, y ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ)))) x =
      ∏ ij : lowerTriangle p, choleskyFactor a ij (x ij) := by
  by_cases hx : x ∈ posDiagLowerRegion p
  · have hpos : ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩ := (mem_posDiagLowerRegion p).mp hx
    -- Split each factor into the part depending on the exponent and a Gaussian part.
    have hfac : ∀ ij : lowerTriangle p, choleskyFactor a ij (x ij) =
        (if ij.1.1 = ij.1.2 then
            2 * x ⟨(ij.1.1, ij.1.1), le_rfl⟩ ^ (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1) else 1) *
          exp (-x ij ^ 2) := by
      intro ij
      simp only [choleskyFactor]
      split_ifs with h
      · have hij : ij = ⟨(ij.1.1, ij.1.1), le_rfl⟩ := Subtype.ext (Prod.ext rfl h.symm)
        rw [Set.indicator_of_mem (by rw [hij]; exact hpos ij.1.1), ← hij]
      · ring
    have hcore := prod_lowerTriangle_diag_rpow_mul_exp_neg_sq x hpos
      (a - ((p : ℝ) + 1) / 2) 1 (fun _ ↦ 2) 1
    have hexponent : ∀ i : Fin p,
        2 * (a - ((p : ℝ) + 1) / 2) + p - ((i : ℕ) : ℝ) =
          2 * a - ((i : ℕ) : ℝ) - 1 := by
      intro i
      ring
    simp_rw [hexponent] at hcore
    simp only [neg_one_mul, one_pow, mul_one] at hcore
    rw [Set.indicator_of_mem hx, Finset.prod_congr rfl fun ij _ ↦ hfac ij]
    rw [hcore]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  · obtain ⟨i, hi⟩ := not_forall.1 ((mem_posDiagLowerRegion p).not.1 hx)
    rw [Set.indicator_of_notMem hx]
    refine (Finset.prod_eq_zero (Finset.mem_univ (⟨(i, i), le_rfl⟩ : lowerTriangle p)) ?_).symm
    have hmem : x (⟨(i, i), le_rfl⟩ : lowerTriangle p) ∉ Ioi (0 : ℝ) := by simpa using hi
    simp [choleskyFactor, Set.indicator_of_notMem hmem]

/-- **The multivariate Gamma integral in Cholesky coordinates.**  Over the region of
lower-triangular coordinates with positive diagonal, the Wishart integrand `(det A) ^
(a - (p + 1) / 2) * exp (-trace A)` pulled back along `L ↦ L * Lᵀ` and weighted by the Jacobian
`2 ^ p * ∏ i, (L i i) ^ (p - i)` integrates to `Γ_p(a)` when `(p - 1) / 2 < a`. The bound is
needed only in positive dimension: for `p = 0` the coordinate space is a point, where the integrand
is `1 = Γ₀(a)` for every `a`. -/
theorem integral_lowerTriangle_det_rpow_mul_exp_neg_trace
    (ha : 0 < p → ((p : ℝ) - 1) / 2 < a) :
    ∫ x in posDiagLowerRegion p,
        ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
          (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ))) =
      multivariateGamma p a := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · -- In dimension zero the region is the whole one-point coordinate space.
    have : IsEmpty (lowerTriangle 0) := ⟨fun ij ↦ ij.1.1.elim0⟩
    rw [show posDiagLowerRegion 0 = Set.univ from
        Set.eq_univ_of_forall fun x ↦ (mem_posDiagLowerRegion 0).2 fun i ↦ i.elim0,
      Measure.restrict_univ, Measure.volume_pi_eq_dirac, integral_dirac, multivariateGamma_zero]
    simp
  have ha := ha hp
  calc ∫ x in posDiagLowerRegion p,
          ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
              exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
            (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ)))
      = ∫ x : lowerTriangle p → ℝ, ∏ ij : lowerTriangle p, choleskyFactor a ij (x ij) := by
        rw [← integral_indicator (measurableSet_posDiagLowerRegion p)]
        exact integral_congr_ae (.of_forall (indicator_eq_prod_choleskyFactor a))
    _ = ∏ ij : lowerTriangle p, ∫ t, choleskyFactor a ij t := by
        exact integral_fintype_prod_volume_eq_prod _
    _ = multivariateGamma p a := by
        rw [Finset.prod_congr rfl fun ij _ ↦ integral_choleskyFactor ha ij,
          prod_lowerTriangle_ite (fun i ↦ Real.Gamma (a - ((i : ℕ) : ℝ) / 2)) fun _ ↦ √π,
          multivariateGamma_eq_prod]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul pi_pos.le, mul_comm]
        ring_nf

/-- For `((p : ℝ) - 1) / 2 < a` (a condition only in positive dimension), the Jacobian-weighted
Wishart integrand `(det (L * Lᵀ)) ^ (a - (p + 1) / 2) * exp (-trace (L * Lᵀ)) *
(2 ^ p * ∏ i, (L i i) ^ (p - i))` is integrable over the region of lower-triangular coordinates
with positive diagonal. -/
theorem integrableOn_lowerTriangle_det_rpow_mul_exp_neg_trace
    (ha : 0 < p → ((p : ℝ) - 1) / 2 < a) :
    IntegrableOn (fun x : lowerTriangle p → ℝ ↦
        ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
          (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ))))
      (posDiagLowerRegion p) := by
  -- A function whose integral is nonzero is integrable, and this integral is `Γ_p(a) ≠ 0`.
  apply Integrable.of_integral_ne_zero
  rw [integral_lowerTriangle_det_rpow_mul_exp_neg_trace ha]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [multivariateGamma_zero]; exact one_ne_zero
  · exact (multivariateGamma_pos (ha hp)).ne'

end TauCeti
