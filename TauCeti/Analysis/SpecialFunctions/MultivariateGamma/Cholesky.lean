/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.LinearAlgebra.Matrix.Cholesky.Coordinates
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The multivariate Gamma function in Cholesky coordinates

Every positive-definite symmetric `p × p` matrix is `L * Lᵀ` for a unique lower-triangular `L`
with positive diagonal, and reading off the on-or-below-diagonal entries of `L` turns the
positive-definite cone into the region of `TauCeti.lowerTriangle p → ℝ` whose diagonal
coordinates are positive.  This file evaluates, in those coordinates, the integral whose value
is `TauCeti.multivariateGamma p a`:

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

/-- The region of lower-triangular coordinates on which the Cholesky factors live: the diagonal
coordinates are positive. -/
private def posDiagCoordinates (p : ℕ) : Set (lowerTriangle p → ℝ) :=
  {x | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩}

private theorem measurableSet_posDiagCoordinates : MeasurableSet (posDiagCoordinates p) := by
  have : posDiagCoordinates p = ⋂ i : Fin p, {x : lowerTriangle p → ℝ | 0 < x ⟨(i, i), le_rfl⟩} :=
    Set.ext fun _ ↦ by simp [posDiagCoordinates]
  rw [this]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_lt measurable_const (measurable_pi_apply (⟨(i, i), le_rfl⟩ : lowerTriangle p))

/-- The one-dimensional factor of the integrand attached to the coordinate `ij`.  A diagonal
coordinate contributes a Gamma integrand, restricted to the positive half-line because the
region constrains it; a strictly lower coordinate contributes a Gaussian integrand. -/
private def choleskyFactor (a : ℝ) (ij : lowerTriangle p) (t : ℝ) : ℝ :=
  if ij.1.1 = ij.1.2 then
    (Ioi (0 : ℝ)).indicator
      (fun s ↦ 2 * s ^ (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1) * exp (-s ^ 2)) t
  else exp (-t ^ 2)

/-- The powers of `√π` contributed by the strictly lower coordinates assemble into the power of
`π` appearing in `TauCeti.multivariateGamma`. -/
private theorem sqrt_pi_pow_sum (p : ℕ) :
    √π ^ (∑ i : Fin p, (i : ℕ)) = π ^ (((p : ℝ) * ((p : ℝ) - 1)) / 4) := by
  have hsum : ((∑ i : Fin p, (i : ℕ) : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    have h := Finset.sum_range_id_mul_two p
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ i) p]
    cases p with
    | zero => simp
    | succ n =>
      have hcast : ((∑ i ∈ Finset.range (n + 1), i : ℕ) : ℝ) * 2 = ((n + 1 : ℕ) : ℝ) * (n : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) h
      push_cast at hcast ⊢
      linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (π ^ (1 / 2 : ℝ)) _, ← Real.rpow_mul pi_pos.le, hsum]
  congr 1
  ring

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
        2 * (s ^ (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1) * exp (-1 * s ^ (2 : ℝ))))
        (fun s _ ↦ by simp only [Real.rpow_two, neg_one_mul]; ring),
      integral_const_mul,
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by linarith) one_pos, Real.one_rpow]
    have hexp : (2 * a - ((ij.1.1 : ℕ) : ℝ) - 1 + 1) / 2 = a - ((ij.1.1 : ℕ) : ℝ) / 2 := by ring
    rw [hexp]
    ring
  · simpa using integral_gaussian 1

/-- On the region the integrand is the product of the one-dimensional factors, and off it both
sides vanish: a nonpositive diagonal coordinate kills the corresponding factor. -/
private theorem indicator_eq_prod_choleskyFactor (a : ℝ) (x : lowerTriangle p → ℝ) :
    (posDiagCoordinates p).indicator
        (fun y : lowerTriangle p → ℝ ↦
          ((lowerTriangleMatrix p y * (lowerTriangleMatrix p y)ᵀ).det ^
                (a - ((p : ℝ) + 1) / 2) *
              exp (-(lowerTriangleMatrix p y * (lowerTriangleMatrix p y)ᵀ).trace)) *
            (2 ^ p * ∏ i : Fin p, y ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ)))) x =
      ∏ ij : lowerTriangle p, choleskyFactor a ij (x ij) := by
  classical
  by_cases hx : x ∈ posDiagCoordinates p
  · have hpos : ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩ := hx
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
  · obtain ⟨i, hi⟩ := not_forall.1 hx
    rw [Set.indicator_of_notMem hx]
    refine (Finset.prod_eq_zero (Finset.mem_univ (⟨(i, i), le_rfl⟩ : lowerTriangle p)) ?_).symm
    have hmem : x (⟨(i, i), le_rfl⟩ : lowerTriangle p) ∉ Ioi (0 : ℝ) := by simpa using hi
    simp [choleskyFactor, Set.indicator_of_notMem hmem]

/-- **The multivariate Gamma integral in Cholesky coordinates.**  Over the region of
lower-triangular coordinates with positive diagonal, the Wishart integrand `(det A) ^
(a - (p + 1) / 2) * exp (-trace A)` pulled back along `L ↦ L * Lᵀ` and weighted by the Jacobian
`2 ^ p * ∏ i, (L i i) ^ (p - i)` integrates to `Γ_p(a)`. -/
theorem integral_lowerTriangle_det_rpow_mul_exp_neg_trace
    (ha : ((p : ℝ) - 1) / 2 < a) :
    ∫ x in {x : lowerTriangle p → ℝ | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩},
        ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
          (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ))) =
      multivariateGamma p a := by
  calc ∫ x in posDiagCoordinates p,
          ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
              exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
            (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ)))
      = ∫ x : lowerTriangle p → ℝ, ∏ ij : lowerTriangle p, choleskyFactor a ij (x ij) := by
        rw [← integral_indicator measurableSet_posDiagCoordinates]
        exact integral_congr_ae (.of_forall (indicator_eq_prod_choleskyFactor a))
    _ = ∏ ij : lowerTriangle p, ∫ t, choleskyFactor a ij t := by
        rw [volume_pi]; exact integral_fintype_prod_eq_prod _
    _ = multivariateGamma p a := by
        rw [Finset.prod_congr rfl fun ij _ ↦ integral_choleskyFactor ha ij,
          prod_lowerTriangle_ite (fun i ↦ Real.Gamma (a - ((i : ℕ) : ℝ) / 2)) fun _ ↦ √π,
          Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sqrt_pi_pow_sum,
          multivariateGamma_def]
        ring

/-- For `((p : ℝ) - 1) / 2 < a`, the Jacobian-weighted Wishart integrand `(det (L * Lᵀ)) ^
(a - (p + 1) / 2) * exp (-trace (L * Lᵀ)) * (2 ^ p * ∏ i, (L i i) ^ (p - i))` is integrable over
the region of lower-triangular coordinates with positive diagonal. -/
theorem integrableOn_lowerTriangle_det_rpow_mul_exp_neg_trace
    (ha : ((p : ℝ) - 1) / 2 < a) :
    IntegrableOn (fun x : lowerTriangle p → ℝ ↦
        ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ (a - ((p : ℝ) + 1) / 2) *
            exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace)) *
          (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - (i : ℕ))))
      {x : lowerTriangle p → ℝ | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩} := by
  -- Were the integrand not integrable the integral would vanish, but it equals the positive
  -- value `Γ_p(a)`.
  by_contra h
  exact (multivariateGamma_pos ha).ne'
    ((integral_lowerTriangle_det_rpow_mul_exp_neg_trace ha).symm.trans (integral_undef h))

end TauCeti
