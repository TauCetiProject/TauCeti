/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Torus.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Cauchy coefficients of multilinear homogeneous terms

The diagonal of a continuous multilinear map is a homogeneous polynomial. Its multivariate
Cauchy coefficient is the sum of its values on basis tuples having the prescribed coordinate
multiplicities. This identifies coefficients obtained by contour integration with those of
native formal multilinear series, without assuming that their multilinear maps are symmetric.

The contour radii may differ but must be positive. The formulas include degree zero and
zero-dimensional coordinate spaces.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real

namespace ContinuousMultilinearMap

variable {ν E : Type*} [Fintype ν] [DecidableEq ν] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] {n : ℕ}

/-- The multivariate Cauchy coefficient of the diagonal of a continuous multilinear map
is the sum of its basis evaluations over assignments with the specified coordinate counts.
No symmetry of the multilinear map is required. -/
theorem torusIntegral_cauchyCoeff (p : ContinuousMultilinearMap ℂ (fun _ : ν => Fin n → ℂ) E)
    (a : Fin n → ℕ) {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(0, R), (∏ i, (z i)⁻¹ ^ (a i + 1)) • p (fun _ => z)) =
      ∑ r ∈ Finset.univ.filter (fun r : ν → Fin n =>
        ∀ i, Fintype.card {k // r k = i} = a i), p (fun k => Pi.single (r k) 1) := by
  -- Expand the diagonal in coordinate monomials, grouped by coordinate multiplicity.
  let b (r : ν → Fin n) (i : Fin n) := Fintype.card {k // r k = i}
  have hp (z : Fin n → ℂ) : p (fun _ => z) =
      ∑ r : ν → Fin n, (∏ i, z i ^ b r i) • p (fun k => Pi.single (r k) 1) := by
    have hz : (fun _ : ν => z) = fun _ : ν => ∑ i, z i • Pi.single i 1 := by
      funext k
      exact pi_eq_sum_univ' z
    rw [hz, p.map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [p.map_smul_univ]
    congr 1
    simpa [b] using (Fintype.prod_fiberwise' r z).symm
  have hprod (z : Fin n → ℂ) (r : ν → Fin n) :
      (∏ i, (z i)⁻¹ ^ (a i + 1)) * (∏ i, z i ^ b r i) =
        ∏ i, z i ^ b r i / z i ^ (a i + 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp [div_eq_mul_inv, mul_comm]
  have hexpand : (fun z : Fin n → ℂ =>
      (∏ i, (z i)⁻¹ ^ (a i + 1)) • p (fun _ => z)) =
      fun z => ∑ r : ν → Fin n,
        (∏ i, z i ^ b r i / z i ^ (a i + 1)) • p (fun k => Pi.single (r k) 1) := by
    funext z
    simp only [hp, Finset.smul_sum, smul_smul, hprod]
  -- Each term is continuous on the torus, so finite linearity applies.
  have hcont (r : ν → Fin n) : TorusIntegrable (fun z : Fin n → ℂ =>
      (∏ i, z i ^ b r i / z i ^ (a i + 1)) • p (fun k => Pi.single (r k) 1)) 0 R := by
    apply Continuous.integrableOn_Icc
    apply Continuous.smul _ continuous_const
    apply continuous_finsetProd
    intro i _
    apply Continuous.div
    · fun_prop [torusMap]
    · fun_prop [torusMap]
    · intro θ
      simp [torusMap, (hR i).ne']
  -- Monomial orthogonality retains exactly the assignments with the requested counts.
  rw [hexpand, TauCeti.torusIntegral_finsetSum _ (fun r _ => hcont r)]
  simp_rw [TauCeti.torusIntegral_smul_const, TauCeti.torusIntegral_prod_pow_div_pow a _ hR]
  rw [Finset.smul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  have hba : b r = a ↔ ∀ i, Fintype.card {k // r k = i} = a i := funext_iff
  by_cases h : b r = a
  · simp [h, ← hba, smul_smul, Real.pi_ne_zero, Complex.I_ne_zero]
  · simp [h, ← hba]

omit [DecidableEq ν] in
/-- A homogeneous term has zero Cauchy coefficient in every other total degree. -/
theorem torusIntegral_cauchyCoeff_eq_zero
    (p : ContinuousMultilinearMap ℂ (fun _ : ν => Fin n → ℂ) E)
    (a : Fin n → ℕ) {R : Fin n → ℝ} (hR : ∀ i, 0 < R i)
    (ha : ∑ i, a i ≠ Fintype.card ν) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(0, R), (∏ i, (z i)⁻¹ ^ (a i + 1)) • p (fun _ => z)) = 0 := by
  classical
  rw [p.torusIntegral_cauchyCoeff a hR]
  apply Finset.sum_eq_zero
  intro r hr
  have hcount := (Finset.mem_filter.1 hr).2
  exfalso
  apply ha
  simp_rw [← hcount]
  simpa using (Fintype.sum_fiberwise' r (fun _ => (1 : ℕ)))

end ContinuousMultilinearMap
