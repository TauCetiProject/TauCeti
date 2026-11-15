/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.Coefficient
public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.Analysis.Complex.PowerSeries.Integration

/-!
# Identifying multivariate Cauchy coefficients of native series

The Cauchy coefficient with exponent vector `m` of a function represented by a native
multilinear series `p` is a finite sum of basis evaluations of `p (∑ i, m i)`. The sum runs over
assignments of coordinates to multilinear slots with the prescribed multiplicities. This
identifies contour coefficients with the native presentation even when its multilinear maps
are not symmetric.

The extraction formula allows any expansion center and unequal positive contour radii bounded
strictly inside the ball of representation. It includes the constant coefficient and dimension
zero.

The proof combines `ContinuousMultilinearMap.torusIntegral_cauchyCoeff`, homogeneous-degree
orthogonality, and termwise integration of the native series from
`HasFPowerSeriesOnBall.hasSum_torusIntegral_cauchyCoeff`.

## References

L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {n : ℕ} {f : (Fin n → ℂ) → F}
  {p : FormalMultilinearSeries ℂ (Fin n → ℂ) F}
  {c : Fin n → ℂ} {R : Fin n → ℝ} {r : ℝ≥0∞}

omit [CompleteSpace F] in
/-- Translating the center of a torus integral of a homogeneous term turns the Cauchy weight
into `(z i)⁻¹ ^ (m i + 1)` on the torus centered at the origin. -/
private theorem torusIntegral_cauchyCoeff_translate (p : FormalMultilinearSeries ℂ (Fin n → ℂ) F)
    (m : Fin n → ℕ) (k : ℕ) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • p k (fun _ ↦ z - c)) =
      ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(0, R), (∏ i, (z i)⁻¹ ^ (m i + 1)) • p k (fun _ ↦ z)) := by
  -- Translation preserves the parametrized torus differential as well as the integrand.
  simp only [torusIntegral, ← Pi.sub_apply, torusMap_sub_center,
    Finset.prod_inv_distrib, inv_pow]

/-- A multivariate Cauchy coefficient of an analytic function is the finite sum of basis
values of the native multilinear term of the corresponding total degree. No symmetry of
that term is assumed. The contour radii are positive and bounded strictly inside the ball
on which the given series represents the function. -/
theorem HasFPowerSeriesOnBall.torusIntegral_cauchyCoeff
    (hf : HasFPowerSeriesOnBall f p c r) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < r) (hR : ∀ i, 0 < R i) (hRs : ∀ i, R i ≤ s)
    (m : Fin n → ℕ) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • f z) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (∑ i, m i) → Fin n ↦
        ∀ i, Fintype.card {j // a j = i} = m i),
        p (∑ i, m i) (fun j ↦ Pi.single (a j) 1) := by
  classical
  let A : ℕ → F := fun k ↦ ((2 * π * I : ℂ) ^ n)⁻¹ •
    (∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • p k (fun _ ↦ z - c))
  have hzero (k : ℕ) (hk : k ≠ ∑ i, m i) : A k = 0 :=
    (torusIntegral_cauchyCoeff_translate p m k).trans
      ((p k).torusIntegral_cauchyCoeff_eq_zero m hR (by simpa using hk.symm))
  have hsum : HasSum A (((2 * π * I : ℂ) ^ n)⁻¹ •
      ∯ z in T(c, R), (∏ i, (z i - c i) ^ (m i + 1))⁻¹ • f z) :=
    (hf.hasSum_torusIntegral_cauchyCoeff hs hR hRs m).const_smul _
  exact (hsum.unique (hasSum_single (∑ i, m i) hzero)).trans
    ((torusIntegral_cauchyCoeff_translate p m _).trans
      ((p (∑ i, m i)).torusIntegral_cauchyCoeff m hR))
