/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Gaussian
public import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The radial Mellin transform and Epstein zeta

The Mellin transform of a lattice theta series in a single positive parameter is the
Epstein zeta series of its Euclidean quadratic form. It sums over nonzero lattice points,
not over ideals or unit orbits. Thus the radial integral alone is not the integral
representation of a partial Dedekind zeta function when the unit rank is positive.

We use the mixed-space form `mixedInner`, where each complex place counts once. Absolute
convergence of the Epstein series and summability of the integrals of the norms justify
interchanging the lattice sum with the Mellin integral. The zero term is removed from the
whole theta series, rather than subtracting a constant from each summand.

The convergence proof uses Mathlib's `ZLattice.summable_norm_rpow`. The individual Mellin
integrals are Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` and its real counterpart.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3–5.
-/

public section

noncomputable section

open Complex MeasureTheory Set NumberField NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Real

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The Epstein zeta series of a mixed-space lattice for the Euclidean form `mixedInner`.
The sum is over nonzero lattice points, not ideals modulo units. -/
def epsteinZeta (L : Submodule ℤ (mixedSpace K)) (s : ℂ) : ℂ :=
  ∑' x : {x : L // x ≠ 0}, (mixedInner K x x : ℂ) ^ (-s)

/-- The defining lattice-point sum for the Epstein zeta series. -/
theorem epsteinZeta_def (L : Submodule ℤ (mixedSpace K)) (s : ℂ) :
    epsteinZeta L s = ∑' x : {x : L // x ≠ 0}, (mixedInner K x x : ℂ) ^ (-s) := (rfl)

private theorem mixedInner_pos {L : Submodule ℤ (mixedSpace K)}
    (x : {x : L // x ≠ 0}) : 0 < mixedInner K x x := by
  classical
  have hx : (x : mixedSpace K) ≠ 0 := by simpa using x.2
  exact (sq_pos_of_pos (norm_pos_iff.mpr hx)).trans_le (norm_sq_le_mixedInner_self K _)

/-- The Epstein series converges absolutely to the right of half the lattice rank.
The lattice need not have full rank. -/
theorem summable_epsteinZeta (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    {s : ℂ} (hs : (Module.finrank ℤ L : ℝ) / 2 < s.re) :
    Summable fun x : {x : L // x ≠ 0} ↦ (mixedInner K x x : ℂ) ^ (-s) := by
  classical
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  refine Summable.of_norm_bounded
    ((ZLattice.summable_norm_rpow L (-2 * s.re) (by linarith)).subtype (· ≠ 0)) ?_
  intro x
  have hx : (x : mixedSpace K) ≠ 0 := by simpa using x.2
  rw [norm_cpow_eq_rpow_re_of_pos (mixedInner_pos x), neg_re]
  calc
    mixedInner K x x ^ (-s.re) ≤ (‖(x : mixedSpace K)‖ ^ 2) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
        (norm_sq_le_mixedInner_self K _) (by linarith)
    _ = ‖(x : L)‖ ^ (-2 * s.re) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring

private theorem archGaussian_const (t : ℝ) (x : mixedSpace K) :
    archGaussian (fun _ ↦ t) x = (Real.exp (-(π * mixedInner K x x * t)) : ℂ) := by
  rw [archGaussian_apply, ← Finset.mul_sum, ← mixedInner_self_eq_sum]
  congr 2
  ring

private theorem radial_integrable {L : Submodule ℤ (mixedSpace K)}
    (x : {x : L // x ≠ 0}) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) *
      archGaussian (K := K) (fun _ ↦ t) (x : L)) (Ioi 0) := by
  simp_rw [archGaussian_const]
  exact mellinConvergent_exp_neg_mul (mul_pos Real.pi_pos (mixedInner_pos x)) hs

private theorem radial_integral {L : Submodule ℤ (mixedSpace K)}
    (x : {x : L // x ≠ 0}) {s : ℂ} (hs : 0 < s.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * archGaussian (K := K) (fun _ ↦ t) (x : L) =
      (π : ℂ) ^ (-s) * Gamma s * (mixedInner K x x : ℂ) ^ (-s) := by
  simp_rw [archGaussian_const, ofReal_exp, ofReal_neg,
    ofReal_mul (π * mixedInner K (x : mixedSpace K) x)]
  rw [integral_cpow_mul_exp_neg_mul_Ioi hs (mul_pos Real.pi_pos (mixedInner_pos x)),
    one_div, inv_cpow_ofReal_nonneg (mul_pos Real.pi_pos (mixedInner_pos x)).le,
    ← cpow_neg, ofReal_mul, ofReal_mul_cpow Real.pi_pos.le]
  ring

/-- The integrals of the norms of the nonzero radial Gaussian Mellin terms are summable.
This is the absolute-integrability bound needed to exchange the lattice sum and integral. -/
theorem summable_integral_norm_radialGaussian (L : Submodule ℤ (mixedSpace K))
    [DiscreteTopology L] {s : ℂ} (hs : (Module.finrank ℤ L : ℝ) / 2 < s.re) :
    Summable fun x : {x : L // x ≠ 0} ↦
      ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) *
        archGaussian (K := K) (fun _ ↦ t) (x : L)‖ := by
  classical
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hsum : Summable fun x : {x : L // x ≠ 0} ↦ mixedInner K x x ^ (-s.re) := by
    simpa only [norm_cpow_eq_rpow_re_of_pos (mixedInner_pos _), neg_re] using
      (summable_epsteinZeta L hs).norm
  refine (hsum.mul_left (π ^ (-s.re) * Real.Gamma s.re)).congr fun x ↦ ?_
  calc
    π ^ (-s.re) * Real.Gamma s.re * mixedInner K x x ^ (-s.re) =
        ∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * Real.exp (-(π * mixedInner K x x * t)) := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs0
        (mul_pos Real.pi_pos (mixedInner_pos x)), one_div,
        Real.inv_rpow (mul_pos Real.pi_pos (mixedInner_pos x)).le,
        ← Real.rpow_neg (mul_pos Real.pi_pos (mixedInner_pos x)).le,
        Real.mul_rpow Real.pi_pos.le (mixedInner_pos x).le]
      ring
    _ = _ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re,
        archGaussian_const, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]

/-- **The radial Mellin transform is Epstein zeta.** The constant term is removed from the
whole theta series. A single radial parameter gives a sum over lattice points, rather than
the unit quotient required for a partial Dedekind zeta function. -/
theorem radialMellin_eq_epsteinZeta (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    {s : ℂ} (hs : (Module.finrank ℤ L : ℝ) / 2 < s.re) :
    mellin (fun t ↦ latticeTheta L (fun _ ↦ t) - 1) s =
      (π : ℂ) ^ (-s) * Gamma s * epsteinZeta L s := by
  classical
  let : Countable L := Countable.of_moduleFinite (R := ℤ)
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  rw [mellin]
  calc
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • (latticeTheta L (fun _ ↦ t) - 1)) =
        ∫ t : ℝ in Ioi 0, ∑' x : {x : L // x ≠ 0},
          (t : ℂ) ^ (s - 1) * archGaussian (K := K) (fun _ ↦ t) (x : L) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      rw [latticeTheta_eq_one_add L _ (fun _ ↦ ht), add_sub_cancel_left,
        smul_eq_mul, tsum_mul_left]
    _ = ∑' x : {x : L // x ≠ 0}, ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) * archGaussian (K := K) (fun _ ↦ t) (x : L) :=
      (integral_tsum_of_summable_integral_norm
        (fun x : {x : L // x ≠ 0} ↦ radial_integrable x hs0)
        (summable_integral_norm_radialGaussian L hs)).symm
    _ = _ := by
      simp_rw [radial_integral _ hs0]
      rw [epsteinZeta_def, tsum_mul_left]

end TauCeti.LFunctions
