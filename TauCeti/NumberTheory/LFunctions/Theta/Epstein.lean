/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Gaussian
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# The radial Mellin transform and Epstein zeta

For `rank(L) / 2 < Re s`, the Mellin transform of the radial theta series `θ_L(t) − 1`
is `π^(-s) Γ(s)` times the Epstein zeta series of its Euclidean quadratic form. The series
sums over nonzero lattice points, not over ideals or unit orbits. Thus the radial integral
alone is not the integral representation of a partial Dedekind zeta function when the unit
rank is positive.

We use the mixed-space form `mixedInner`, where each complex place counts once. Absolute
convergence of the Epstein series and summability of the integrals of the norms justify
interchanging the lattice sum with the Mellin integral. The zero term is removed from the
whole theta series, rather than subtracting a constant from each summand.

The convergence proof uses Mathlib's `ZLattice.summable_norm_rpow`. The Mellin identity
specializes Mathlib's `hasSum_mellin_pi_mul` for sums of exponentials.

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
  rw [norm_cpow_eq_rpow_re_of_pos (mixedInner_self_pos K hx), neg_re]
  calc
    mixedInner K x x ^ (-s.re) ≤ (‖(x : mixedSpace K)‖ ^ 2) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
        (norm_sq_le_mixedInner_self K _) (by linarith)
    _ = ‖(x : L)‖ ^ (-2 * s.re) := by
      rw [Submodule.norm_coe, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring

/-- For `rank(L) / 2 < Re s`, the Mellin transform of `θ_L(t) − 1` is `π^(-s) Γ(s)` times
Epstein zeta. The constant term is removed from the whole theta series. A single radial
parameter gives a sum over lattice points, rather than the unit quotient required for a
partial Dedekind zeta function. -/
theorem radialMellin_eq_epsteinZeta (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    {s : ℂ} (hs : (Module.finrank ℤ L : ℝ) / 2 < s.re) :
    mellin (fun t ↦ latticeTheta L (fun _ ↦ t) - 1) s =
      (π : ℂ) ^ (-s) * Gamma s * epsteinZeta L s := by
  classical
  let : Countable L := Countable.of_moduleFinite (R := ℤ)
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hF (t : ℝ) (ht : t ∈ Ioi 0) :
      HasSum (fun x : {x : L // x ≠ 0} ↦
        (1 : ℂ) * Real.exp (-π * mixedInner K x x * t))
        (latticeTheta L (fun _ ↦ t) - 1) := by
    rw [latticeTheta_eq_one_add L _ (fun _ ↦ ht), add_sub_cancel_left]
    convert ((summable_archGaussian L _ (fun _ ↦ ht)).subtype (· ≠ 0)).hasSum using 1 <;>
      simp only [Function.comp_def, archGaussian_const, one_mul, mul_assoc, mul_comm t]
  have hsum : Summable fun x : {x : L // x ≠ 0} ↦
      ‖(1 : ℂ)‖ / mixedInner K x x ^ s.re := by
    refine (summable_epsteinZeta L hs).norm.congr fun x ↦ ?_
    rw [norm_cpow_eq_rpow_re_of_pos (mixedInner_self_pos K (by simpa using x.2)),
      neg_re, Real.rpow_neg (mixedInner_self_pos K (by simpa using x.2)).le,
      norm_one, one_div]
  have h := (hasSum_mellin_pi_mul (a := fun _ : {x : L // x ≠ 0} ↦ 1)
    (q := fun x ↦ mixedInner K x x)
    (fun x ↦ Or.inr (mixedInner_self_pos K (by simpa using x.2))) hs0 hF hsum).tsum_eq.symm
  simpa only [epsteinZeta_def, cpow_neg, mul_one, div_eq_mul_inv, tsum_mul_left] using h

end TauCeti.LFunctions
