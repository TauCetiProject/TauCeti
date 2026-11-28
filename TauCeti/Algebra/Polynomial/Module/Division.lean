/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Recovering coefficients after scalar polynomial multiplication

If a scalar polynomial has unit constant coefficient, multiplying a module-valued
polynomial by it can be inverted to any finite order. The recovery coefficients come
from the formal power series inverse and are independent of the module.
-/

public section

open Finset
open scoped PowerSeries Polynomial

namespace PolynomialModule

/-- Recover the degree-`n` coefficient of `v` from the coefficients through degree `n`
of `p • v`, using the power series inverse of `p`. No unit hypothesis on the leading
coefficient of `p` is needed. -/
theorem coeff_eq_sum_smul_coeff_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : PolynomialModule R M) (p : R[X]) (u : Rˣ) (hu : p.coeff 0 = u) (n : ℕ) :
    v.coeff n = ∑ j : Fin (n + 1),
      PowerSeries.coeff (n - j.val) (PowerSeries.invOfUnit (p : R⟦X⟧) u) • (p • v).coeff j := by
  let g := PowerSeries.invOfUnit (p : R⟦X⟧) u
  let q := g.trunc (n + 1)
  have hg : g * (p : R⟦X⟧) = 1 :=
    PowerSeries.invOfUnit_mul _ _ (by rwa [Polynomial.constantCoeff_coe])
  have htrunc : (((q * p : R[X]) : R⟦X⟧).trunc (n + 1)) =
      (PowerSeries.trunc (n + 1)) (1 : R⟦X⟧) := by
    rw [Polynomial.coe_mul, PowerSeries.trunc_trunc_mul, hg]
  have hq (j : ℕ) (hj : j ≤ n) : (q * p).coeff j = (1 : R[X]).coeff j := by
    have hj' := Nat.lt_succ_of_le hj
    simpa only [PowerSeries.coeff_trunc, ite_eq_left hj', ← Polynomial.coe_one,
      Polynomial.coeff_coe] using congrArg (fun f : R[X] ↦ f.coeff j) htrunc
  calc
    v.coeff n = ((1 : R[X]) • v).coeff n := by rw [one_smul]
    _ = ((q * p) • v).coeff n := by
      simp only [smul_apply]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [hq j.1 (by have := Finset.mem_antidiagonal.mp hj; omega)]
    _ = (q • (p • v)).coeff n := by rw [mul_smul]
    _ = ∑ j : Fin (n + 1), q.coeff (n - j.val) • (p • v).coeff j := by
      rw [smul_apply, ← Finset.Nat.sum_antidiagonal_swap
        (f := fun j ↦ q.coeff j.1 • (p • v).coeff j.2)]
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ q.coeff j • (p • v).coeff i),
        ← Fin.sum_univ_eq_sum_range]
    _ = _ := sum_congr rfl fun j _ ↦ by
      rw [PowerSeries.coeff_trunc, ite_eq_left (by omega : n - j.val < n + 1)]

end PolynomialModule
