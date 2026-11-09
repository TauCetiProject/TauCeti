/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Taylor translation of power series

For a power series `f` over a commutative topological ring and a point `a`, the Taylor translate
`taylor a f` is the series whose `n`-th coefficient is the value `(Δⁿ f)(a)` of the
`n`-th Hasse derivative of `f` at `a`. On polynomials it is `Polynomial.taylor a`, the substitution
`X ↦ X + a`.

Writing `f = ∑ cₖ Xᵏ`, both `(taylor a f)(b)` and `f(b + a)` are sums of the double series
`∑ₙ,ₘ (n + m).choose n • cₙ₊ₘ aᵐ bⁿ`: grouping its terms by `n` gives the translate at `b`, and
grouping them by `n + m` gives `f` at `b + a` by the binomial theorem. So the **Taylor identity**
`(taylor a f)(b) = f(b + a)` holds as soon as that double series is summable and its rows converge
to `(Δⁿ f)(a)`. This is shared by the Taylor theories of entire series
(`PowerSeries.IsEntire.evalAt_taylor`) and of restricted series
(`PowerSeries.IsRestricted.evalAt_taylor`), which supply the convergence.

## Main definitions

* `taylor a f`: the Taylor translate of `f` at `a`, with coefficients `(Δⁿ f)(a)`.

## Main results

* `constantCoeff_taylor`: the constant term of the translate is `f(a)`.
* `taylor_coe`: on polynomials, the translate is `Polynomial.taylor`.
* `taylor_zero`: translation by `0` is the identity.
* `taylor_one`: the translate of `1` is `1`.
* `evalAt_taylor_of_summable`: the Taylor identity `(taylor a f)(b) = f(b + a)` for any series
  whose double series at `(a, b)` is summable with rows converging to `(Δⁿ f)(a)`.
* `taylor_add_of_summable_norm`, `taylor_mul_of_summable_norm`: translation is additive and
  multiplicative when all Hasse derivatives have absolutely summable terms at the centre.
-/

public section

namespace PowerSeries

open Finset

section Topological

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- The **Taylor translate** of a power series `f` at `a`: the series `∑ₙ (Δⁿ f)(a) Xⁿ`, whose
coefficients are the values at `a` of the Hasse derivatives of `f`. For an entire series over a
complete normed ring it is the series `f(X + a)` (`PowerSeries.IsEntire.evalAt_taylor`); in
general the values `(Δⁿ f)(a)` are the junk value of `PowerSeries.evalAt` when they diverge. -/
noncomputable def taylor (a : R) (f : R⟦X⟧) : R⟦X⟧ :=
  mk fun n ↦ (hasseDeriv n f).evalAt a

/-- The coefficients of the Taylor translate are the values of the Hasse derivatives. -/
@[simp]
theorem coeff_taylor (a : R) (f : R⟦X⟧) (n : ℕ) :
    coeff n (taylor a f) = (hasseDeriv n f).evalAt a := by
  simp [taylor]

/-- The constant term of the Taylor translate at `a` is the value at `a`. -/
@[simp]
theorem constantCoeff_taylor (a : R) (f : R⟦X⟧) : constantCoeff (taylor a f) = f.evalAt a := by
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- On polynomials, Taylor translation is `Polynomial.taylor`. -/
@[simp]
theorem taylor_coe (a : R) (p : Polynomial R) :
    taylor a (p : R⟦X⟧) = (Polynomial.taylor a p : R⟦X⟧) := by
  ext n
  rw [coeff_taylor, evalAt_hasseDeriv_coe, Polynomial.coeff_coe]

/-- Translation by `0` is the identity. -/
@[simp]
theorem taylor_zero (f : R⟦X⟧) : taylor 0 f = f := by
  ext n
  simp [evalAt_at_zero, ← coeff_zero_eq_constantCoeff_apply]

/-- The translate of the zero series is zero. -/
@[simp]
theorem taylor_zero_right (a : R) : taylor a (0 : R⟦X⟧) = 0 := by
  ext n
  simp

/-- The translate of the constant series `1` is `1`. -/
@[simp]
theorem taylor_one (a : R) : taylor a (1 : R⟦X⟧) = 1 := by
  simpa using taylor_coe a 1

end Topological

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  {f : R⟦X⟧}

/-- **The Taylor identity from the double series.** If the double series
`∑ₙ,ₘ coeff m (Δⁿ f) aᵐ bⁿ` is summable and each of its rows `∑ₘ coeff m (Δⁿ f) aᵐ` converges to
`(Δⁿ f)(a)`, then the Taylor translate at `a` evaluated at `b` is `f(b + a)`. Grouping the terms
by `n` gives the translate at `b`, and grouping them by `n + m` gives `f` at `b + a`, by the
binomial theorem. -/
theorem evalAt_taylor_of_summable {a b : R}
    (hF : Summable fun p : ℕ × ℕ ↦ coeff p.2 (hasseDeriv p.1 f) * a ^ p.2 * b ^ p.1)
    (hrow : ∀ n, HasSum (fun m ↦ coeff m (hasseDeriv n f) • a ^ m) ((hasseDeriv n f).evalAt a)) :
    (taylor a f).evalAt b = f.evalAt (b + a) := by
  set F : ℕ × ℕ → R := fun p ↦ coeff p.2 (hasseDeriv p.1 f) * a ^ p.2 * b ^ p.1
  have h₁ : HasSum (fun n ↦ coeff n (taylor a f) • b ^ n) (∑' p, F p) :=
    hF.hasSum.prod_fiberwise fun n ↦ by
      simpa only [coeff_taylor, smul_eq_mul] using (hrow n).mul_right (b ^ n)
  have h₂ : HasSum (fun k ↦ coeff k f • (b + a) ^ k) (∑' p, F p) := by
    have h := (HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hF.hasSum).sigma
      fun k ↦ hasSum_fintype _
    simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply,
      sum_coe_sort (antidiagonal _) F] at h
    convert h using 2 with k
    rw [(Commute.all _ _).add_pow', smul_eq_mul, mul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [mem_antidiagonal] at hp
    simp only [F, coeff_hasseDeriv, add_comm p.2 p.1, hp, nsmul_eq_mul]
    ring
  rw [evalAt_def, evalAt_def, h₁.tsum_eq, h₂.tsum_eq]

end TopologicalRing

section Complete

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {f : R⟦X⟧}

/-- Taylor translation is additive when all Hasse derivatives have absolutely summable terms
at the translation point. -/
theorem taylor_add_of_summable_norm {g : R⟦X⟧} {a : R}
    (hf : ∀ n, Summable fun m ↦ ‖coeff m (hasseDeriv n f) • a ^ m‖)
    (hg : ∀ n, Summable fun m ↦ ‖coeff m (hasseDeriv n g) • a ^ m‖) :
    taylor a (f + g) = taylor a f + taylor a g := by
  ext n
  simp only [coeff_taylor, map_add, evalAt_add_of_summable_norm (hf n) (hg n)]

/-- Taylor translation is multiplicative when all Hasse derivatives have absolutely summable
terms at the translation point. -/
theorem taylor_mul_of_summable_norm {g : R⟦X⟧} {a : R}
    (hf : ∀ n, Summable fun m ↦ ‖coeff m (hasseDeriv n f) • a ^ m‖)
    (hg : ∀ n, Summable fun m ↦ ‖coeff m (hasseDeriv n g) • a ^ m‖) :
    taylor a (f * g) = taylor a f * taylor a g := by
  have hmul (i j : ℕ) :
      Summable fun m ↦ ‖coeff m (hasseDeriv i f * hasseDeriv j g) • a ^ m‖ := by
    refine (summable_norm_sum_mul_antidiagonal_of_summable_norm (hf i) (hg j)).congr
      fun m ↦ ?_
    apply congrArg norm
    rw [coeff_mul, Finset.sum_smul]
    exact sum_congr rfl fun p hp ↦ by
      rw [← mem_antidiagonal.mp hp, pow_add, smul_mul_smul_comm]
  ext n
  rw [coeff_taylor, hasseDeriv_mul,
    evalAt_sum_of_summable_norm _
      (f := fun p : ℕ × ℕ ↦ hasseDeriv p.1 f * hasseDeriv p.2 g)
      (b := a) (fun p _ ↦ hmul p.1 p.2), coeff_mul]
  exact sum_congr rfl fun p _ ↦ by
    rw [evalAt_mul_of_summable_norm (hf p.1) (hg p.2), coeff_taylor, coeff_taylor]

end Complete

end PowerSeries
