/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Eval
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Taylor translation of entire power series

For a power series `f` over a commutative topological ring and a point `a`, the Taylor translate
`taylor a f` is the series whose `n`-th coefficient is the value `(Δⁿ f)(a)` of the
`n`-th Hasse derivative of `f` at `a`. On polynomials it is `Polynomial.taylor a`, the substitution
`X ↦ X + a`.

For an entire series `f` over a complete normed commutative ring, the translate is again entire and
satisfies the **Taylor identity** `(taylor a f)(b) = f(b + a)`. Writing `f = ∑ cₖ Xᵏ`, both sides
are sums of the absolutely summable double series `∑ₙ,ₘ (n + m).choose n • cₙ₊ₘ aᵐ bⁿ`: grouping
its terms by `n` gives the translate at `b`, and grouping them by `n + m` gives `f` at `b + a` by
the binomial theorem. Since Hasse derivatives commute with translation, translations compose,
`taylor b (taylor a f) = taylor (b + a) f`, so translation by `-a` inverts translation by `a` and
Taylor translation is injective on entire series. No factorial is inverted and no ultrametric
hypothesis is used, so all of this holds in every characteristic and over `ℂ` as well as over
nonarchimedean rings.

Injectivity is what controls the zeros of entire series over a field: a nonzero entire series has a
nonvanishing Hasse derivative at every point, so each of its zeros has a finite order
(`PowerSeries.IsEntire.exists_isGoodZero`).

## Main definitions

* `taylor a f`: the Taylor translate of `f` at `a`, with coefficients `(Δⁿ f)(a)`.

## Main results

* `taylor_coe`: on polynomials, the translate is `Polynomial.taylor`.
* `taylor_zero`: translation by `0` is the identity.
* `PowerSeries.IsEntire.taylor`: the translate of an entire series is entire.
* `PowerSeries.IsEntire.evalAt_taylor`: the Taylor identity `(taylor a f)(b) = f(b + a)`.
* `PowerSeries.IsEntire.hasseDeriv_taylor`: Hasse derivatives commute with translation.
* `PowerSeries.IsEntire.taylor_taylor`: `taylor b (taylor a f) = taylor (b + a) f`.
* `PowerSeries.IsEntire.taylor_inj`, `PowerSeries.IsEntire.taylor_eq_zero_iff`: translation is
  injective on entire series.
-/

public section

namespace PowerSeries

open Filter Finset

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

end Topological

section Normed

variable {R : Type*} [NormedCommRing R] {f : R⟦X⟧}

/-- For an entire series `f = ∑ cₖ Xᵏ` and `t ≥ 0`, the real double series
`∑ₙ,ₘ (n + m).choose n ‖cₙ₊ₘ‖ tⁿ ‖a‖ᵐ` converges: its antidiagonal sums are `‖cₖ‖ (t + ‖a‖)ᵏ`. -/
private theorem summable_taylorMajorant (hf : f.IsEntire) (a : R) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun p : ℕ × ℕ ↦
      (p.1 + p.2).choose p.1 * ‖coeff (p.1 + p.2) f‖ * (t ^ p.1 * ‖a‖ ^ p.2) := by
  rw [← HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  refine (summable_sigma_of_nonneg fun _ ↦ by simp only [Function.comp_apply]; positivity).2
    ⟨fun _ ↦ .of_finite, (hf.summable_norm_coeff_mul_pow (t + ‖a‖)).congr fun k ↦ ?_⟩
  simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (antidiagonal k)
    fun p : ℕ × ℕ ↦ (p.1 + p.2).choose p.1 * ‖coeff (p.1 + p.2) f‖ * (t ^ p.1 * ‖a‖ ^ p.2),
    (Commute.all _ _).add_pow', mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [mem_antidiagonal] at hp
  rw [hp, nsmul_eq_mul]
  ring

/-- The terms `coeff m (Δⁿ f) aᵐ` of `(Δⁿ f)(a)` are bounded by the majorant of
`summable_taylorMajorant`, up to the constant `max ‖1‖ 1`. -/
private theorem norm_coeff_hasseDeriv_mul_pow_le_max (f : R⟦X⟧) (a : R) (n m : ℕ) :
    ‖coeff m (hasseDeriv n f) * a ^ m‖ ≤
      max ‖(1 : R)‖ 1 * ((n + m).choose n * ‖coeff (n + m) f‖ * ‖a‖ ^ m) := by
  rw [coeff_hasseDeriv, add_comm m n, ← nsmul_eq_mul]
  calc ‖(n + m).choose n • coeff (n + m) f * a ^ m‖
      ≤ (n + m).choose n * ‖coeff (n + m) f‖ * (max ‖(1 : R)‖ 1 * ‖a‖ ^ m) :=
        (norm_mul_le _ _).trans (mul_le_mul norm_nsmul_le (TauCeti.norm_pow_le_max_mul a m)
          (norm_nonneg _) (by positivity))
    _ = _ := by ring

section Complete

variable [CompleteSpace R]

/-- **The Taylor identity.** For an entire series `f`, the Taylor translate at `a` evaluated at
`b` is `f(b + a)`. -/
theorem IsEntire.evalAt_taylor (hf : f.IsEntire) (a b : R) :
    (taylor a f).evalAt b = f.evalAt (b + a) := by
  set F : ℕ × ℕ → R := fun p ↦ coeff p.2 (PowerSeries.hasseDeriv p.1 f) * a ^ p.2 * b ^ p.1
  have hF : Summable F := by
    refine Summable.of_norm <| ((summable_taylorMajorant hf a (norm_nonneg b)).mul_left
      (max ‖(1 : R)‖ 1 * max ‖(1 : R)‖ 1)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun p ↦ ?_
    calc ‖F p‖ ≤ ‖coeff p.2 (PowerSeries.hasseDeriv p.1 f) * a ^ p.2‖ * ‖b ^ p.1‖ :=
        norm_mul_le _ _
      _ ≤ max ‖(1 : R)‖ 1 * ((p.1 + p.2).choose p.1 * ‖coeff (p.1 + p.2) f‖ * ‖a‖ ^ p.2) *
          (max ‖(1 : R)‖ 1 * ‖b‖ ^ p.1) :=
        mul_le_mul (norm_coeff_hasseDeriv_mul_pow_le_max f a p.1 p.2)
          (TauCeti.norm_pow_le_max_mul b p.1) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- Grouping the terms by the order `n` of the Hasse derivative gives the translate at `b`.
  have h₁ : HasSum (fun n ↦ coeff n (taylor a f) • b ^ n) (∑' p, F p) :=
    hF.hasSum.prod_fiberwise fun n ↦ by
      simpa only [coeff_taylor, smul_eq_mul] using
        ((hf.hasseDeriv n).hasSum_evalAt a).mul_right (b ^ n)
  -- Grouping them by the total degree `n + m` gives `f` at `b + a`, by the binomial theorem.
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
  rw [evalAt_def, h₁.tsum_eq, (hf.hasSum_evalAt (b + a)).unique h₂]

/-- **Hasse derivatives commute with Taylor translation** of entire series. -/
theorem IsEntire.hasseDeriv_taylor (hf : f.IsEntire) (a : R) (k : ℕ) :
    PowerSeries.hasseDeriv k (taylor a f) = taylor a (PowerSeries.hasseDeriv k f) := by
  ext n
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) n k) f
  rw [LinearMap.comp_apply, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R] at h
  rw [coeff_hasseDeriv, coeff_taylor, coeff_taylor, h, (hf.hasseDeriv _).evalAt_smul,
    smul_eq_mul, Nat.choose_symm_add]

/-- **Taylor translations compose**: for an entire series `f`,
`taylor b (taylor a f) = taylor (b + a) f`. -/
theorem IsEntire.taylor_taylor (hf : f.IsEntire) (a b : R) :
    taylor b (taylor a f) = taylor (b + a) f := by
  ext n
  rw [coeff_taylor, hf.hasseDeriv_taylor, (hf.hasseDeriv n).evalAt_taylor, coeff_taylor]

/-- Translation by `-a` inverts translation by `a` on entire series. -/
theorem IsEntire.taylor_neg_taylor (hf : f.IsEntire) (a : R) :
    taylor (-a) (taylor a f) = f := by
  rw [hf.taylor_taylor, neg_add_cancel, taylor_zero]

/-- **Taylor translation is injective on entire series.** -/
theorem IsEntire.taylor_inj {g : R⟦X⟧} (hf : f.IsEntire) (hg : g.IsEntire) (a : R) :
    taylor a f = taylor a g ↔ f = g :=
  ⟨fun h ↦ by rw [← hf.taylor_neg_taylor a, h, hg.taylor_neg_taylor], fun h ↦ h ▸ rfl⟩

/-- An entire series has zero Taylor translate exactly when it is zero. -/
theorem IsEntire.taylor_eq_zero_iff (hf : f.IsEntire) (a : R) : taylor a f = 0 ↔ f = 0 := by
  simpa using hf.taylor_inj isEntire_zero a

end Complete

/-- **Taylor translates of entire series are entire.** -/
theorem IsEntire.taylor (hf : f.IsEntire) (a : R) : (taylor a f).IsEntire := by
  refine isEntire_iff.2 fun r ↦ ?_
  rw [← isRestricted_abs_iff, isRestricted_iff']
  set M := max ‖(1 : R)‖ 1
  set G : ℕ × ℕ → ℝ := fun p ↦
    (p.1 + p.2).choose p.1 * ‖coeff (p.1 + p.2) f‖ * (|r| ^ p.1 * ‖a‖ ^ p.2)
  have hG := (summable_prod_of_nonneg fun _ ↦ by positivity).1
    (summable_taylorMajorant hf a (abs_nonneg r))
  -- `‖(Δⁿ f)(a)‖ |r|ⁿ` is at most `M` times the `n`-th row sum of the majorant `G`
  refine squeeze_zero (fun _ ↦ by positivity) (fun n ↦ ?_) (hG.2.mul_left M).tendsto_atTop_zero
  have hterm := (hf.hasseDeriv n).summable_norm_smul_pow a
  rw [coeff_taylor, evalAt_def, ← tsum_mul_left]
  calc ‖∑' m, coeff m (PowerSeries.hasseDeriv n f) • a ^ m‖ * |r| ^ n
      ≤ (∑' m, ‖coeff m (PowerSeries.hasseDeriv n f) • a ^ m‖) * |r| ^ n := by
        gcongr
        exact norm_tsum_le_tsum_norm hterm
    _ = ∑' m, ‖coeff m (PowerSeries.hasseDeriv n f) • a ^ m‖ * |r| ^ n :=
        (hterm.tsum_mul_right _).symm
    _ ≤ ∑' m, M * G (n, m) := by
        refine (hterm.mul_right _).tsum_le_tsum (fun m ↦ ?_) ((hG.1 n).mul_left M)
        calc ‖coeff m (PowerSeries.hasseDeriv n f) • a ^ m‖ * |r| ^ n
            ≤ M * ((n + m).choose n * ‖coeff (n + m) f‖ * ‖a‖ ^ m) * |r| ^ n := by
              gcongr
              exact norm_coeff_hasseDeriv_mul_pow_le_max f a n m
          _ = M * G (n, m) := by simp only [G]; ring

end Normed

end PowerSeries
