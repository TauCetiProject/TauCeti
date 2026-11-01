/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Taylor translation of entire power series

For a power series `f` over a commutative topological ring and a point `a`, the **Taylor
translation** `PowerSeries.taylor a f = ∑ₖ (Δᵏ f)(a) Xᵏ` is the series whose coefficients are the
values at `a` of the Hasse derivatives of `f`. On polynomials it is `Polynomial.taylor a`, that is,
substitution of `X + a` for `X` (`PowerSeries.taylor_coe`).

For an entire series `f` over a complete normed commutative ring, the Taylor expansion
`f(b + a) = ∑ₖ (Δᵏ f)(a) bᵏ` converges at every `b` (`PowerSeries.IsEntire.hasSum_taylor`), so
`taylor a f` takes the value `f(b + a)` at `b` (`PowerSeries.IsEntire.evalAt_taylor`). The
translated series is again entire, and translations compose: `taylor r (taylor s f) =
taylor (r + s) f`. Translation by `-a` therefore inverts translation by `a`, and Taylor translation
is injective on entire series (`PowerSeries.IsEntire.taylor_inj`). In particular an entire series
all of whose Hasse derivatives vanish at one point is zero. No ultrametric hypothesis and no
factorial is needed, so this holds in every characteristic and over coefficient rings with
nilpotents.

## Main definitions

* `PowerSeries.taylor a f`: the series `∑ₖ (Δᵏ f)(a) Xᵏ`.

## Main results

* `PowerSeries.coeff_taylor`, `PowerSeries.taylor_coe`, `PowerSeries.taylor_zero`: the
  coefficients, the comparison with `Polynomial.taylor`, and translation by `0`.
* `PowerSeries.IsEntire.hasSum_taylor`, `PowerSeries.IsEntire.evalAt_taylor`: the Taylor
  expansion of an entire series converges, `(taylor a f)(b) = f(b + a)`.
* `PowerSeries.IsEntire.taylor`: Taylor translation preserves entire series.
* `PowerSeries.IsEntire.hasseDeriv_taylor`: Hasse derivatives commute with translation.
* `PowerSeries.IsEntire.taylor_taylor`: `taylor r (taylor s f) = taylor (r + s) f`.
* `PowerSeries.IsEntire.taylor_inj`, `PowerSeries.IsEntire.taylor_eq_zero_iff`: translation is
  injective on entire series.
-/

public section

namespace PowerSeries

open Filter Finset
open scoped Topology

section TopologicalRing

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- The **Taylor translation** `∑ₖ (Δᵏ f)(a) Xᵏ` of a power series `f` at `a`: its coefficients
are the values at `a` of the Hasse derivatives of `f`. For entire `f` over a complete normed ring
this is the expansion of `f(X + a)` (`PowerSeries.IsEntire.evalAt_taylor`); on polynomials it is
`Polynomial.taylor a` (`PowerSeries.taylor_coe`). -/
noncomputable def taylor (a : R) (f : R⟦X⟧) : R⟦X⟧ :=
  mk fun k ↦ (hasseDeriv k f).evalAt a

/-- The `k`-th coefficient of the Taylor translation at `a` is `(Δᵏ f)(a)`. -/
@[simp]
theorem coeff_taylor (a : R) (f : R⟦X⟧) (k : ℕ) :
    coeff k (taylor a f) = (hasseDeriv k f).evalAt a := by
  simp [taylor]

/-- On polynomials, Taylor translation is `Polynomial.taylor`. -/
@[simp]
theorem taylor_coe (a : R) (p : Polynomial R) :
    taylor a (p : R⟦X⟧) = (Polynomial.taylor a p : R⟦X⟧) := by
  ext k
  rw [coeff_taylor, evalAt_hasseDeriv_coe, Polynomial.coeff_coe]

/-- Taylor translation by `0` is the identity. -/
@[simp]
theorem taylor_zero (f : R⟦X⟧) : taylor 0 f = f := by
  ext k
  simp [evalAt_at_zero, ← coeff_zero_eq_constantCoeff_apply]

/-- Taylor translation of the zero series is zero. -/
@[simp]
theorem taylor_zero_right (a : R) : taylor a (0 : R⟦X⟧) = 0 := by
  ext k
  simp [evalAt_zero]

end TopologicalRing

section Normed

variable {R : Type*} [NormedCommRing R] {f : R⟦X⟧}

/-- A bound for norms of powers in a normed ring whose unit may have norm larger than one. -/
private theorem norm_pow_le_max_mul (x : R) (n : ℕ) : ‖x ^ n‖ ≤ max 1 ‖(1 : R)‖ * ‖x‖ ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact (norm_pow_le' x hn).trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))

/-- For an entire `f = ∑ cₙ Xⁿ`, the double series `∑_(k, m) ‖c_(k+m)‖ (k+m choose k) tᵏ sᵐ` of the
binomial expansion of `∑ ‖cₙ‖ (t + s)ⁿ` converges for `t, s ≥ 0`. -/
private theorem IsEntire.summable_norm_coeff_choose_mul (hf : f.IsEntire) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) :
    Summable fun p : ℕ × ℕ ↦
      ‖coeff (p.1 + p.2) f‖ * ((p.1 + p.2).choose p.1 * (t ^ p.1 * s ^ p.2)) := by
  set F : ℕ × ℕ → ℝ := fun p ↦
    ‖coeff (p.1 + p.2) f‖ * ((p.1 + p.2).choose p.1 * (t ^ p.1 * s ^ p.2))
  rw [← (HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff,
    summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply, F]; positivity)]
  refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
  refine (hf.summable_norm_coeff_mul_pow (t + s)).congr fun n ↦ ?_
  simp only [Function.comp_apply, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, tsum_fintype]
  rw [Finset.sum_coe_sort (antidiagonal n) F, (Commute.all t s).add_pow', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  simp only [F, mem_antidiagonal.mp hp, nsmul_eq_mul]

/-- Taylor translation preserves entire series. -/
theorem IsEntire.taylor (hf : f.IsEntire) (a : R) : (PowerSeries.taylor a f).IsEntire := by
  refine isEntire_iff_forall_pos.mpr fun r hr ↦ (isRestricted_iff' _ _).mpr ?_
  set M := max 1 ‖(1 : R)‖
  have hF := hf.summable_norm_coeff_choose_mul hr.le (norm_nonneg a)
  -- `‖(Δᵏ f)(a)‖ rᵏ` is bounded by `M` times the `k`-th row sum of a summable double series.
  refine squeeze_zero (fun _ ↦ by positivity) (fun k ↦ ?_)
    ((hF.prod.mul_left M).tendsto_atTop_zero)
  have hsum := (hf.hasseDeriv k).summable_norm_smul_pow a
  rw [coeff_taylor, evalAt_def]
  refine (mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) (by positivity)).trans ?_
  rw [← tsum_mul_right, ← tsum_mul_left]
  refine (hsum.mul_right _).tsum_le_tsum (fun m ↦ ?_) ((hF.prod_factor k).mul_left M)
  simp only [coeff_hasseDeriv, smul_eq_mul, add_comm m k]
  calc ‖((k + m).choose k : R) * coeff (k + m) f * a ^ m‖ * r ^ k
      ≤ (k + m).choose k * ‖coeff (k + m) f‖ * (M * ‖a‖ ^ m) * r ^ k := by
        gcongr
        refine (norm_mul_le _ _).trans (mul_le_mul ?_ (norm_pow_le_max_mul _ _) (norm_nonneg _)
          (by positivity))
        rw [← nsmul_eq_mul]
        exact norm_nsmul_le
    _ = M * (‖coeff (k + m) f‖ * ((k + m).choose k * (r ^ k * ‖a‖ ^ m))) := by ring

variable [CompleteSpace R]

/-- **Taylor expansion of an entire series.** For an entire series `f` over a complete normed
commutative ring, `f(b + a) = ∑ₖ (Δᵏ f)(a) bᵏ`, the series converging at every `a` and `b`. -/
theorem IsEntire.hasSum_taylor (hf : f.IsEntire) (a b : R) :
    HasSum (fun k ↦ (PowerSeries.hasseDeriv k f).evalAt a * b ^ k) (f.evalAt (b + a)) := by
  -- The binomial expansion of `∑ cₙ (b + a)ⁿ` as a double series over `(k, m)`, `n = k + m`.
  set g : ℕ × ℕ → R := fun p ↦ coeff (p.1 + p.2) f * ((p.1 + p.2).choose p.1 • (b ^ p.1 * a ^ p.2))
  set M := max 1 ‖(1 : R)‖
  have hg : Summable g := by
    refine Summable.of_norm_bounded
      ((hf.summable_norm_coeff_choose_mul (norm_nonneg b) (norm_nonneg a)).mul_left (M * M))
      fun p ↦ ?_
    calc ‖g p‖ ≤ ‖coeff (p.1 + p.2) f‖ * ((p.1 + p.2).choose p.1 * ‖b ^ p.1 * a ^ p.2‖) :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_nsmul_le)
      _ ≤ ‖coeff (p.1 + p.2) f‖ * ((p.1 + p.2).choose p.1 *
            ((M * ‖b‖ ^ p.1) * (M * ‖a‖ ^ p.2))) := by
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul (norm_pow_le_max_mul _ _)
            (norm_pow_le_max_mul _ _) (norm_nonneg _) (by positivity))
      _ = M * M * (‖coeff (p.1 + p.2) f‖ * ((p.1 + p.2).choose p.1 *
            (‖b‖ ^ p.1 * ‖a‖ ^ p.2))) := by ring
  -- Summing over the antidiagonals `k + m = n` gives `∑ cₙ (b + a)ⁿ = f(b + a)`.
  have htot : HasSum g (f.evalAt (b + a)) := by
    set e := HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
    have hσ := (e.summable_iff.mpr hg).hasSum.sigma fun n ↦ hasSum_fintype _
    have hn : (fun n ↦ ∑ y, (g ∘ e) ⟨n, y⟩) = fun n ↦ coeff n f • (b + a) ^ n := by
      funext n
      simp only [Function.comp_apply, e, HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
      rw [Finset.sum_coe_sort (antidiagonal n) g, smul_eq_mul, (Commute.all b a).add_pow',
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      simp only [g, mem_antidiagonal.mp hp]
    rw [hn] at hσ
    rw [← e.hasSum_iff, (hf.hasSum_evalAt (b + a)).unique hσ]
    exact (e.summable_iff.mpr hg).hasSum
  -- Summing first over `m` gives `∑ₖ (Δᵏ f)(a) bᵏ`.
  refine htot.prod_fiberwise fun k ↦ ?_
  refine ((hf.hasseDeriv k).hasSum_evalAt a).mul_right (b ^ k) |>.congr_fun fun m ↦ ?_
  simp only [g, coeff_hasseDeriv, smul_eq_mul, nsmul_eq_mul, add_comm m k]
  ring

/-- **Taylor translation evaluates by translation.** For an entire series `f`,
`(taylor a f)(b) = f(b + a)`. -/
theorem IsEntire.evalAt_taylor (hf : f.IsEntire) (a b : R) :
    (PowerSeries.taylor a f).evalAt b = f.evalAt (b + a) := by
  rw [evalAt_def, ← (hf.hasSum_taylor a b).tsum_eq]
  simp [smul_eq_mul]

/-- Hasse derivatives commute with Taylor translation of entire series:
`Δᵏ (taylor a f) = taylor a (Δᵏ f)`. -/
theorem IsEntire.hasseDeriv_taylor (hf : f.IsEntire) (a : R) (k : ℕ) :
    PowerSeries.hasseDeriv k (PowerSeries.taylor a f) =
      PowerSeries.taylor a (PowerSeries.hasseDeriv k f) := by
  ext n
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) n k) f
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [coeff_hasseDeriv, coeff_taylor, coeff_taylor, h, ← Nat.cast_smul_eq_nsmul R,
    (hf.hasseDeriv _).evalAt_smul, smul_eq_mul, Nat.choose_symm_add]

/-- **Composition of Taylor translations** of an entire series:
`taylor r (taylor s f) = taylor (r + s) f`. -/
theorem IsEntire.taylor_taylor (hf : f.IsEntire) (r s : R) :
    PowerSeries.taylor r (PowerSeries.taylor s f) = PowerSeries.taylor (r + s) f := by
  ext k
  rw [coeff_taylor, hf.hasseDeriv_taylor, (hf.hasseDeriv k).evalAt_taylor, coeff_taylor]

/-- **Taylor translation is injective on entire series.** -/
theorem IsEntire.taylor_inj {g : R⟦X⟧} (hf : f.IsEntire) (hg : g.IsEntire) (a : R) :
    PowerSeries.taylor a f = PowerSeries.taylor a g ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [← taylor_zero f, ← neg_add_cancel a, ← hf.taylor_taylor, h, hg.taylor_taylor,
    neg_add_cancel, taylor_zero]

/-- An entire series is zero exactly when its Taylor translation at some point is zero, that is,
when all of its Hasse derivatives vanish at that point. -/
theorem IsEntire.taylor_eq_zero_iff (hf : f.IsEntire) (a : R) :
    PowerSeries.taylor a f = 0 ↔ f = 0 := by
  simpa using hf.taylor_inj isEntire_zero a

end Normed

end PowerSeries
