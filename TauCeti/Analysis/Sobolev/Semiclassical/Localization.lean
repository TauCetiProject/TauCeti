/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.UniformlyLocal
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Analysis.Calculus.BumpFunction.Translates
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Localizing semiclassical Sobolev norms over covers by `h`-balls

Let `E` be a finite-dimensional real inner product space of dimension `n`, `h > 0` a length scale
and `η` a real cutoff on `E`. For centres `x a ∈ E`, indexed by a finite set `s`, the localization
of a function `f` about `x a` is `y ↦ η (h⁻¹ • (y - x a)) • f y`. This file compares the
semiclassical Sobolev norm `‖f‖_{k,h}` (`TauCeti.semiclassicalSobolevNorm`) with the norms of
these localizations, when the rescaled cutoffs have **bounded overlap**: every point `y` lies in
the support of at most `K` of them, `#{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K`. All constants
depend only on `k`, `K` and a bound `B` for the derivatives of the cutoffs through order `k`; they
are independent of `h`, of the number and position of the centres, and of `f`.

* **Upper bound.** If `‖Dⁱ η‖ ≤ B` for `i ≤ k`, then
  `∑_{a ∈ s} ‖η (h⁻¹ • (· - x a)) f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ‖f‖²_{k,h}`
  (`TauCeti.sum_sq_semiclassicalSobolevNorm_localization_le`).
* **Lower bound.** If moreover `η` is compactly supported, `ψ` is a second cutoff with
  `‖Dⁱ ψ‖ ≤ B` for `i ≤ k`, and `∑_{a ∈ s} ψ (h⁻¹ • (y - x a)) η (h⁻¹ • (y - x a)) = 1` wherever
  `f y ≠ 0`, then
  `‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ∑_{a ∈ s} ‖η (h⁻¹ • (· - x a)) f‖²_{k,h}`
  (`TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_localization`).

So the squared norm of a function is comparable, uniformly in `h`, to the sum of the squared norms
of its localizations over a bounded-overlap cover of its support by balls of radius comparable to
`h`. The uniformly local norm `‖f‖_{k,h,η} = sup_x ‖η (h⁻¹ • (· - x)) f‖_{k,h}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm`) keeps only the largest of these localizations.
It is bounded by the global norm, `‖f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm`), and conversely
the lower bound recovers the global norm from it up to the number of balls,
`‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K #s ‖f‖²_{k,h,η}`
(`TauCeti.sq_semiclassicalSobolevNorm_le_mul_card_mul_sq_uniformlyLocalSemiclassicalSobolevNorm`).
This is the total mass that the supremum alone does not see. In Taubes's large-parameter analysis
of the Seiberg–Witten equations near a pseudoholomorphic curve, at the scale `h = (2r)^(-1/2)`, the
recovery norms combine the supremum over `h`-balls with a global norm for this reason.

Both bounds are pointwise estimates of the scaled jet `∑_{i ≤ k} hⁱ ‖Dⁱ g (y)‖`, integrated. The
square of its `L²` norm is comparable to `hⁿ ‖g‖²_{k,h}` with constant `k + 1` in both directions.
By the Leibniz rule in scaled units (`ContDiff.pow_mul_norm_iteratedFDeriv_smul_le_of_le_left`),
the scaled jet of a localization is at most `(k + 1) 2ᵏ B` times that of `f`, and it vanishes off
the support of the rescaled cutoff. For the upper bound, summing the squares over `a` counts each
point at most `K` times. For the lower bound, `f = ∑_{a ∈ s} ψ (h⁻¹ • (· - x a)) • (η (h⁻¹ •
(· - x a)) • f)`, and at each point at most `K` of the terms are nonzero, so the square of the sum
is at most `K` times the sum of the squares.

## Main results

* `TauCeti.sum_sq_semiclassicalSobolevNorm_localization_le`: the localizations over a
  bounded-overlap family of `h`-balls are square-summable, with the bound above.
* `TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_localization`: conversely, the localizations over
  a bounded-overlap partition of unity control the global norm.
* `TauCeti.uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm`: the uniformly
  local norm is bounded by the global norm.
* `TauCeti.sq_semiclassicalSobolevNorm_le_mul_card_mul_sq_uniformlyLocalSemiclassicalSobolevNorm`:
  the global norm is bounded by the uniformly local norm times the square root of the number of
  balls.

## References

* T. Kato, *The Cauchy problem for quasi-linear symmetric hyperbolic systems*, Arch. Rational
  Mech. Anal. 58 (1975), 181–205 (uniformly local Sobolev spaces).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set
open scoped Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {h : ℝ} {η ψ : E → ℝ} {f : E → F}

/-! ### The squared norm and the scaled jet -/

/-- The square of the semiclassical norm, `‖g‖²_{k,h} = h⁻ⁿ (∑_{i ≤ k} hⁱ ‖Dⁱ g‖₂)²`. -/
private theorem sq_semiclassicalSobolevNorm (hh : 0 < h) (g : E → F) :
    semiclassicalSobolevNorm k h g ^ 2 = h ^ (-(finrank ℝ E : ℝ)) *
      (∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i g) 2 volume) ^ 2 := by
  rw [semiclassicalSobolevNorm_def, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
  norm_num

/-- The square of a weighted `L²` norm of a derivative is the integral of the square of the
weighted pointwise norm. -/
private theorem sq_pow_mul_lpNorm_iteratedFDeriv {g : E → F} {i : ℕ}
    (hm : MemLp (iteratedFDeriv ℝ i g) 2) (h : ℝ) :
    (h ^ i * lpNorm (iteratedFDeriv ℝ i g) 2 volume) ^ 2 =
      ∫ y, (h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2 := by
  rw [mul_pow, lpNorm_two_sq_eq_integral_norm_sq hm.aestronglyMeasurable, ← integral_const_mul]
  simp only [mul_pow]

/-- The weighted pointwise norm of a square-integrable derivative is square integrable. -/
private theorem integrable_sq_pow_mul_norm_iteratedFDeriv {g : E → F} {i : ℕ}
    (hm : MemLp (iteratedFDeriv ℝ i g) 2) (h : ℝ) :
    Integrable fun y ↦ (h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2 :=
  (hm.norm.const_mul (h ^ i)).integrable_sq

/-- The square of the scaled jet `y ↦ ∑_{i ≤ k} hⁱ ‖Dⁱ g y‖` of a function with square-integrable
derivatives through order `k` is integrable. -/
private theorem integrable_sq_sum_pow_mul_norm_iteratedFDeriv {g : E → F}
    (hm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) (h : ℝ) :
    Integrable fun y ↦ (∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2 :=
  (memLp_finsetSum _ fun i hi ↦
    ((hm i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).norm.const_mul (h ^ i))).integrable_sq

/-- The squared semiclassical norm is at most `k + 1` times `h⁻ⁿ` times the integral of the
square of the scaled jet. -/
private theorem sq_semiclassicalSobolevNorm_le_integral {g : E → F}
    (hm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) (hh : 0 < h) :
    semiclassicalSobolevNorm k h g ^ 2 ≤ (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) *
      ∫ y, (∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2) := by
  have hm' (i) (hi : i ∈ Finset.range (k + 1)) := hm i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [sq_semiclassicalSobolevNorm hh, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh.le _)
  refine (sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1))).trans ?_
  rw [Finset.card_range, Nat.cast_add_one]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_congr rfl fun i hi ↦ sq_pow_mul_lpNorm_iteratedFDeriv (hm' i hi) h,
    ← integral_finsetSum _ fun i hi ↦ integrable_sq_pow_mul_norm_iteratedFDeriv (hm' i hi) h]
  exact integral_mono (integrable_finsetSum _ fun i hi ↦
    integrable_sq_pow_mul_norm_iteratedFDeriv (hm' i hi) h)
    (integrable_sq_sum_pow_mul_norm_iteratedFDeriv hm h)
    fun y ↦ Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ by positivity

/-- `h⁻ⁿ` times the integral of the square of the scaled jet is at most `k + 1` times the squared
semiclassical norm. -/
private theorem integral_le_sq_semiclassicalSobolevNorm {g : E → F}
    (hm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) (hh : 0 < h) :
    h ^ (-(finrank ℝ E : ℝ)) *
        ∫ y, (∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2 ≤
      (k + 1) * semiclassicalSobolevNorm k h g ^ 2 := by
  have hm' (i) (hi : i ∈ Finset.range (k + 1)) := hm i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [sq_semiclassicalSobolevNorm hh, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh.le _)
  calc ∫ y, (∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2
      ≤ ∫ y, (k + 1 : ℝ) * ∑ i ∈ Finset.range (k + 1), (h ^ i * ‖iteratedFDeriv ℝ i g y‖) ^ 2 := by
        refine integral_mono (integrable_sq_sum_pow_mul_norm_iteratedFDeriv hm h)
          ((integrable_finsetSum _ fun i hi ↦
            integrable_sq_pow_mul_norm_iteratedFDeriv (hm' i hi) h).const_mul _) fun y ↦ ?_
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1))
          (f := fun i ↦ h ^ i * ‖iteratedFDeriv ℝ i g y‖)
    _ = (k + 1) * ∑ i ∈ Finset.range (k + 1),
          (h ^ i * lpNorm (iteratedFDeriv ℝ i g) 2 volume) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun i hi ↦
          integrable_sq_pow_mul_norm_iteratedFDeriv (hm' i hi) h,
          Finset.sum_congr rfl fun i hi ↦ sq_pow_mul_lpNorm_iteratedFDeriv (hm' i hi) h]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦
          mul_nonneg (pow_nonneg hh.le i) lpNorm_nonneg) (by positivity)

/-! ### The scaled jet of a localization -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A cutoff with `‖Dⁱ η‖ ≤ B` for `i ≤ k`, placed at scale `h > 0` about any centre, has the
semiclassical bounds `hⁱ ‖Dⁱ (η (h⁻¹ • (· - x)))‖ ≤ B`. -/
private theorem pow_mul_norm_iteratedFDeriv_cutoff_le {B : ℝ}
    (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i η z‖ ≤ B) (hh : 0 < h) (x : E) :
    ∀ i ≤ k, ∀ y, h ^ i * ‖iteratedFDeriv ℝ i (fun z ↦ η (h⁻¹ • (z - x))) y‖ ≤ B := by
  intro i hi y
  rw [iteratedFDeriv_comp_sub (f := fun w ↦ η (h⁻¹ • w)), norm_iteratedFDeriv_comp_const_smul,
    norm_inv, Real.norm_of_nonneg hh.le, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hh.ne', one_pow,
    one_mul]
  exact hB i hi _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The scaled jet of a localization is at most `(k + 1) 2ᵏ B` times the scaled jet of the
function. -/
private theorem sum_pow_mul_norm_iteratedFDeriv_localization_le (hη : ContDiff ℝ k η) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i η z‖ ≤ B) (hf : ContDiff ℝ k f) (hh : 0 < h)
    (x y : E) :
    ∑ i ∈ Finset.range (k + 1), h ^ i *
        ‖iteratedFDeriv ℝ i (fun z ↦ η (h⁻¹ • (z - x)) • f z) y‖ ≤
      (k + 1) * 2 ^ k * B *
        ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖ := by
  calc _ ≤ ∑ _i ∈ Finset.range (k + 1), 2 ^ k * B *
        ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖ :=
        Finset.sum_le_sum fun i hi ↦
          (hη.comp_inv_smul_sub h x).pow_mul_norm_iteratedFDeriv_smul_le_of_le_left hf hh.le
            (pow_mul_norm_iteratedFDeriv_cutoff_le hB hh x)
            (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) y
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]
        ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivatives of a localization vanish at the points `y` with `h⁻¹ • (y - x)` outside the
support of the cutoff. -/
private theorem iteratedFDeriv_localization_eq_zero {x y : E} (hy : h⁻¹ • (y - x) ∉ tsupport η)
    (i : ℕ) : iteratedFDeriv ℝ i (fun z ↦ η (h⁻¹ • (z - x)) • f z) y = 0 := by
  by_contra hne
  exact hy (tsupport_comp_subset_preimage η (f := fun z ↦ h⁻¹ • (z - x)) (by fun_prop)
    (tsupport_smul_subset_left _ f (support_iteratedFDeriv_subset i hne)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The scaled jet of a localization vanishes at the points `y` with `h⁻¹ • (y - x)` outside the
support of the cutoff. -/
private theorem sum_pow_mul_norm_iteratedFDeriv_localization_eq_zero {x y : E}
    (hy : h⁻¹ • (y - x) ∉ tsupport η) :
    ∑ i ∈ Finset.range (k + 1), h ^ i *
      ‖iteratedFDeriv ℝ i (fun z ↦ η (h⁻¹ • (z - x)) • f z) y‖ = 0 := by
  simp [iteratedFDeriv_localization_eq_zero hy]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- With bounded overlap, a sum over the centres of a nonnegative quantity vanishing off the
supports of the rescaled cutoffs is a sum over at most `K` centres. -/
private theorem sum_le_mul_of_card_le {ι : Type*} {s : Finset ι} {x : ι → E} {K : ℕ}
    (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (y : E) {u : ι → ℝ} {M : ℝ}
    (hu : ∀ a ∈ s, h⁻¹ • (y - x a) ∉ tsupport η → u a = 0) (huM : ∀ a ∈ s, u a ≤ M)
    (hM : 0 ≤ M) : ∑ a ∈ s, u a ≤ K * M := by
  rw [← Finset.sum_filter_of_ne fun a ha hne ↦ by_contra fun hy ↦ hne (hu a ha hy)]
  calc _ ≤ ∑ a ∈ s with h⁻¹ • (y - x a) ∈ tsupport η, M :=
        Finset.sum_le_sum fun a ha ↦ huM a (Finset.mem_filter.1 ha).1
    _ ≤ K * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK y) hM

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- With bounded overlap, the square of a sum over the centres of a quantity vanishing off the
supports of the rescaled cutoffs is at most `K` times the sum of the squares. -/
private theorem sq_sum_le_mul_sum_sq_of_card_le {ι : Type*} {s : Finset ι} {x : ι → E} {K : ℕ}
    (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (y : E) {u : ι → ℝ}
    (hu : ∀ a ∈ s, h⁻¹ • (y - x a) ∉ tsupport η → u a = 0) :
    (∑ a ∈ s, u a) ^ 2 ≤ K * ∑ a ∈ s, u a ^ 2 := by
  have hfil (v : ι → ℝ) (hv : ∀ a ∈ s, h⁻¹ • (y - x a) ∉ tsupport η → v a = 0) :
      ∑ a ∈ s with h⁻¹ • (y - x a) ∈ tsupport η, v a = ∑ a ∈ s, v a :=
    Finset.sum_filter_of_ne fun a ha hne ↦ by_contra fun hy ↦ hne (hv a ha hy)
  rw [← hfil u hu, ← hfil (u · ^ 2) fun a ha hy ↦ by rw [hu a ha hy, zero_pow two_ne_zero]]
  exact sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hK y)
    (Finset.sum_nonneg fun a _ ↦ sq_nonneg _))

/-! ### Square-summability of the localizations -/

open Classical in
/-- **The localizations over a bounded-overlap family of `h`-balls are square-summable.** Let
`η` be a cutoff of class `Cᵏ` with `‖Dⁱ η‖ ≤ B` for `i ≤ k`, and let `x a`, `a ∈ s`, be centres
such that every point lies in the support of at most `K` of the rescaled cutoffs
`η (h⁻¹ • (· - x a))`. For `h > 0` and `f` of class `Cᵏ` with square-integrable derivatives
through order `k`,

`∑_{a ∈ s} ‖η (h⁻¹ • (· - x a)) f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ‖f‖²_{k,h}`.

The constant is independent of `h`, of the centres and of their number. -/
theorem sum_sq_semiclassicalSobolevNorm_localization_le {ι : Type*} (s : Finset ι) (x : ι → E)
    {K : ℕ} (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (hη : ContDiff ℝ k η)
    {B : ℝ} (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i η z‖ ≤ B) (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hh : 0 < h) :
    ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x a)) • f y) ^ 2 ≤
      (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K * semiclassicalSobolevNorm k h f ^ 2 := by
  -- The scaled jets of `f` and of its localizations `g a`.
  set W : E → ℝ := fun y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖
  set V : ι → E → ℝ := fun a y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i *
    ‖iteratedFDeriv ℝ i (fun z ↦ η (h⁻¹ • (z - x a)) • f z) y‖
  set c : ℝ := (k + 1) * 2 ^ k * B with hcdef
  have hgm (a : ι) := (semiclassicalSobolevNorm_smul_le_of_le_left (hη.comp_inv_smul_sub h (x a))
    hf hfm hh (pow_mul_norm_iteratedFDeriv_cutoff_le hB hh (x a))).1
  -- Pointwise, the squares of the scaled jets of the localizations sum to at most `K c² W²`.
  have hpt (y : E) : ∑ a ∈ s, V a y ^ 2 ≤ K * (c ^ 2 * W y ^ 2) :=
    sum_le_mul_of_card_le hK y
      (fun a _ hy ↦ by simp [V, sum_pow_mul_norm_iteratedFDeriv_localization_eq_zero hy])
      (fun a _ ↦ by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity)
          (sum_pow_mul_norm_iteratedFDeriv_localization_le hη hB hf hh (x a) y) 2)
      (by positivity)
  have hint : ∑ a ∈ s, ∫ y, V a y ^ 2 ≤ K * c ^ 2 * ∫ y, W y ^ 2 := by
    rw [← integral_finsetSum _ fun a _ ↦ integrable_sq_sum_pow_mul_norm_iteratedFDeriv (hgm a) h,
      mul_assoc, ← integral_const_mul, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun a _ ↦
      integrable_sq_sum_pow_mul_norm_iteratedFDeriv (hgm a) h)
      (((integrable_sq_sum_pow_mul_norm_iteratedFDeriv hfm h).const_mul _).const_mul _) hpt
  calc ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x a)) • f y) ^ 2
      ≤ ∑ a ∈ s, (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) * ∫ y, V a y ^ 2) :=
        Finset.sum_le_sum fun a _ ↦ sq_semiclassicalSobolevNorm_le_integral (hgm a) hh
    _ = (k + 1) * h ^ (-(finrank ℝ E : ℝ)) * ∑ a ∈ s, ∫ y, V a y ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ (k + 1) * h ^ (-(finrank ℝ E : ℝ)) * (K * c ^ 2 * ∫ y, W y ^ 2) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (k + 1) * K * c ^ 2 * (h ^ (-(finrank ℝ E : ℝ)) * ∫ y, W y ^ 2) := by ring
    _ ≤ (k + 1) * K * c ^ 2 * ((k + 1) * semiclassicalSobolevNorm k h f ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_le_sq_semiclassicalSobolevNorm hfm hh)
          (by positivity)
    _ = _ := by
        rw [hcdef, show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring

/-! ### Recovering the norm from the localizations -/

/-- A function equal to the sum of its localizations against a second family of cutoffs has
square-integrable derivatives, when the first cutoff is compactly supported. -/
private theorem localization_decomposition {ι : Type*} (s : Finset ι) (x : ι → E)
    (hηc : HasCompactSupport η) (hf : ContDiff ℝ k f)
    (hpart : ∀ y ∈ Function.support f, ∑ a ∈ s, ψ (h⁻¹ • (y - x a)) * η (h⁻¹ • (y - x a)) = 1)
    (hh : h ≠ 0) :
    f = (fun y ↦ ∑ a ∈ s, ψ (h⁻¹ • (y - x a)) • η (h⁻¹ • (y - x a)) • f y) ∧
      ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2 := by
  have hdec : f = (fun y ↦ ∑ a ∈ s, ψ (h⁻¹ • (y - x a)) • η (h⁻¹ • (y - x a)) • f y) := by
    ext y
    by_cases hy : f y = 0
    · simp [hy]
    · simp_rw [smul_smul, ← Finset.sum_smul, hpart y (Function.mem_support.2 hy), one_smul]
  refine ⟨hdec, fun i hi ↦ ?_⟩
  -- Each term of the decomposition is compactly supported.
  set u : ι → E → F := fun a y ↦ ψ (h⁻¹ • (y - x a)) • η (h⁻¹ • (y - x a)) • f y
  have huc (a : ι) : HasCompactSupport (u a) :=
    HasCompactSupport.smul_left (HasCompactSupport.smul_right (hηc.comp_inv_smul_sub hh (x a)))
  -- Hence `f` vanishes off the compact union of their supports.
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (s.isCompact_biUnion fun a _ ↦ huc a) fun y hy ↦ ?_
    rw [congrFun hdec y]
    exact Finset.sum_eq_zero fun a ha ↦
      image_eq_zero_of_notMem_tsupport (f := u a) fun hya ↦ hy (Set.mem_biUnion ha hya)
  exact hf.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hi) hfc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `f = ∑_{a ∈ s} ψ (h⁻¹ • (· - x a)) • g a` with `‖Dⁱ ψ‖ ≤ B` for `i ≤ k`, the scaled jet of
`f` is at most `(k + 1) 2ᵏ B` times the sum of the scaled jets of the `g a`. -/
private theorem sum_pow_mul_norm_iteratedFDeriv_le_sum {ι : Type*} (s : Finset ι) (x : ι → E)
    {g : ι → E → F} (hψ : ContDiff ℝ k ψ) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ B) (hg : ∀ a, ContDiff ℝ k (g a))
    (hdec : f = fun z ↦ ∑ a ∈ s, ψ (h⁻¹ • (z - x a)) • g a z) (hh : 0 < h) (y : E) :
    ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖ ≤
      (k + 1) * 2 ^ k * B *
        ∑ a ∈ s, ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i (g a) y‖ := by
  have hD (i : ℕ) (hi : i ≤ k) : iteratedFDeriv ℝ i f y =
      ∑ a ∈ s, iteratedFDeriv ℝ i (fun z ↦ ψ (h⁻¹ • (z - x a)) • g a z) y := by
    rw [hdec]
    exact iteratedFDeriv_fun_sum_apply fun a _ ↦
      (((hψ.comp_inv_smul_sub h (x a)).smul (hg a)).of_le (by exact_mod_cast hi)).contDiffAt
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ a ∈ s, h ^ i *
        ‖iteratedFDeriv ℝ i (fun z ↦ ψ (h⁻¹ • (z - x a)) • g a z) y‖ := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [hD i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hh.le i)
    _ = ∑ a ∈ s, ∑ i ∈ Finset.range (k + 1), h ^ i *
        ‖iteratedFDeriv ℝ i (fun z ↦ ψ (h⁻¹ • (z - x a)) • g a z) y‖ := Finset.sum_comm
    _ ≤ ∑ a ∈ s, (k + 1) * 2 ^ k * B *
        ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i (g a) y‖ :=
        Finset.sum_le_sum fun a _ ↦
          sum_pow_mul_norm_iteratedFDeriv_localization_le hψ hB (hg a) hh (x a) y
    _ = _ := (Finset.mul_sum ..).symm

open Classical in
/-- **The localizations over a bounded-overlap partition of unity control the norm.** Let `η` be a
compactly supported cutoff of class `Cᵏ` and `ψ` a cutoff of class `Cᵏ` with `‖Dⁱ ψ‖ ≤ B` for
`i ≤ k`. Let `x a`, `a ∈ s`, be centres such that every point lies in the support of at most `K`
of the rescaled cutoffs `η (h⁻¹ • (· - x a))`, and let `f` be of class `Cᵏ` with
`∑_{a ∈ s} ψ (h⁻¹ • (y - x a)) η (h⁻¹ • (y - x a)) = 1` wherever `f y ≠ 0`. Then for `h > 0`

`‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ∑_{a ∈ s} ‖η (h⁻¹ • (· - x a)) f‖²_{k,h}`.

The constant is independent of `h`, of the centres and of their number. -/
theorem sq_semiclassicalSobolevNorm_le_sum_sq_localization {ι : Type*} (s : Finset ι) (x : ι → E)
    {K : ℕ} (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hψ : ContDiff ℝ k ψ) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ B) (hf : ContDiff ℝ k f)
    (hpart : ∀ y ∈ Function.support f, ∑ a ∈ s, ψ (h⁻¹ • (y - x a)) * η (h⁻¹ • (y - x a)) = 1)
    (hh : 0 < h) :
    semiclassicalSobolevNorm k h f ^ 2 ≤ (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K *
      ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x a)) • f y) ^ 2 := by
  -- The localizations `g a` of `f`, and the scaled jets of `f` and of the `g a`.
  set g : ι → E → F := fun a y ↦ η (h⁻¹ • (y - x a)) • f y
  set W : E → ℝ := fun y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖
  set V : ι → E → ℝ := fun a y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i *
    ‖iteratedFDeriv ℝ i (g a) y‖
  set c : ℝ := (k + 1) * 2 ^ k * B with hcdef
  obtain ⟨hdec, hfm⟩ := localization_decomposition s x hηc hf hpart hh.ne'
  have hg (a : ι) : ContDiff ℝ k (g a) := (hη.comp_inv_smul_sub h (x a)).smul hf
  have hgm (a : ι) (i : ℕ) (hi : i ≤ k) : MemLp (iteratedFDeriv ℝ i (g a)) 2 :=
    (hg a).memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hi)
      (hηc.comp_inv_smul_sub hh.ne' (x a)).smul_right
  -- Pointwise, `W ≤ c ∑ₐ V a`, a sum with at most `K` nonzero terms, so `W² ≤ c² K ∑ₐ (V a)²`.
  have hW (y : E) : W y ≤ c * ∑ a ∈ s, V a y :=
    sum_pow_mul_norm_iteratedFDeriv_le_sum s x hψ hB hg hdec hh y
  have hpt (y : E) : W y ^ 2 ≤ c ^ 2 * (K * ∑ a ∈ s, V a y ^ 2) :=
    calc W y ^ 2 ≤ (c * ∑ a ∈ s, V a y) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun i _ ↦ by positivity) (hW y) 2
      _ = c ^ 2 * (∑ a ∈ s, V a y) ^ 2 := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_sum_le_mul_sum_sq_of_card_le hK y fun a _ hy ↦
          sum_pow_mul_norm_iteratedFDeriv_localization_eq_zero hy) (by positivity)
  have hint : ∫ y, W y ^ 2 ≤ c ^ 2 * (K * ∑ a ∈ s, ∫ y, V a y ^ 2) := by
    have hVi (a : ι) := integrable_sq_sum_pow_mul_norm_iteratedFDeriv (hgm a) h
    rw [← integral_finsetSum _ fun a _ ↦ hVi a, ← integral_const_mul, ← integral_const_mul]
    exact integral_mono (integrable_sq_sum_pow_mul_norm_iteratedFDeriv hfm h)
      (((integrable_finsetSum _ fun a _ ↦ hVi a).const_mul _).const_mul _) hpt
  calc semiclassicalSobolevNorm k h f ^ 2
      ≤ (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) * ∫ y, W y ^ 2) :=
        sq_semiclassicalSobolevNorm_le_integral hfm hh
    _ ≤ (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) * (c ^ 2 * (K * ∑ a ∈ s, ∫ y, V a y ^ 2))) := by
        gcongr
    _ = (k + 1) * c ^ 2 * K * ∑ a ∈ s, h ^ (-(finrank ℝ E : ℝ)) * ∫ y, V a y ^ 2 := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ (k + 1) * c ^ 2 * K * ∑ a ∈ s, (k + 1) * semiclassicalSobolevNorm k h (g a) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ ↦
          integral_le_sq_semiclassicalSobolevNorm (hgm a) hh) (by positivity)
    _ = _ := by
        rw [← Finset.mul_sum, hcdef,
          show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring

/-! ### Comparison with the uniformly local norm -/

/-- **The uniformly local norm is bounded by the global norm.** Let `η` be a cutoff of class `Cᵏ`
with `‖Dⁱ η‖ ≤ B` for `i ≤ k`. For `h > 0` and `f` of class `Cᵏ` with square-integrable
derivatives through order `k`, the localizations of `f` are bounded above and

`‖f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h}`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm
    (hη : ContDiff ℝ k η) {B : ℝ} (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i η z‖ ≤ B)
    (hf : ContDiff ℝ k f) (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hh : 0 < h) :
    BddAbove (range fun x ↦ semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) ∧
      uniformlyLocalSemiclassicalSobolevNorm k h η f ≤
        (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k h f := by
  have hle (x : E) : semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • f y) ≤
      (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k h f :=
    (semiclassicalSobolevNorm_smul_le_of_le_left (hη.comp_inv_smul_sub h x) hf hfm hh
      (pow_mul_norm_iteratedFDeriv_cutoff_le hB hh x)).2
  exact ⟨⟨_, forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

open Classical in
/-- **The global norm from the uniformly local norm and the number of balls.** Under the
hypotheses of `TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_localization`, with `#s` centres,

`‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K #s ‖f‖²_{k,h,η}`.

The uniformly local norm sees each ball separately; the factor `#s` accounts for the total mass
spread over the balls. -/
theorem sq_semiclassicalSobolevNorm_le_mul_card_mul_sq_uniformlyLocalSemiclassicalSobolevNorm
    {ι : Type*} (s : Finset ι) (x : ι → E) {K : ℕ}
    (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hψ : ContDiff ℝ k ψ) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ B) (hf : ContDiff ℝ k f)
    (hpart : ∀ y ∈ Function.support f, ∑ a ∈ s, ψ (h⁻¹ • (y - x a)) * η (h⁻¹ • (y - x a)) = 1)
    (hh : 0 < h) :
    semiclassicalSobolevNorm k h f ^ 2 ≤ (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K * #s *
      uniformlyLocalSemiclassicalSobolevNorm k h η f ^ 2 := by
  obtain ⟨B', -, hB'⟩ := hηc.exists_bound_iteratedFDeriv_of_contDiff hη
  have hb := (uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm hη hB' hf
    (localization_decomposition s x hηc hf hpart hh.ne').2 hh).1
  refine (sq_semiclassicalSobolevNorm_le_sum_sq_localization s x hK hη hηc hψ hB hf hpart
    hh).trans ?_
  rw [mul_assoc _ (#s : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x a)) • f y) ^ 2
      ≤ ∑ _a ∈ s, uniformlyLocalSemiclassicalSobolevNorm k h η f ^ 2 :=
        Finset.sum_le_sum fun a _ ↦ pow_le_pow_left₀ (semiclassicalSobolevNorm_nonneg k hh.le _)
          (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hb (x a)) 2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end TauCeti
