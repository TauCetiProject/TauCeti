/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.UniformlyLocal
import TauCeti.Algebra.Order.Chebyshev
import TauCeti.Analysis.Calculus.BumpFunction.Translates
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.Scaling
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp

/-!
# Localizing semiclassical Sobolev norms over covers by `h`-balls

Let `E` be a finite-dimensional real inner product space of dimension `n` and `h > 0` a length
scale. This file compares the semiclassical Sobolev norm `‖f‖_{k,h}`
(`TauCeti.semiclassicalSobolevNorm`) of a function `f` on `E` with the norms of its localizations
`χ a • f` by a finite family of real cutoffs `χ a`, `a ∈ s`, varying on the scale `h`, when the
cutoffs have **bounded overlap**: every point `y` lies in the support of at most `K` of them,
`#{a ∈ s | y ∈ tsupport (χ a)} ≤ K`. All constants depend only on `k`, `K` and a bound `B` for the
semiclassical derivatives `hⁱ ‖Dⁱ ·‖`, `i ≤ k`, of the cutoffs that multiply: the `χ a` in the
upper bound and the second cutoffs `ψ a` in the lower bound. They are independent of `h`, of the
number of cutoffs, and of `f`.

* **Upper bound.** If `hⁱ ‖Dⁱ χ a‖ ≤ B` for `i ≤ k`, then
  `∑_{a ∈ s} ‖χ a • f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ‖f‖²_{k,h}`
  (`TauCeti.sum_sq_semiclassicalSobolevNorm_smul_le`).
* **Lower bound.** If the `χ a` are compactly supported, `ψ a` are second cutoffs with
  `hⁱ ‖Dⁱ ψ a‖ ≤ B` for `i ≤ k`, and `∑_{a ∈ s} ψ a y χ a y = 1` wherever `f y ≠ 0`, then
  `‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ∑_{a ∈ s} ‖χ a • f‖²_{k,h}`
  (`TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_smul`).

The cutoffs may differ from ball to ball, as they do for cutoffs adapted to local charts. The
basic case is a cover by `h`-balls with centres `x a ∈ E` and translates of one rescaled cutoff,
`χ a = η (h⁻¹ • (· - x a))`, where semiclassical derivative bounds become unscaled ones. The
upper bound then assumes `‖Dⁱ η‖ ≤ B` (`TauCeti.sum_sq_semiclassicalSobolevNorm_localization_le`).
The lower bound instead uses the translates `ψ (h⁻¹ • (· - x a))` of a second cutoff `ψ` with
`‖Dⁱ ψ‖ ≤ B` and `∑_{a ∈ s} ψ (h⁻¹ • (y - x a)) η (h⁻¹ • (y - x a)) = 1` wherever `f y ≠ 0`, and
assumes no derivative bound on `η` (`TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_localization`).

So the squared norm of a function is comparable, uniformly in `h`, to the sum of the squared norms
of its localizations over a bounded-overlap cover of its support by balls of radius comparable to
`h`. The uniformly local norm `‖f‖_{k,h,η} = sup_x ‖η (h⁻¹ • (· - x)) f‖_{k,h}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm`) keeps only the largest of these localizations.
If `‖Dⁱ η‖ ≤ B`, it is bounded by the global norm, `‖f‖_{k,h,η} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm`). Conversely,
under the hypotheses of the lower bound, where `B` bounds the derivatives of the second cutoff
`ψ`, it recovers the global norm up to the number of balls,
`‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K #s ‖f‖²_{k,h,η}`
(`TauCeti.sq_semiclassicalSobolevNorm_le_mul_card_mul_sq_uniformlyLocalSemiclassicalSobolevNorm`).
This is the total mass that the supremum alone does not see. In Taubes's large-parameter analysis
of the Seiberg–Witten equations near a pseudoholomorphic curve, at the scale `h = (2r)^(-1/2)`, the
recovery norms combine the supremum over `h`-balls with a global norm for this reason.

Both bounds are pointwise estimates of the scaled jet `∑_{i ≤ k} hⁱ ‖Dⁱ g (y)‖`, integrated: `h⁻ⁿ`
times the integral of its square is comparable to `‖g‖²_{k,h}` with constant `k + 1` in both
directions (`TauCeti.sq_semiclassicalSobolevNorm_le_integral`,
`TauCeti.integral_le_sq_semiclassicalSobolevNorm`). By the Leibniz rule in scaled units
(`ContDiff.pow_mul_norm_iteratedFDeriv_smul_le_of_le_left`), the scaled jet of a localization
`χ a • f` is at most `(k + 1) 2ᵏ B` times that of `f`, and it vanishes off the support of `χ a`.
For the upper bound, summing the squares over `a` counts each point at most `K` times. For the
lower bound, `f = ∑_{a ∈ s} ψ a • (χ a • f)`, and at each point at most `K` of the terms are
nonzero, so the square of the sum is at most `K` times the sum of the squares
(`sq_sum_le_card_filter_ne_zero_mul_sum_sq`).

## Main results

* `TauCeti.sum_sq_semiclassicalSobolevNorm_smul_le`: the localizations over a bounded-overlap
  family of cutoffs are square-summable, with the bound above.
* `TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_smul`: conversely, the localizations over a
  bounded-overlap partition of unity control the global norm.
* `TauCeti.sum_sq_semiclassicalSobolevNorm_localization_le`,
  `TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_localization`: the same bounds for the
  translates of one rescaled cutoff over a cover by `h`-balls.
* `TauCeti.uniformlyLocalSemiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm`: the uniformly
  local norm is bounded by the global norm.
* `TauCeti.sq_semiclassicalSobolevNorm_le_mul_card_mul_sq_uniformlyLocalSemiclassicalSobolevNorm`:
  the global norm is bounded by `(k + 1)² 2ᵏ B √(K #s)` times the uniformly local norm, where `#s`
  is the number of balls and `B` bounds the derivatives of the second cutoff `ψ`.

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

/-! ### The scaled jet of a localization -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- The rescaled cutoffs `η (h⁻¹ • (· - x a))` containing a point `y` in their supports are among
those with `h⁻¹ • (y - x a) ∈ tsupport η`. -/
private theorem card_filter_mem_tsupport_le {ι : Type*} {s : Finset ι} {x : ι → E} {K : ℕ}
    (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (y : E) :
    #{a ∈ s | y ∈ tsupport fun z ↦ η (h⁻¹ • (z - x a))} ≤ K :=
  (Finset.card_le_card (Finset.monotone_filter_right s fun a _ hy ↦
    tsupport_comp_subset_preimage η (f := fun z ↦ h⁻¹ • (z - x a)) (by fun_prop) hy)).trans (hK y)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `χ` has the semiclassical bounds `hⁱ ‖Dⁱ χ‖ ≤ B` for `i ≤ k`, the scaled jet of `χ • g` is
at most `(k + 1) 2ᵏ B` times the scaled jet of `g`. -/
private theorem sum_pow_mul_norm_iteratedFDeriv_smul_le {χ : E → ℝ} {g : E → F}
    (hχ : ContDiff ℝ k χ) {B : ℝ} (hB : ∀ i ≤ k, ∀ y, h ^ i * ‖iteratedFDeriv ℝ i χ y‖ ≤ B)
    (hg : ContDiff ℝ k g) (hh : 0 ≤ h) (y : E) :
    ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i (fun z ↦ χ z • g z) y‖ ≤
      (k + 1) * 2 ^ k * B *
        ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i g y‖ := by
  calc _ ≤ ∑ _i ∈ Finset.range (k + 1), 2 ^ k * B *
        ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i g y‖ :=
        Finset.sum_le_sum fun i hi ↦ hχ.pow_mul_norm_iteratedFDeriv_smul_le_of_le_left hg hh hB
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) y
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]
        ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The scaled jet of `χ • g` vanishes off the support of `χ`. -/
private theorem sum_pow_mul_norm_iteratedFDeriv_smul_eq_zero {χ : E → ℝ} {g : E → F} {y : E}
    (hy : y ∉ tsupport χ) :
    ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i (fun z ↦ χ z • g z) y‖ = 0 := by
  have hD (i : ℕ) : iteratedFDeriv ℝ i (fun z ↦ χ z • g z) y = 0 := by
    by_contra hne
    exact hy (tsupport_smul_subset_left _ g (support_iteratedFDeriv_subset i hne))
  simp [hD]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- With bounded overlap, a sum over the cutoffs of a nonnegative quantity vanishing off their
supports is a sum over at most `K` cutoffs. -/
private theorem sum_le_mul_of_card_le {ι : Type*} {s : Finset ι} {χ : ι → E → ℝ} {K : ℕ}
    (hK : ∀ y, #{a ∈ s | y ∈ tsupport (χ a)} ≤ K) (y : E) {u : ι → ℝ} {M : ℝ}
    (hu : ∀ a ∈ s, y ∉ tsupport (χ a) → u a = 0) (huM : ∀ a ∈ s, u a ≤ M) (hM : 0 ≤ M) :
    ∑ a ∈ s, u a ≤ K * M := by
  rw [← Finset.sum_filter_of_ne fun a ha hne ↦ by_contra fun hy ↦ hne (hu a ha hy)]
  calc _ ≤ ∑ a ∈ s with y ∈ tsupport (χ a), M :=
        Finset.sum_le_sum fun a ha ↦ huM a (Finset.mem_filter.1 ha).1
    _ ≤ K * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK y) hM

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
/-- With bounded overlap, the square of a sum over the cutoffs of a quantity vanishing off their
supports is at most `K` times the sum of the squares. -/
private theorem sq_sum_le_mul_sum_sq_of_card_le {ι : Type*} {s : Finset ι} {χ : ι → E → ℝ}
    {K : ℕ} (hK : ∀ y, #{a ∈ s | y ∈ tsupport (χ a)} ≤ K) (y : E) {u : ι → ℝ}
    (hu : ∀ a ∈ s, y ∉ tsupport (χ a) → u a = 0) :
    (∑ a ∈ s, u a) ^ 2 ≤ K * ∑ a ∈ s, u a ^ 2 := by
  have hcard : #{a ∈ s | u a ≠ 0} ≤ K :=
    (Finset.card_le_card (Finset.monotone_filter_right s fun a ha hne ↦
      by_contra fun hy ↦ hne (hu a ha hy))).trans (hK y)
  exact (sq_sum_le_card_filter_ne_zero_mul_sum_sq s u).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Finset.sum_nonneg fun a _ ↦ sq_nonneg _))

/-! ### Square-summability of the localizations -/

open Classical in
/-- **The localizations over a bounded-overlap family of cutoffs are square-summable.** Let
`χ a`, `a ∈ s`, be cutoffs of class `Cᵏ` with the semiclassical bounds `hⁱ ‖Dⁱ χ a‖ ≤ B` for
`i ≤ k`, such that every point lies in the support of at most `K` of them. For `h > 0` and `f` of
class `Cᵏ` with square-integrable derivatives through order `k`,

`∑_{a ∈ s} ‖χ a • f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ‖f‖²_{k,h}`.

The constant is independent of `h`, of the cutoffs and of their number. -/
theorem sum_sq_semiclassicalSobolevNorm_smul_le {ι : Type*} (s : Finset ι) {χ : ι → E → ℝ}
    {K : ℕ} (hK : ∀ y, #{a ∈ s | y ∈ tsupport (χ a)} ≤ K) (hχ : ∀ a ∈ s, ContDiff ℝ k (χ a))
    {B : ℝ} (hB : ∀ a ∈ s, ∀ i ≤ k, ∀ y, h ^ i * ‖iteratedFDeriv ℝ i (χ a) y‖ ≤ B)
    (hf : ContDiff ℝ k f) (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hh : 0 < h) :
    ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ χ a y • f y) ^ 2 ≤
      (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K * semiclassicalSobolevNorm k h f ^ 2 := by
  -- The scaled jets of `f` and of its localizations `χ a • f`.
  set W : E → ℝ := fun y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖
  set V : ι → E → ℝ := fun a y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i *
    ‖iteratedFDeriv ℝ i (fun z ↦ χ a z • f z) y‖
  set c : ℝ := (k + 1) * 2 ^ k * B with hcdef
  have hgm (a : ι) (ha : a ∈ s) :=
    (semiclassicalSobolevNorm_smul_le_of_le_left (hχ a ha) hf hfm hh (hB a ha)).1
  -- Pointwise, the squares of the scaled jets of the localizations sum to at most `K c² W²`.
  have hpt (y : E) : ∑ a ∈ s, V a y ^ 2 ≤ K * (c ^ 2 * W y ^ 2) :=
    sum_le_mul_of_card_le hK y
      (fun a _ hy ↦ by simp [V, sum_pow_mul_norm_iteratedFDeriv_smul_eq_zero hy])
      (fun a ha ↦ by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity)
          (sum_pow_mul_norm_iteratedFDeriv_smul_le (hχ a ha) (hB a ha) hf hh.le y) 2)
      (by positivity)
  have hint : ∑ a ∈ s, ∫ y, V a y ^ 2 ≤ K * c ^ 2 * ∫ y, W y ^ 2 := by
    rw [← integral_finsetSum _ fun a ha ↦
        integrable_sq_sum_pow_mul_norm_iteratedFDeriv (hgm a ha) h,
      mul_assoc, ← integral_const_mul, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun a ha ↦
      integrable_sq_sum_pow_mul_norm_iteratedFDeriv (hgm a ha) h)
      (((integrable_sq_sum_pow_mul_norm_iteratedFDeriv hfm h).const_mul _).const_mul _) hpt
  calc ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ χ a y • f y) ^ 2
      ≤ ∑ a ∈ s, (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) * ∫ y, V a y ^ 2) :=
        Finset.sum_le_sum fun a ha ↦ sq_semiclassicalSobolevNorm_le_integral (hgm a ha) hh.le
    _ = (k + 1) * h ^ (-(finrank ℝ E : ℝ)) * ∑ a ∈ s, ∫ y, V a y ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ (k + 1) * h ^ (-(finrank ℝ E : ℝ)) * (K * c ^ 2 * ∫ y, W y ^ 2) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (k + 1) * K * c ^ 2 * (h ^ (-(finrank ℝ E : ℝ)) * ∫ y, W y ^ 2) := by ring
    _ ≤ (k + 1) * K * c ^ 2 * ((k + 1) * semiclassicalSobolevNorm k h f ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_le_sq_semiclassicalSobolevNorm hfm hh.le)
          (by positivity)
    _ = _ := by
        rw [hcdef, show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring

open Classical in
/-- **The localizations over a bounded-overlap family of `h`-balls are square-summable.** Let
`η` be a cutoff of class `Cᵏ` with `‖Dⁱ η‖ ≤ B` for `i ≤ k`, and let `x a`, `a ∈ s`, be centres
such that every point lies in the support of at most `K` of the rescaled cutoffs
`η (h⁻¹ • (· - x a))`. For `h > 0` and `f` of class `Cᵏ` with square-integrable derivatives
through order `k`,

`∑_{a ∈ s} ‖η (h⁻¹ • (· - x a)) f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ‖f‖²_{k,h}`.

The constant is independent of `h`, of the centres and of their number. This is
`TauCeti.sum_sq_semiclassicalSobolevNorm_smul_le` for the translates of one rescaled cutoff. -/
theorem sum_sq_semiclassicalSobolevNorm_localization_le {ι : Type*} (s : Finset ι) (x : ι → E)
    {K : ℕ} (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (hη : ContDiff ℝ k η)
    {B : ℝ} (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i η z‖ ≤ B) (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hh : 0 < h) :
    ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x a)) • f y) ^ 2 ≤
      (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K * semiclassicalSobolevNorm k h f ^ 2 :=
  sum_sq_semiclassicalSobolevNorm_smul_le s (χ := fun a z ↦ η (h⁻¹ • (z - x a)))
    (card_filter_mem_tsupport_le hK) (fun a _ ↦ hη.comp_inv_smul_sub h (x a))
    (fun a _ i hi y ↦ (pow_mul_norm_iteratedFDeriv_comp_inv_smul_sub _ hh (x a) i y).trans_le
      (hB i hi _)) hf hfm hh

/-! ### Recovering the norm from the localizations -/

/-- A function equal to the sum of its localizations against a second family of cutoffs has
square-integrable derivatives, when the first cutoffs are compactly supported. -/
private theorem localization_decomposition {ι : Type*} (s : Finset ι) {χ ψ : ι → E → ℝ}
    (hχc : ∀ a ∈ s, HasCompactSupport (χ a)) (hf : ContDiff ℝ k f)
    (hpart : ∀ y ∈ Function.support f, ∑ a ∈ s, ψ a y * χ a y = 1) :
    f = (fun y ↦ ∑ a ∈ s, ψ a y • χ a y • f y) ∧ ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2 := by
  have hdec : f = (fun y ↦ ∑ a ∈ s, ψ a y • χ a y • f y) := by
    ext y
    by_cases hy : f y = 0
    · simp [hy]
    · simp_rw [smul_smul, ← Finset.sum_smul, hpart y (Function.mem_support.2 hy), one_smul]
  refine ⟨hdec, fun i hi ↦ ?_⟩
  -- Each term of the decomposition is compactly supported.
  set u : ι → E → F := fun a y ↦ ψ a y • χ a y • f y
  have huc (a : ι) (ha : a ∈ s) : HasCompactSupport (u a) :=
    HasCompactSupport.smul_left (HasCompactSupport.smul_right (hχc a ha))
  -- Hence `f` vanishes off the compact union of their supports.
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (s.isCompact_biUnion huc) fun y hy ↦ ?_
    rw [congrFun hdec y]
    exact Finset.sum_eq_zero fun a ha ↦
      image_eq_zero_of_notMem_tsupport (f := u a) fun hya ↦ hy (Set.mem_biUnion ha hya)
  exact hf.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hi) hfc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `f = ∑_{a ∈ s} ψ a • g a` with `hⁱ ‖Dⁱ ψ a‖ ≤ B` for `i ≤ k`, the scaled jet of `f` is at
most `(k + 1) 2ᵏ B` times the sum of the scaled jets of the `g a`. -/
private theorem sum_pow_mul_norm_iteratedFDeriv_le_sum {ι : Type*} (s : Finset ι)
    {ψ : ι → E → ℝ} {g : ι → E → F} (hψ : ∀ a ∈ s, ContDiff ℝ k (ψ a)) {B : ℝ}
    (hB : ∀ a ∈ s, ∀ i ≤ k, ∀ y, h ^ i * ‖iteratedFDeriv ℝ i (ψ a) y‖ ≤ B)
    (hg : ∀ a ∈ s, ContDiff ℝ k (g a)) (hdec : f = fun z ↦ ∑ a ∈ s, ψ a z • g a z) (hh : 0 ≤ h)
    (y : E) :
    ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖ ≤
      (k + 1) * 2 ^ k * B *
        ∑ a ∈ s, ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i (g a) y‖ := by
  have hD (i : ℕ) (hi : i ≤ k) : iteratedFDeriv ℝ i f y =
      ∑ a ∈ s, iteratedFDeriv ℝ i (fun z ↦ ψ a z • g a z) y := by
    rw [hdec]
    exact iteratedFDeriv_fun_sum_apply fun a ha ↦
      (((hψ a ha).smul (hg a ha)).of_le (by exact_mod_cast hi)).contDiffAt
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ a ∈ s, h ^ i *
        ‖iteratedFDeriv ℝ i (fun z ↦ ψ a z • g a z) y‖ := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [hD i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hh i)
    _ = ∑ a ∈ s, ∑ i ∈ Finset.range (k + 1), h ^ i *
        ‖iteratedFDeriv ℝ i (fun z ↦ ψ a z • g a z) y‖ := Finset.sum_comm
    _ ≤ ∑ a ∈ s, (k + 1) * 2 ^ k * B *
        ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i (g a) y‖ :=
        Finset.sum_le_sum fun a ha ↦
          sum_pow_mul_norm_iteratedFDeriv_smul_le (hψ a ha) (hB a ha) (hg a ha) hh y
    _ = _ := (Finset.mul_sum ..).symm

open Classical in
/-- **The localizations over a bounded-overlap partition of unity control the norm.** Let `χ a`,
`a ∈ s`, be compactly supported cutoffs of class `Cᵏ` such that every point lies in the support of
at most `K` of them, and let `ψ a` be cutoffs of class `Cᵏ` with the semiclassical bounds
`hⁱ ‖Dⁱ ψ a‖ ≤ B` for `i ≤ k`. Let `f` be of class `Cᵏ` with `∑_{a ∈ s} ψ a y χ a y = 1` wherever
`f y ≠ 0`. Then for `h ≥ 0`

`‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ∑_{a ∈ s} ‖χ a • f‖²_{k,h}`.

The constant is independent of `h`, of the cutoffs and of their number. -/
theorem sq_semiclassicalSobolevNorm_le_sum_sq_smul {ι : Type*} (s : Finset ι)
    {χ ψ : ι → E → ℝ} {K : ℕ} (hK : ∀ y, #{a ∈ s | y ∈ tsupport (χ a)} ≤ K)
    (hχ : ∀ a ∈ s, ContDiff ℝ k (χ a)) (hχc : ∀ a ∈ s, HasCompactSupport (χ a))
    (hψ : ∀ a ∈ s, ContDiff ℝ k (ψ a)) {B : ℝ}
    (hB : ∀ a ∈ s, ∀ i ≤ k, ∀ y, h ^ i * ‖iteratedFDeriv ℝ i (ψ a) y‖ ≤ B) (hf : ContDiff ℝ k f)
    (hpart : ∀ y ∈ Function.support f, ∑ a ∈ s, ψ a y * χ a y = 1) (hh : 0 ≤ h) :
    semiclassicalSobolevNorm k h f ^ 2 ≤ (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K *
      ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ χ a y • f y) ^ 2 := by
  -- The localizations `g a` of `f`, and the scaled jets of `f` and of the `g a`.
  set g : ι → E → F := fun a y ↦ χ a y • f y
  set W : E → ℝ := fun y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i * ‖iteratedFDeriv ℝ i f y‖
  set V : ι → E → ℝ := fun a y ↦ ∑ i ∈ Finset.range (k + 1), h ^ i *
    ‖iteratedFDeriv ℝ i (g a) y‖
  set c : ℝ := (k + 1) * 2 ^ k * B with hcdef
  obtain ⟨hdec, hfm⟩ := localization_decomposition s hχc hf hpart
  have hg (a : ι) (ha : a ∈ s) : ContDiff ℝ k (g a) := (hχ a ha).smul hf
  have hgm (a : ι) (ha : a ∈ s) (i : ℕ) (hi : i ≤ k) : MemLp (iteratedFDeriv ℝ i (g a)) 2 :=
    (hg a ha).memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hi)
      (hχc a ha).smul_right
  -- Pointwise, `W ≤ c ∑ₐ V a`, a sum with at most `K` nonzero terms, so `W² ≤ c² K ∑ₐ (V a)²`.
  have hW (y : E) : W y ≤ c * ∑ a ∈ s, V a y :=
    sum_pow_mul_norm_iteratedFDeriv_le_sum s hψ hB hg hdec hh y
  have hpt (y : E) : W y ^ 2 ≤ c ^ 2 * (K * ∑ a ∈ s, V a y ^ 2) :=
    calc W y ^ 2 ≤ (c * ∑ a ∈ s, V a y) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun i _ ↦ by positivity) (hW y) 2
      _ = c ^ 2 * (∑ a ∈ s, V a y) ^ 2 := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_sum_le_mul_sum_sq_of_card_le hK y fun a _ hy ↦
          sum_pow_mul_norm_iteratedFDeriv_smul_eq_zero hy) (by positivity)
  have hint : ∫ y, W y ^ 2 ≤ c ^ 2 * (K * ∑ a ∈ s, ∫ y, V a y ^ 2) := by
    have hVi (a : ι) (ha : a ∈ s) := integrable_sq_sum_pow_mul_norm_iteratedFDeriv (hgm a ha) h
    rw [← integral_finsetSum _ hVi, ← integral_const_mul, ← integral_const_mul]
    exact integral_mono (integrable_sq_sum_pow_mul_norm_iteratedFDeriv hfm h)
      (((integrable_finsetSum _ hVi).const_mul _).const_mul _) hpt
  calc semiclassicalSobolevNorm k h f ^ 2
      ≤ (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) * ∫ y, W y ^ 2) :=
        sq_semiclassicalSobolevNorm_le_integral hfm hh
    _ ≤ (k + 1) * (h ^ (-(finrank ℝ E : ℝ)) * (c ^ 2 * (K * ∑ a ∈ s, ∫ y, V a y ^ 2))) := by
        gcongr
    _ = (k + 1) * c ^ 2 * K * ∑ a ∈ s, h ^ (-(finrank ℝ E : ℝ)) * ∫ y, V a y ^ 2 := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ (k + 1) * c ^ 2 * K * ∑ a ∈ s, (k + 1) * semiclassicalSobolevNorm k h (g a) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha ↦
          integral_le_sq_semiclassicalSobolevNorm (hgm a ha) hh) (by positivity)
    _ = _ := by
        rw [← Finset.mul_sum, hcdef,
          show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring

open Classical in
/-- **The localizations over a bounded-overlap partition of unity by `h`-balls control the norm.**
Let `η` be a compactly supported cutoff of class `Cᵏ` and `ψ` a cutoff of class `Cᵏ` with
`‖Dⁱ ψ‖ ≤ B` for `i ≤ k`. Let `x a`, `a ∈ s`, be centres such that every point lies in the support
of at most `K` of the rescaled cutoffs `η (h⁻¹ • (· - x a))`, and let `f` be of class `Cᵏ` with
`∑_{a ∈ s} ψ (h⁻¹ • (y - x a)) η (h⁻¹ • (y - x a)) = 1` wherever `f y ≠ 0`. Then for `h > 0`

`‖f‖²_{k,h} ≤ (k + 1)⁴ 4ᵏ B² K ∑_{a ∈ s} ‖η (h⁻¹ • (· - x a)) f‖²_{k,h}`.

The constant is independent of `h`, of the centres and of their number. This is
`TauCeti.sq_semiclassicalSobolevNorm_le_sum_sq_smul` for the translates of two rescaled
cutoffs. -/
theorem sq_semiclassicalSobolevNorm_le_sum_sq_localization {ι : Type*} (s : Finset ι) (x : ι → E)
    {K : ℕ} (hK : ∀ y, #{a ∈ s | h⁻¹ • (y - x a) ∈ tsupport η} ≤ K) (hη : ContDiff ℝ k η)
    (hηc : HasCompactSupport η) (hψ : ContDiff ℝ k ψ) {B : ℝ}
    (hB : ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ B) (hf : ContDiff ℝ k f)
    (hpart : ∀ y ∈ Function.support f, ∑ a ∈ s, ψ (h⁻¹ • (y - x a)) * η (h⁻¹ • (y - x a)) = 1)
    (hh : 0 < h) :
    semiclassicalSobolevNorm k h f ^ 2 ≤ (k + 1) ^ 4 * 4 ^ k * B ^ 2 * K *
      ∑ a ∈ s, semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x a)) • f y) ^ 2 :=
  sq_semiclassicalSobolevNorm_le_sum_sq_smul s (χ := fun a z ↦ η (h⁻¹ • (z - x a)))
    (ψ := fun a z ↦ ψ (h⁻¹ • (z - x a))) (card_filter_mem_tsupport_le hK)
    (fun a _ ↦ hη.comp_inv_smul_sub h (x a)) (fun a _ ↦ hηc.comp_inv_smul_sub hh.ne' (x a))
    (fun a _ ↦ hψ.comp_inv_smul_sub h (x a))
    (fun a _ i hi y ↦ (pow_mul_norm_iteratedFDeriv_comp_inv_smul_sub _ hh (x a) i y).trans_le
      (hB i hi _)) hf hpart hh.le

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
      fun i hi y ↦ (pow_mul_norm_iteratedFDeriv_comp_inv_smul_sub _ hh x i y).trans_le
        (hB i hi _)).2
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
    (localization_decomposition s (χ := fun a z ↦ η (h⁻¹ • (z - x a)))
      (fun a _ ↦ hηc.comp_inv_smul_sub hh.ne' (x a)) hf hpart).2 hh).1
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
