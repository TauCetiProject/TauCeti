/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The binomial expansion of a power of the Japanese bracket

On a real inner product space `E`, fix a scale `c ≠ 0` and a real exponent `r`. At frequencies
with `‖c ξ‖ > 1` the binomial series gives

`(1 + ‖c ξ‖ ^ 2) ^ r = ∑ₖ (r choose k) (‖c ξ‖ ^ 2) ^ (r - k)`,

a sum of terms positively homogeneous of the decreasing degrees `2r - 2k`. This file proves that
truncating the series is an expansion in the sense of symbols: if `ψ` is a smooth function which
vanishes near `0` and equals `1` at large frequencies, then for every `K` the remainder

`(1 + ‖c ξ‖ ^ 2) ^ r - ψ(ξ) ∑_{k < K} (r choose k) (‖c ξ‖ ^ 2) ^ (r - k)`

satisfies the symbol estimates of order `2r - 2K`: its `j`-th derivative is
`O((1 + ‖ξ‖ ^ 2) ^ (r - K - j / 2))`
(`TauCeti.exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_sub_sum_le`). With `c = (2π)⁻¹`
and `r = s / 2`, this is the statement that the Bessel weight `⟨ξ / 2π⟩ ^ s` is a classical symbol
of order `s`.

## The argument

Write `R_r` for the remainder. The size estimate (`j = 0`) is the remainder estimate of the
binomial series `(1 + u) ^ r = ∑ₖ (r choose k) uᵏ` at `u = ‖c ξ‖⁻²`
(`Real.one_add_rpow_hasFPowerSeriesAt_zero`). For the derivatives, the identity
`(r - k) (r choose k) = r (r - 1 choose k)` (`Ring.choose_mul_add_one_eq`) shows that
differentiating the terms of the expansion of exponent `r` gives `2 r c² ⟪ξ, ·⟫` times the terms of
exponent `r - 1`, exactly as for `(1 + ‖c ξ‖ ^ 2) ^ r` itself. Hence

`D R_r(ξ) = 2 r c² R_{r - 1}(ξ) ⟪ξ, ·⟫ - ∑_{k < K} (r choose k) (‖c ξ‖ ^ 2) ^ (r - k) Dψ(ξ)`,

where the last sum is smooth and compactly supported, since `Dψ` vanishes near `0` and at large
frequencies. The estimates then follow by induction on the order of the derivative, for all
exponents at once: the first term gains half a power of `1 + ‖ξ‖ ^ 2` over `R_{r - 1}`
(`ContinuousLinearMap.exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.4) and (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
-/

public section

open Filter Topology Metric
open scoped ContDiff

namespace Ring

/-- The analogue of `Nat.choose_mul_succ_eq` for generalized binomial coefficients:
`(r choose k) (r + 1) = (r + 1 choose k) (r + 1 - k)`. -/
theorem choose_mul_add_one_eq {R : Type*} [CommRing R] [BinomialRing R] (r : R) (k : ℕ) :
    choose r k * (r + 1) = choose (r + 1) k * (r + 1 - k) := by
  have h := choose_smul_choose (r + 1) (n := k + 1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, choose_one_right, Nat.cast_one, Nat.add_sub_cancel,
    add_sub_cancel_right] at h
  -- Multiply by `k!` and use `(r + 1)_(k + 1) = (r + 1)_k (r + 1 - k)` for the Pochhammer
  -- evaluations.
  have := BinomialRing.toHasUniqueDiv (R := R)
  rw [mul_comm, ← h, ← nsmul_right_inj (Nat.factorial_ne_zero k), smul_smul, mul_comm,
    ← Nat.factorial_succ, ← descPochhammer_eq_factorial_smul_choose, ← smul_mul_assoc,
    ← descPochhammer_eq_factorial_smul_choose, descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
  simp

end Ring

namespace TauCeti

section Bounds

/-- On a closed ball a continuous function is bounded by any power of the Japanese bracket. -/
private theorem exists_norm_le_one_add_norm_sq_rpow_of_norm_le {E F : Type*}
    [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F] {f : E → F} (hf : Continuous f)
    (R ρ : ℝ) : ∃ C, 0 ≤ C ∧ ∀ ξ, ‖ξ‖ ≤ R → ‖f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ρ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0 / (1 + R ^ 2) ^ (-|2 * ρ| / 2), by positivity, fun ξ hξ ↦ ?_⟩
  have hw := one_add_sq_rpow_neg_abs_le_one_add_norm_sq_rpow hξ (2 * ρ)
  rw [mul_div_cancel_left₀ _ two_ne_zero] at hw
  calc ‖f ξ‖ ≤ max M 0 := (hM ξ (mem_closedBall_zero_iff.2 hξ)).trans (le_max_left _ _)
    _ = max M 0 / (1 + R ^ 2) ^ (-|2 * ρ| / 2) * (1 + R ^ 2) ^ (-|2 * ρ| / 2) := by field_simp
    _ ≤ _ := by gcongr

/-- A `C^j` function vanishing outside a ball has its `j`-th derivative bounded by any power of
the Japanese bracket. -/
private theorem exists_norm_iteratedFDeriv_le_of_eq_zero_of_lt_norm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {j : ℕ} {f : E → F}
    (hf : ContDiff ℝ j f) {R : ℝ} (hf0 : ∀ ξ, R < ‖ξ‖ → f ξ = 0) (ρ : ℝ) :
    ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ j f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ρ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_le_one_add_norm_sq_rpow_of_norm_le (hf.continuous_iteratedFDeriv le_rfl) R ρ
  refine ⟨C, fun ξ ↦ ?_⟩
  rcases le_or_gt ‖ξ‖ R with hξ | hξ
  · exact hC ξ hξ
  · have h0 : f =ᶠ[𝓝 ξ] 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with η hη
      exact hf0 η hη
    rw [(h0.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    positivity

end Bounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : ℝ} {ψ : E → ℝ}

/-- The remainder of the binomial expansion of `(1 + ‖c ξ‖ ^ 2) ^ r` after `K` terms, the terms
being cut off by `ψ`. -/
private noncomputable def bracketRemainder (c : ℝ) (ψ : E → ℝ) (r : ℝ) (K : ℕ) (ξ : E) : ℝ :=
  (1 + ‖c • ξ‖ ^ 2) ^ r - ψ ξ * ∑ k ∈ Finset.range K, Ring.choose r k * (‖c • ξ‖ ^ 2) ^ (r - k)

/-- A homogeneous power `(‖c ξ‖ ^ 2) ^ μ` times a smooth function vanishing near `0` is smooth. -/
private theorem contDiff_rpow_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hc : c ≠ 0) {g : E → F} (hg : ContDiff ℝ ∞ g) (hg0 : g =ᶠ[𝓝 0] 0) (μ : ℝ) :
    ContDiff ℝ ∞ fun ξ ↦ (‖c • ξ‖ ^ 2) ^ μ • g ξ := by
  refine contDiff_iff_contDiffAt.2 fun ξ ↦ ?_
  rcases eq_or_ne ξ 0 with rfl | hξ
  · refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
    filter_upwards [hg0] with η hη
    simp [hη]
  · have hne : ‖c • ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (smul_ne_zero hc hξ))
    exact ((((contDiff_norm_sq ℝ).comp (contDiff_const_smul c)).contDiffAt.rpow_const_of_ne
      hne).smul hg.contDiffAt)

private theorem contDiff_bracketRemainder (hc : c ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ψ =ᶠ[𝓝 0] 0) (r : ℝ) (K : ℕ) : ContDiff ℝ ∞ (bracketRemainder c ψ r K) := by
  have hfun : bracketRemainder c ψ r K = fun ξ ↦ (1 + ‖c • ξ‖ ^ 2) ^ r -
      ∑ k ∈ Finset.range K, Ring.choose r k • ((‖c • ξ‖ ^ 2) ^ (r - k) • ψ ξ) := by
    funext ξ
    simp only [bracketRemainder, Finset.mul_sum, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hfun]
  exact ((contDiff_one_add_norm_sq_rpow r).comp (contDiff_const_smul c)).sub
    (ContDiff.sum fun k _ ↦ (contDiff_rpow_smul hc hψ hψ0 _).const_smul _)

/-- The derivative of `(‖c ξ‖ ^ 2) ^ μ` is `μ (‖c ξ‖ ^ 2) ^ (μ - 1)` times `2 c² ⟪ξ, ·⟫`, away
from `0`. -/
private theorem hasFDerivAt_norm_smul_sq_rpow {ξ : E} (hcξ : c • ξ ≠ 0) (μ : ℝ) :
    HasFDerivAt (fun ξ : E ↦ (‖c • ξ‖ ^ 2) ^ μ)
      ((μ * (‖c • ξ‖ ^ 2) ^ (μ - 1)) • ((2 * c ^ 2) • innerSL ℝ ξ)) ξ := by
  have h := ((hasStrictFDerivAt_norm_sq (c • ξ)).hasFDerivAt.comp ξ
    ((hasFDerivAt_id ξ).const_smul c)).rpow_const (p := μ)
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.2 hcξ)))
  refine h.congr_fderiv ?_
  ext v
  simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right,
    smul_eq_mul, nsmul_eq_mul, RCLike.conj_to_real]
  ring

/-- The derivative of the expanded bracket power `(1 + ‖c ξ‖ ^ 2) ^ r`. -/
private theorem hasFDerivAt_one_add_norm_smul_sq_rpow (r : ℝ) (ξ : E) :
    HasFDerivAt (fun ξ : E ↦ (1 + ‖c • ξ‖ ^ 2) ^ r)
      ((1 + ‖c • ξ‖ ^ 2) ^ (r - 1) • ((2 * r * c ^ 2) • innerSL ℝ ξ)) ξ := by
  have h := (hasFDerivAt_one_add_norm_sq_rpow r (c • ξ)).comp ξ
    ((hasFDerivAt_id ξ).const_smul c)
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

/-- The derivative of a cut-off term `ψ(ξ) (‖c ξ‖ ^ 2) ^ μ`, for a cutoff `ψ` vanishing
near `0`. -/
private theorem hasFDerivAt_mul_norm_smul_sq_rpow (hc : c ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ψ =ᶠ[𝓝 0] 0) (μ : ℝ) (ξ : E) :
    HasFDerivAt (fun ξ : E ↦ ψ ξ * (‖c • ξ‖ ^ 2) ^ μ)
      (ψ ξ • (μ * (‖c • ξ‖ ^ 2) ^ (μ - 1)) • ((2 * c ^ 2) • innerSL ℝ ξ) +
        (‖c • ξ‖ ^ 2) ^ μ • fderiv ℝ ψ ξ) ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h0 : (fun ξ : E ↦ ψ ξ * (‖c • ξ‖ ^ 2) ^ μ) =ᶠ[𝓝 0] fun _ ↦ 0 := by
      filter_upwards [hψ0] with η hη
      simp [hη]
    have hd : fderiv ℝ ψ 0 = 0 := by
      rw [hψ0.fderiv_eq]
      exact fderiv_const_apply 0
    rw [hψ0.self_of_nhds, hd]
    simpa using (hasFDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq h0
  · exact ((hψ.differentiable (by simp) ξ).hasFDerivAt.mul
      (hasFDerivAt_norm_smul_sq_rpow (smul_ne_zero hc hξ) μ))

/-- The error term `∑_{k < K} (r choose k) (‖c ξ‖ ^ 2) ^ (r - k) Dψ(ξ)` of the derivative of the
remainder. -/
private noncomputable def bracketRemainderError (c : ℝ) (ψ : E → ℝ) (r : ℝ) (K : ℕ) (ξ : E) :
    E →L[ℝ] ℝ :=
  ∑ k ∈ Finset.range K, (Ring.choose r k * (‖c • ξ‖ ^ 2) ^ (r - k)) • fderiv ℝ ψ ξ

/-- **The derivative of the remainder.** It is `2 r c² ⟪ξ, ·⟫` times the remainder of exponent
`r - 1`, up to the error term where the cutoff varies. -/
private theorem fderiv_bracketRemainder (hc : c ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ψ =ᶠ[𝓝 0] 0) (r : ℝ) (K : ℕ) :
    fderiv ℝ (bracketRemainder c ψ r K) = fun ξ ↦
      bracketRemainder c ψ (r - 1) K ξ • ((2 * r * c ^ 2) • innerSL ℝ) ξ -
        bracketRemainderError c ψ r K ξ := by
  funext ξ
  have hsum := HasFDerivAt.fun_sum (u := Finset.range K) fun k _ ↦
    (hasFDerivAt_mul_norm_smul_sq_rpow hc hψ hψ0 (r - k) ξ).const_mul (Ring.choose r k)
  have h := (hasFDerivAt_one_add_norm_smul_sq_rpow (c := c) r ξ).fun_sub hsum
  have hfun : bracketRemainder c ψ r K = fun ξ ↦ (1 + ‖c • ξ‖ ^ 2) ^ r -
      ∑ k ∈ Finset.range K, Ring.choose r k * (ψ ξ * (‖c • ξ‖ ^ 2) ^ (r - k)) := by
    funext ξ
    simp only [bracketRemainder, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hfun, h.fderiv]
  -- Termwise, `(r - k) (r choose k) = r (r - 1 choose k)` turns the derivative of a cut-off term
  -- of exponent `r` into `2 r c² ⟪ξ, ·⟫` times the cut-off term of exponent `r - 1`.
  have hterm : ∀ k ∈ Finset.range K, Ring.choose r k •
      (ψ ξ • ((r - k) * (‖c • ξ‖ ^ 2) ^ (r - k - 1)) • (2 * c ^ 2) • innerSL ℝ ξ +
        (‖c • ξ‖ ^ 2) ^ (r - k) • fderiv ℝ ψ ξ) =
      (ψ ξ * (Ring.choose (r - 1) k * (‖c • ξ‖ ^ 2) ^ (r - 1 - k))) •
          ((2 * r * c ^ 2) • innerSL ℝ) ξ +
        (Ring.choose r k * (‖c • ξ‖ ^ 2) ^ (r - k)) • fderiv ℝ ψ ξ := by
    intro k _
    have hchoose := Ring.choose_mul_add_one_eq (r - 1) k
    rw [sub_add_cancel] at hchoose
    rw [show r - k - 1 = r - 1 - k by ring]
    ext v
    simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    linear_combination (-(ψ ξ * (‖c • ξ‖ ^ 2) ^ (r - 1 - k) * (2 * c ^ 2 * inner ℝ ξ v))) * hchoose
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  simp only [bracketRemainder, bracketRemainderError, sub_smul, Finset.mul_sum, Finset.sum_smul,
    smul_apply]
  abel

/-- The error term is smooth. -/
private theorem contDiff_bracketRemainderError (hc : c ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ψ =ᶠ[𝓝 0] 0) (r : ℝ) (K : ℕ) : ContDiff ℝ ∞ (bracketRemainderError c ψ r K) := by
  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  have hdψ0 : fderiv ℝ ψ =ᶠ[𝓝 0] 0 := by
    filter_upwards [hψ0.eventuallyEq_nhds] with η hη
    rw [hη.fderiv_eq]
    exact fderiv_const_apply 0
  have hfun : bracketRemainderError c ψ r K = fun ξ ↦
      ∑ k ∈ Finset.range K, Ring.choose r k • ((‖c • ξ‖ ^ 2) ^ (r - k) • fderiv ℝ ψ ξ) := by
    funext ξ
    simp only [bracketRemainderError, smul_smul]
  rw [hfun]
  exact ContDiff.sum fun k _ ↦ (contDiff_rpow_smul hc hdψ hdψ0 _).const_smul _

/-- The error term vanishes where `ψ` is locally constant equal to `1`. -/
private theorem bracketRemainderError_eq_zero {R : ℝ} (hψ1 : ∀ ξ, R ≤ ‖ξ‖ → ψ ξ = 1) (r : ℝ)
    (K : ℕ) {ξ : E} (hξ : R < ‖ξ‖) : bracketRemainderError c ψ r K ξ = 0 := by
  have h1 : ψ =ᶠ[𝓝 ξ] fun _ ↦ 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with η hη
    exact hψ1 η hη.le
  simp [bracketRemainderError, h1.fderiv_eq]

/-- The remainder of the binomial series of `(1 + u) ^ r` after `K` terms is `O(u ^ K)` for small
`u > 0`. -/
private theorem exists_abs_one_add_rpow_sub_sum_le (r : ℝ) (K : ℕ) :
    ∃ A ε, 0 < ε ∧ ∀ u : ℝ, 0 < u → u < ε →
      |(1 + u) ^ r - ∑ k ∈ Finset.range K, Ring.choose r k * u ^ k| ≤ A * u ^ K := by
  obtain ⟨A, hA⟩ := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := r)).isBigO_sub_partialSum_pow
    K |>.bound
  obtain ⟨ε, hε, hεA⟩ := Metric.eventually_nhds_iff.1 hA
  refine ⟨A, ε, hε, fun u hu huε ↦ ?_⟩
  have hbound := hεA (y := u) (by simpa [abs_of_pos hu] using huε)
  simpa only [zero_add, FormalMultilinearSeries.partialSum, binomialSeries_apply, List.ofFn_const,
    List.prod_replicate, smul_eq_mul, Real.norm_eq_abs, abs_pow, abs_of_pos hu] using hbound

/-- Where the cutoff is `1`, the remainder is `G ^ r` times the remainder of the binomial series of
`(1 + u) ^ r` at `u = G⁻¹`, with `G = ‖c ξ‖ ^ 2`. -/
private theorem bracketRemainder_eq_mul {ξ : E} (hψ : ψ ξ = 1) (hG : 0 < ‖c • ξ‖ ^ 2) (r : ℝ)
    (K : ℕ) : bracketRemainder c ψ r K ξ = (‖c • ξ‖ ^ 2) ^ r *
      ((1 + (‖c • ξ‖ ^ 2)⁻¹) ^ r -
        ∑ k ∈ Finset.range K, Ring.choose r k * ((‖c • ξ‖ ^ 2)⁻¹) ^ k) := by
  set G := ‖c • ξ‖ ^ 2 with hGdef
  have h1G : 1 + G = G * (1 + G⁻¹) := by rw [mul_add, mul_one, mul_inv_cancel₀ hG.ne']; ring
  simp only [bracketRemainder, hψ, one_mul, ← hGdef, h1G,
    Real.mul_rpow hG.le (by positivity : (0 : ℝ) ≤ 1 + G⁻¹), mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Real.rpow_sub hG, Real.rpow_natCast, inv_pow]
  ring

/-- For `‖ξ‖ ≥ 1`, the power `(‖c ξ‖ ^ 2) ^ μ` is at most a constant times `(1 + ‖ξ‖ ^ 2) ^ μ`. -/
private theorem norm_smul_sq_rpow_le (hc : c ≠ 0) (μ : ℝ) {ξ : E} (h1 : 1 ≤ ‖ξ‖) :
    (‖c • ξ‖ ^ 2) ^ μ ≤ ((c ^ 2 / 2) ^ μ + (c ^ 2) ^ μ) * (1 + ‖ξ‖ ^ 2) ^ μ := by
  have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hc2 : 0 < c ^ 2 := by positivity
  have hGeq : ‖c • ξ‖ ^ 2 = c ^ 2 * ‖ξ‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  -- The ratio `‖c ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2)` lies between `c ^ 2 / 2` and `c ^ 2`.
  have hratio : c ^ 2 / 2 ≤ ‖c • ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2) ∧
      ‖c • ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2) ≤ c ^ 2 := by
    have h1sq : 1 ≤ ‖ξ‖ ^ 2 := one_le_pow₀ h1
    rw [hGeq, le_div_iff₀ hw, div_le_iff₀ hw]
    constructor <;> nlinarith [mul_nonneg hc2.le (sub_nonneg.2 h1sq)]
  have hpow : (‖c • ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2)) ^ μ ≤ (c ^ 2 / 2) ^ μ + (c ^ 2) ^ μ := by
    rcases le_total 0 μ with hμ | hμ
    · exact (Real.rpow_le_rpow (by positivity) hratio.2 hμ).trans
        (le_add_of_nonneg_left (by positivity))
    · exact (Real.rpow_le_rpow_of_nonpos (by positivity) hratio.1 hμ).trans
        (le_add_of_nonneg_right (by positivity))
  calc (‖c • ξ‖ ^ 2) ^ μ = (‖c • ξ‖ ^ 2 / (1 + ‖ξ‖ ^ 2)) ^ μ * (1 + ‖ξ‖ ^ 2) ^ μ := by
        rw [← Real.mul_rpow (by positivity) hw.le, div_mul_cancel₀ _ hw.ne']
    _ ≤ _ := by gcongr

/-- **The size of the remainder.** At large frequencies it is `(‖c ξ‖ ^ 2) ^ r` times the
remainder of the binomial series of `(1 + u) ^ r` at `u = ‖c ξ‖⁻²`, hence
`O((‖c ξ‖ ^ 2) ^ (r - K))`; on a ball it is bounded. -/
private theorem exists_abs_bracketRemainder_le [ProperSpace E] (hc : c ≠ 0)
    (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ =ᶠ[𝓝 0] 0) {R : ℝ} (hψ1 : ∀ ξ, R ≤ ‖ξ‖ → ψ ξ = 1) (r : ℝ)
    (K : ℕ) : ∃ C, ∀ ξ, |bracketRemainder c ψ r K ξ| ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r - K) := by
  obtain ⟨A, ε, hε, hA⟩ := exists_abs_one_add_rpow_sub_sum_le r K
  -- Beyond `R₁`, the cutoff is `1`, `‖ξ‖ ≥ 1` and `u = ‖c ξ‖⁻² < ε`.
  set R₁ := max (max R 1) (Real.sqrt (2 / (ε * c ^ 2)))
  obtain ⟨B, -, hB⟩ := exists_norm_le_one_add_norm_sq_rpow_of_norm_le
    ((contDiff_bracketRemainder hc hψ hψ0 r K).continuous) R₁ (r - K)
  refine ⟨max B (|A| * ((c ^ 2 / 2) ^ (r - K) + (c ^ 2) ^ (r - K))), fun ξ ↦ ?_⟩
  rcases le_or_gt ‖ξ‖ R₁ with hξ | hξ
  · exact (hB ξ hξ).trans (by gcongr; exact le_max_left _ _)
  have h1 : 1 ≤ ‖ξ‖ := (le_max_right _ _).trans ((le_max_left _ _).trans hξ.le)
  have hsq : 2 < ‖ξ‖ ^ 2 * (ε * c ^ 2) := by
    rw [← div_lt_iff₀ (by positivity)]
    exact (Real.sqrt_lt' (by linarith)).1 ((le_max_right _ _).trans_lt hξ)
  have hGeq : ‖c • ξ‖ ^ 2 = c ^ 2 * ‖ξ‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hG : 0 < ‖c • ξ‖ ^ 2 := by rw [hGeq]; positivity
  have huε : (‖c • ξ‖ ^ 2)⁻¹ < ε := by
    rw [inv_lt_iff_one_lt_mul₀ hG, hGeq]
    nlinarith
  calc |bracketRemainder c ψ r K ξ|
      = (‖c • ξ‖ ^ 2) ^ r * |(1 + (‖c • ξ‖ ^ 2)⁻¹) ^ r -
          ∑ k ∈ Finset.range K, Ring.choose r k * ((‖c • ξ‖ ^ 2)⁻¹) ^ k| := by
        rw [bracketRemainder_eq_mul (hψ1 ξ ((le_max_left _ _).trans ((le_max_left _ _).trans
          hξ.le))) hG, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hG r)]
    _ ≤ (‖c • ξ‖ ^ 2) ^ r * (A * ((‖c • ξ‖ ^ 2)⁻¹) ^ K) := by
        gcongr
        exact hA _ (inv_pos.2 hG) huε
    _ = A * (‖c • ξ‖ ^ 2) ^ (r - K) := by
        rw [Real.rpow_sub hG, Real.rpow_natCast, inv_pow]
        ring
    _ ≤ |A| * (((c ^ 2 / 2) ^ (r - K) + (c ^ 2) ^ (r - K)) * (1 + ‖ξ‖ ^ 2) ^ (r - K)) :=
        mul_le_mul (le_abs_self A) (norm_smul_sq_rpow_le hc _ h1) (by positivity) (abs_nonneg A)
    _ ≤ _ := by
        rw [← mul_assoc]
        gcongr
        exact le_max_right _ _

/-- The remainder of the binomial expansion of `(1 + ‖c ξ‖ ^ 2) ^ r` after `K` terms cut off by
a smooth `ψ` vanishing near `0` is smooth. -/
theorem contDiff_one_add_norm_smul_sq_rpow_sub_sum (hc : c ≠ 0) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ψ =ᶠ[𝓝 0] 0) (r : ℝ) (K : ℕ) :
    ContDiff ℝ ∞ fun ξ : E ↦ (1 + ‖c • ξ‖ ^ 2) ^ r -
      ψ ξ * ∑ k ∈ Finset.range K, Ring.choose r k * (‖c • ξ‖ ^ 2) ^ (r - k) :=
  contDiff_bracketRemainder hc hψ hψ0 r K

/-- **The binomial expansion of a power of the Japanese bracket.** Let `c ≠ 0` and let `ψ` be a
smooth function vanishing near `0` and equal to `1` outside some ball. For every real `r` and all
`K` and `j`, the `j`-th derivative of the remainder

`(1 + ‖c ξ‖ ^ 2) ^ r - ψ(ξ) ∑_{k < K} (r choose k) (‖c ξ‖ ^ 2) ^ (r - k)`

of the binomial expansion is `O((1 + ‖ξ‖ ^ 2) ^ (r - K - j / 2))`: the remainder is a symbol of
order `2r - 2K`. -/
theorem exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_sub_sum_le [ProperSpace E]
    (hc : c ≠ 0) (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ =ᶠ[𝓝 0] 0) (hψ1 : ∃ R, ∀ ξ, R ≤ ‖ξ‖ → ψ ξ = 1)
    (r : ℝ) (K j : ℕ) :
    ∃ C, ∀ ξ : E, ‖iteratedFDeriv ℝ j (fun ξ ↦ (1 + ‖c • ξ‖ ^ 2) ^ r -
        ψ ξ * ∑ k ∈ Finset.range K, Ring.choose r k * (‖c • ξ‖ ^ 2) ^ (r - k)) ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (r - K - j / 2) := by
  obtain ⟨R, hR⟩ := hψ1
  change ∃ C, ∀ ξ : E, ‖iteratedFDeriv ℝ j (bracketRemainder c ψ r K) ξ‖ ≤ _
  induction j using Nat.strong_induction_on generalizing r with
  | _ j ih =>
  rcases j with _ | j
  · obtain ⟨C, hC⟩ := exists_abs_bracketRemainder_le hc hψ hψ0 hR r K
    refine ⟨C, fun ξ ↦ ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    simpa using hC ξ
  · -- Differentiate once: the remainder of exponent `r - 1` times a linear map, plus the error.
    have hrem := contDiff_bracketRemainder hc hψ hψ0 (r - 1) K
    have herr := contDiff_bracketRemainderError hc hψ hψ0 r K
    obtain ⟨C₁, hC₁⟩ := ContinuousLinearMap.exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow
      ((2 * r * c ^ 2) • innerSL ℝ) (hrem.of_le (mod_cast le_top)) (ρ := r - 1 - K) fun i hi ↦
        (ih i (Nat.lt_succ_of_le hi) (r - 1)).imp fun C hC ξ ↦ (hC ξ).trans_eq (by ring_nf)
    obtain ⟨C₂, hC₂⟩ := exists_norm_iteratedFDeriv_le_of_eq_zero_of_lt_norm
      (herr.of_le (mod_cast le_top)) (j := j)
      (fun ξ hξ ↦ bracketRemainderError_eq_zero hR r K hξ) (r - K - (j + 1 : ℕ) / 2)
    have hsmul : ContDiff ℝ ∞ fun ξ ↦
        bracketRemainder c ψ (r - 1) K ξ • ((2 * r * c ^ 2) • innerSL ℝ) ξ :=
      hrem.smul ((2 * r * c ^ 2) • innerSL ℝ).contDiff
    refine ⟨C₁ + C₂, fun ξ ↦ ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, fderiv_bracketRemainder hc hψ hψ0,
      fun_iteratedFDeriv_sub_apply (hsmul.contDiffAt.of_le (mod_cast le_top))
        (herr.contDiffAt.of_le (mod_cast le_top))]
    refine (norm_sub_le _ _).trans ?_
    rw [add_mul]
    gcongr
    · exact (hC₁ ξ).trans_eq (by push_cast; ring_nf)
    · exact hC₂ ξ

end TauCeti
