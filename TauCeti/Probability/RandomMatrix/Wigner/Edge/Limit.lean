/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Probability.RandomMatrix.Wigner.Truncation.OperatorNorm
import TauCeti.Probability.RandomMatrix.Wigner.SemicircleLaw
import TauCeti.Probability.RandomMatrix.Wigner.Diagonal.OperatorNorm
import TauCeti.Probability.RandomMatrix.SpectralMoment.Extremes
import TauCeti.Probability.RandomMatrix.Wigner.Trace.Integrability
import TauCeti.Analysis.Matrix.SpectralMeasure.ExtremeEigenvalues
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Probability.RandomMatrix.Wigner.Trace.Bound

/-!
# Edge limits of Wigner matrices

Let the upper entries of a Wigner matrix be i.i.d. with mean zero, second absolute moment `v` and
finite fourth moment, and let the diagonal entries share a law of finite second moment. Then the
largest and smallest eigenvalues of the normalized corners converge almost surely to `2 * √v`
and `-(2 * √v)`, the edges of the semicircle law of variance `v`.

The zero-diagonal semicircle law forces eigenvalues arbitrarily close to both edges from
inside. A growing trace bound on centered truncated corners controls the operator norm
from above. This upper bound transfers to the original matrices by the operator-norm
truncation result. The diagonal perturbation also transfers the lower edge estimates,
so the diagonal entries can be dependent. The growing trace bound holds at truncation radius
`(n + 1) ^ (1 / 3)` and orders of logarithmic size, by the Füredi–Komlós bound
`ProbabilityTheory.iIndepFun.norm_integral_trace_pow_wignerMatrix_centeredTruncation_le`.

## Main results

* `ProbabilityTheory.iIndepFun.ae_tendsto_eigenvalues₀_zero_and_card_sub_one_wignerMatrix`: the
  almost-sure edge limits. The variant with the suffix `_of_integral_re_trace_pow_two_mul_le`
  reduces them to a growing trace bound.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.12.
* Z. Füredi and J. Komlós, *The eigenvalues of random symmetric matrices*, Combinatorica 1
  (1981), 233–241.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix TauCeti TauCeti.Probability
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace TauCeti

/-- At truncation radius `(n + 1) ^ (1 / 3)` and orders `⌈B * log (n + 1)⌉₊`, the parameter `γ` of
the Füredi–Komlós bound eventually lies in `[0, 1]`, and its product with the orders tends to
zero. -/
private theorem eventually_sqrt_le_one_and_ceil_mul_sqrt_le {σ B δ : ℝ} (hσ : 0 < σ)
    (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) / (σ * Real.sqrt ((n + 1 : ℕ) : ℝ))) ≤ 1 ∧
      (⌈B * Real.log (n + 1)⌉₊ : ℝ) *
        Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) / (σ * Real.sqrt ((n + 1 : ℕ) : ℝ))) ≤
          δ := by
  -- The parameter is `√(2 / σ) / (n + 1) ^ (1 / 12)`.
  have hγ (x : ℝ) (hx : 0 < x) : Real.sqrt (2 * x ^ (1 / 3 : ℝ) / (σ * Real.sqrt x)) =
      Real.sqrt (2 / σ) / x ^ (1 / 12 : ℝ) := by
    have h₄ : x ^ (1 / 3 : ℝ) = (x ^ (1 / 12 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    have h₆ : Real.sqrt x = (x ^ (1 / 12 : ℝ)) ^ 6 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
      norm_num
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt (2 / σ) / x ^ (1 / 12 : ℝ)), div_pow,
      Real.sq_sqrt (by positivity), h₄, h₆]
    congr 1
    field_simp
  -- Both `(n + 1) ^ (-1 / 12)` and `log (n + 1) / (n + 1) ^ (1 / 12)` tend to zero.
  have hlim : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h₁ := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).inv_tendsto_atTop.comp
    hlim).const_mul (Real.sqrt (2 / σ))
  have h₂ := ((((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).tendsto_div_nhds_zero
    ).comp hlim).const_mul (B * Real.sqrt (2 / σ))).add h₁
  rw [mul_zero] at h₁
  rw [mul_zero, zero_add, mul_zero] at h₂
  filter_upwards [h₁.eventually (ge_mem_nhds zero_lt_one), h₂.eventually (ge_mem_nhds hδ)]
    with n hn₁ hn₂
  simp only [Function.comp_apply, Pi.inv_apply] at hn₁ hn₂
  have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  rw [hγ _ (Nat.cast_pos.mpr n.succ_pos)]
  refine ⟨by rwa [div_eq_mul_inv], ?_⟩
  calc (⌈B * Real.log (n + 1)⌉₊ : ℝ) * (Real.sqrt (2 / σ) / ((n + 1 : ℕ) : ℝ) ^ (1 / 12 : ℝ))
      ≤ (B * Real.log (n + 1) + 1) * (Real.sqrt (2 / σ) / ((n + 1 : ℕ) : ℝ) ^ (1 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (mul_nonneg hB hlog)).le (by positivity)
    _ = B * Real.sqrt (2 / σ) *
          (Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 / 12 : ℝ)) +
        Real.sqrt (2 / σ) * (((n + 1 : ℕ) : ℝ) ^ (1 / 12 : ℝ))⁻¹ := by
        push_cast
        ring
    _ ≤ δ := hn₂

end TauCeti

namespace ProbabilityTheory.iIndepFun

variable {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  {P : Measure Ω} {Q : Measure Ω'} {S : Measure Ω''}
  {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {X : Ω' → ℂ} {Y : Ω'' → ℝ}

local notation "e₀" => (⟨(0, 1), by decide⟩ : StrictUpper)

/-- At truncation radius `(n + 1) ^ (1 / 3)`, the expected real traces of the `2 * k`th powers of
the zero-diagonal centered truncated corners of size `n + 1` are at most `(n + 1) * t₂ ^ (2 * k)`.
This holds once the parameter `γ` of the Füredi–Komlós bound for the second-moment scale
`t₁ / 2` satisfies `γ ≤ 1` and `k * γ ≤ t₂ / t₁ - 1`. -/
private theorem integral_re_trace_pow_wignerMatrix_centeredTruncation_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q) (hX : MemLp X 2 Q)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (hσ : ∫ ω, ‖X ω‖ ^ 2 ∂Q ≤ (t₁ / 2) ^ 2) {n k : ℕ}
    (hγ : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) /
      (t₁ / 2 * Real.sqrt ((n + 1 : ℕ) : ℝ))) ≤ 1)
    (hkγ : (k : ℝ) * Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) /
      (t₁ / 2 * Real.sqrt ((n + 1 : ℕ) : ℝ))) ≤ t₂ / t₁ - 1) :
    ∫ ω, ((wignerMatrix (fun ij ↦ TauCeti.Probability.centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ), Real.rpow_nonneg (Nat.cast_nonneg _) _⟩)
      (fun _ _ ↦ 0) (n + 1) ω) ^ (2 * k)).trace.re ∂P ≤ ((n + 1 : ℕ) : ℝ) * t₂ ^ (2 * k) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  set γ := Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) /
    (t₁ / 2 * Real.sqrt ((n + 1 : ℕ) : ℝ)))
  -- For `σ = t₁ / 2`, `σ * γ ^ 2 * √(n + 1)` is exactly `2 * R`, the bound on the centered
  -- truncations at radius `R = (n + 1) ^ (1 / 3)`.
  have hR : 2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤
      t₁ / 2 * γ ^ 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    exact (by field_simp : t₁ / 2 * (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) /
      (t₁ / 2 * Real.sqrt ((n + 1 : ℕ) : ℝ))) * Real.sqrt ((n + 1 : ℕ) : ℝ) =
        2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ)).ge
  have hcorner : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P :=
    hind.precomp Subtype.val_injective
  have htrace := hcorner.norm_integral_trace_pow_wignerMatrix_centeredTruncation_le
    (fun ij _ ↦ (hid ij).symm.memLp_snd hX)
    (fun ij _ ↦ by
      simpa only [Function.comp_apply] using
        ((hid ij).comp (measurable_norm.pow_const 2)).integral_eq.trans_le hσ)
    (half_pos ht₁).le (Real.sqrt_nonneg _) hγ
    ⟨((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ), Real.rpow_nonneg (Nat.cast_nonneg _) _⟩ hR (2 * k)
  have hint : Integrable (fun ω ↦ ((wignerMatrix (fun ij ↦
      TauCeti.Probability.centeredTruncation (ξ ij) P
        ⟨((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ), Real.rpow_nonneg (Nat.cast_nonneg _) _⟩)
      (fun _ _ ↦ 0) (n + 1) ω) ^ (2 * k)).trace) P :=
    integrable_trace_pow_wignerMatrix (fun _ ↦ inferInstance) (fun ij _ ↦
      (hid ij).aestronglyMeasurable_fst.memLp_centeredTruncation _) (fun _ _ ↦ memLp_const 0)
  -- The base `σ * (2 + 2 * k * γ) = t₁ * (1 + k * γ)` is at most `t₂`.
  have hbase : t₁ / 2 * (2 + ((2 * k : ℕ) : ℝ) * γ) ≤ t₂ := by
    calc t₁ / 2 * (2 + ((2 * k : ℕ) : ℝ) * γ) = t₁ + t₁ * (k * γ) := by push_cast; ring
      _ ≤ t₁ + t₁ * (t₂ / t₁ - 1) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hkγ ht₁.le)
      _ = t₂ := by field_simp; ring
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  refine hre.trans_le ((Complex.re_le_norm _).trans (htrace.trans ?_))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) (Nat.cast_nonneg _)

/-- Let the upper entries be independent with a common centered law of second moment `v` and
finite fourth moment, and let the diagonal entries, possibly dependent, share a law of finite
second moment. Then the largest and smallest eigenvalues of the normalized corners converge
almost surely to `2 * √v` and `-(2 * √v)`, provided the following trace bound holds at each
threshold `r > 2 * √v`. For all sufficiently large `n`, the expected real trace of the
`2 * k n`-th power of the zero-diagonal centered truncation of size `n + 1` at radius `(n+1)^a`,
with `a > 1/4`, is at most `C * (n + 1)^d * t^(2 * k n)`; the bound need not hold for small `n`.
The scale `0 < t < r`, the constants `B`, `C`, `d` and the orders `k n` may depend on `r`. The
orders satisfy `k n ≥ B * log (n + 1)` eventually and `2 * B * log (r/t) > d+1`. At `v = 1` the
limits are `2` and `-2`. -/
theorem
    ae_tendsto_eigenvalues₀_zero_and_card_sub_one_wignerMatrix_of_integral_re_trace_pow_two_mul_le
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q)
    (hξ : MemLp X 4 Q) (hmean : ∫ ω, X ω ∂Q = 0) {v : ℝ≥0} (hvar : ∫ ω, ‖X ω‖ ^ 2 ∂Q = v)
    (hd : ∀ i, IdentDistrib (η i) Y P S) (hη : MemLp Y 2 S)
    {a : ℝ} (ha : 1 / 4 < a)
    (htrace : ∀ r > 2 * Real.sqrt v, ∃ (t B C d : ℝ) (k : ℕ → ℕ), 0 < t ∧ t < r ∧
      d + 1 < 2 * B * Real.log (r / t) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, ((wignerMatrix (fun ij ↦
        TauCeti.Probability.centeredTruncation (ξ ij) P
          ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
        (fun _ _ ↦ 0) (n + 1) ω ^ (2 * k n)).trace).re ∂P) ≤
        C * (n + 1 : ℝ) ^ d * t ^ (2 * k n))) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦
          (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⟨0, Fintype.card_pos⟩)
        atTop (𝓝 (2 * Real.sqrt v)) ∧
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀
          ⟨Fintype.card (Fin (n + 1)) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩)
        atTop (𝓝 (-(2 * Real.sqrt v))) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let B (n : ℕ) (ω : Ω) :=
    wignerMatrix (fun ij ↦ TauCeti.Probability.centeredTruncation (ξ ij) P
      ⟨((n + 1 : ℕ) : ℝ) ^ a, Real.rpow_nonneg (by positivity) _⟩)
      (fun _ _ ↦ 0) (n + 1) ω
  let Z (n : ℕ) (ω : Ω) := wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω
  have hZ n ω : (Z n ω).IsHermitian := wignerMatrix_isHermitian _ _ _ _
  have hnorm : ∀ᵐ ω ∂P, ∀ r > 2 * Real.sqrt v, ∀ᶠ n in atTop, ‖B n ω‖ < r := by
    apply ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_two_mul_le (A := B)
      (.of_forall fun n ↦ .of_forall fun ω ↦ wignerMatrix_isHermitian _ _ ω (n + 1))
    intro r hr
    obtain ⟨t, b, C, d, k, ht, htr, hb, hk, htrace'⟩ := htrace r hr
    refine ⟨t, b, C, d, k, ht, htr, hb, hk, .of_forall fun n ↦ ?_, ?_⟩
    · have hi : Integrable (fun ω ↦ ((B n ω) ^ (2 * k n)).trace) P :=
        integrable_trace_pow_wignerMatrix (fun _ ↦ inferInstance) (fun ij _ ↦
          (hid ij).aestronglyMeasurable_fst.memLp_centeredTruncation _) (fun _ _ ↦ memLp_const 0)
      exact hi.re
    · simpa only [B, RCLike.re_to_complex] using htrace'
  have happrox : ∀ᵐ ω ∂P, Tendsto (fun n ↦ ‖Z n ω - B n ω‖) atTop (𝓝 0) := by
    simpa only [B, Z] using
      ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_centeredTruncation
        (η := fun _ _ ↦ 0)
        (fun _ i ↦ iIndepFun_wignerMatrix_offDiag_row i (hind.precomp Subtype.val_injective))
        hid hξ hmean ha
  have hweak := ae_tendsto_spectralMeasure_wignerMatrix_zero_of_memLp hind
    (fun ij ↦ (hid ij).trans (hid e₀).symm)
    (((hid e₀).symm.memLp_snd hξ).mono_exponent (by norm_num))
    ((hid e₀).integral_eq.trans hmean) v (by
      simpa only [Function.comp_apply] using
        ((hid e₀).comp (measurable_norm.pow_const 2)).integral_eq.trans hvar)
  have hdiag := ae_tendsto_l2_opNorm_wignerMatrix_sub_wignerMatrix_zero (ξ := ξ) hd hη
  filter_upwards [hnorm, happrox, hweak, hdiag] with ω hn hdiff hw hdω
  -- The norm bounds pass from the truncations to the zero-diagonal corners.
  obtain ⟨hmax, hmin⟩ := tendsto_eigenvalues₀_zero_and_card_sub_one_of_eventually_l2_opNorm_lt
    (hA := fun n ↦ hZ n ω) hw (by simp [support_semicircleReal]) (by simp [support_semicircleReal])
    (hdiff.eventually_norm_lt_of_eventually_norm_lt hn)
  -- The diagonal perturbation has vanishing operator norm.
  exact ⟨hmax.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
      (fun n ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hdω,
    hmin.eigenvalues₀_of_tendsto_l2_opNorm_sub_zero
      (fun n ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hdω⟩

/-- **Edge limits of Wigner matrices.** Let the upper entries be independent with a common
centered law of second moment `v` and finite fourth moment, and let the diagonal entries, possibly
dependent, share a law of finite second moment. Then almost surely the largest and smallest
eigenvalues of the normalized corners converge to `2 * √v` and `-(2 * √v)`. At `v = 1` the limits
are `2` and `-2`. -/
theorem ae_tendsto_eigenvalues₀_zero_and_card_sub_one_wignerMatrix
    (hind : iIndepFun ξ P) (hid : ∀ ij, IdentDistrib (ξ ij) X P Q)
    (hξ : MemLp X 4 Q) (hmean : ∫ ω, X ω ∂Q = 0) {v : ℝ≥0} (hvar : ∫ ω, ‖X ω‖ ^ 2 ∂Q = v)
    (hd : ∀ i, IdentDistrib (η i) Y P S) (hη : MemLp Y 2 S) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦
          (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⟨0, Fintype.card_pos⟩)
        atTop (𝓝 (2 * Real.sqrt v)) ∧
      Tendsto (fun n : ℕ ↦ (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀
          ⟨Fintype.card (Fin (n + 1)) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩)
        atTop (𝓝 (-(2 * Real.sqrt v))) := by
  refine
    ae_tendsto_eigenvalues₀_zero_and_card_sub_one_wignerMatrix_of_integral_re_trace_pow_two_mul_le
      hind hid hξ hmean hvar hd hη (a := 1 / 3) (by norm_num) fun r hr ↦ ?_
  -- Choose `2 * √v < t₁ < t₂ < r`, the second-moment scale `t₁ / 2` and orders of size `log n`.
  obtain ⟨t₁, ht₁, ht₁r⟩ := exists_between hr
  obtain ⟨t₂, ht₁₂, ht₂r⟩ := exists_between ht₁r
  have ht₁₀ : 0 < t₁ := (mul_nonneg zero_le_two (Real.sqrt_nonneg _)).trans_lt ht₁
  have hσ : (v : ℝ) ≤ (t₁ / 2) ^ 2 := by
    calc (v : ℝ) = Real.sqrt v ^ 2 := (Real.sq_sqrt v.coe_nonneg).symm
      _ ≤ (t₁ / 2) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (by linarith) 2
  have hlog : 0 < Real.log (r / t₂) := Real.log_pos ((one_lt_div (ht₁₀.trans ht₁₂)).mpr ht₂r)
  refine ⟨t₂, 2 / Real.log (r / t₂), 1, 1, fun n ↦ ⌈2 / Real.log (r / t₂) * Real.log (n + 1)⌉₊,
    ht₁₀.trans ht₁₂, ht₂r, ?_, .of_forall fun n ↦ Nat.le_ceil _, ?_⟩
  · rw [mul_assoc, div_mul_cancel₀ _ hlog.ne']
    norm_num
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hX : MemLp X 2 Q :=
    (hid e₀).memLp_snd (((hid e₀).symm.memLp_snd hξ).mono_exponent (by norm_num))
  filter_upwards [eventually_sqrt_le_one_and_ceil_mul_sqrt_le (half_pos ht₁₀)
    (div_nonneg zero_le_two hlog.le) (sub_pos.mpr ((one_lt_div ht₁₀).mpr ht₁₂))]
    with n ⟨hγ, hkγ⟩
  refine (hind.integral_re_trace_pow_wignerMatrix_centeredTruncation_le hid hX ht₁₀
    (hvar.trans_le hσ) hγ hkγ).trans_eq ?_
  rw [Real.rpow_one, one_mul, Nat.cast_add_one]

end ProbabilityTheory.iIndepFun
