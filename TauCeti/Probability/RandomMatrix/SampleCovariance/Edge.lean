/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.HasLaw
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Analysis.Matrix.SampleCovariance.OperatorNorm
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Probability.RandomMatrix.ExtremeEigenvalues
import TauCeti.Probability.RandomMatrix.SampleCovariance.MarchenkoPastur
import TauCeti.Probability.RandomMatrix.SampleCovariance.Trace.Bound
import TauCeti.Probability.RandomMatrix.SampleCovariance.Trace.Integrability
import TauCeti.Probability.RandomMatrix.SampleCovariance.Truncation
import TauCeti.Probability.RandomMatrix.SpectralMoment.Extremes

/-!
# The largest eigenvalue of a sample covariance matrix

Let `Xₙ` be the top-left `p(n) × n` corner of an array of independent complex entries with a
common centred law of unit second absolute moment and finite fourth moment, where
`p(n) / n → y > 0`. The largest eigenvalue of the sample covariance `Sₙ = XₙXₙᴴ/n` converges
almost surely to the upper edge `(1 + √y)²` of the Marchenko–Pastur law `MP_y`.

The proof first reduces the limit to a growing trace bound on the matrices `Tₙ` of centered
truncations of the entries at `n^a`, with `a > 1/4`: for each threshold `r > (1 + √y)²`, the
expected real trace of the `2 kₙ`-th power of the sample covariance of `Tₙ` is eventually at most
`C (n + 1)^d t^(2 kₙ)` with `0 < t < r`, where the orders satisfy `kₙ ≥ B log (n + 1)` eventually
and `2 B log (r / t) > d + 1`. The lower half, that the largest eigenvalue eventually exceeds every
`c < (1 + √y)²`, is a consequence of the almost-sure Marchenko–Pastur law
`TauCeti.Probability.marchenkoPastur_ae`. For the upper half, the trace bound and Borel–Cantelli
give operator-norm bounds for the sample covariance of the truncated corners. These transfer to
`Xₙ / √n`, since the corners and their truncations differ by `o(√n)` in operator norm, and the
largest eigenvalue of `Sₙ` is `‖Xₙ‖² / n`.

The trace bound holds at truncation radius `n ^ (1 / 3)` and orders of logarithmic size, by the
Füredi–Komlós bound `ProbabilityTheory.iIndepFun.norm_integral_trace_pow_sampleCovariance_le`
with the parameter `γ` a constant multiple of `n ^ (-1 / 12)`.

## Main results

* `TauCeti.Probability.ae_tendsto_eigenvalues₀_zero_sampleCovariance`: the almost-sure limit of
  the largest eigenvalue.
* `ae_tendsto_eigenvalues₀_zero_sampleCovariance_of_integral_re_trace_pow_two_mul_le`, in the
  same namespace: its reduction to a growing trace bound.

## References

* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988).
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.15.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ → ℕ} [∀ n, NeZero (p n)]
  {y : ℝ≥0}

/-- Let the entries of an array indexed by `ℕ × ℕ` be independent with a common centred law `ν`
of unit second absolute moment and finite fourth moment, let `p(n) ≥ 1` with `p(n) / n → y > 0`,
and let `Xₙ` be the top-left `p(n) × n` corner. Then the largest eigenvalue of the sample
covariance `XₙXₙᴴ/n` converges almost surely to `(1 + √y)²`, provided the following trace bound
holds at each threshold `r > (1 + √y)²`. For all sufficiently large `n`, the expected real trace
of the `2 * k n`-th power of the sample covariance of the matrix of centered truncations of the
entries of `Xₙ` at `n ^ a`, with `a > 1/4`, is at most `C * (n + 1)^d * t^(2 * k n)`. The scale
`0 < t < r`, the constants `B`, `C`, `d` and the orders `k n` may depend on `r`; the orders
satisfy `k n ≥ B * log (n + 1)` eventually and `2 * B * log (r / t) > d + 1`. -/
theorem ae_tendsto_eigenvalues₀_zero_sampleCovariance_of_integral_re_trace_pow_two_mul_le
    {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hindep : iIndepFun x P) (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1)
    (h4 : MemLp id 4 ν) (hy : 0 < y) (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y))
    {a : ℝ} (ha : 1 / 4 < a)
    (htrace : ∀ r > (1 + √y) ^ 2, ∃ (t B C d : ℝ) (k : ℕ → ℕ), 0 < t ∧ t < r ∧
      d + 1 < 2 * B * Real.log (r / t) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((sampleCovariance
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
          centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω)) ^ (2 * k n)).trace ∂P) ≤
        C * (n + 1 : ℝ) ^ d * t ^ (2 * k n))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (isHermitian_sampleCovariance
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω)).eigenvalues₀
        ⟨0, Fintype.card_pos⟩) atTop (𝓝 ((1 + √y) ^ 2)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let X (n : ℕ) (ω : Ω) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω
  let T (n : ℕ) (ω : Ω) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
    centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
  -- The aspect ratio bounds the row dimension linearly.
  have hK : ∀ᶠ n in atTop, (p n : ℝ) ≤ (y + 1) * n := by
    filter_upwards [hp.eventually (gt_mem_nhds (lt_add_one (y : ℝ))), eventually_gt_atTop 0]
      with n hn hn₀
    exact ((div_le_iff₀ (by exact_mod_cast hn₀)).1 hn.le)
  -- The trace bound controls the covariances of the truncated corners.
  have hnorm : ∀ᵐ ω ∂P, ∀ r > (1 + √y) ^ 2, ∀ᶠ n in atTop, ‖sampleCovariance (T n ω)‖ < r := by
    refine ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_two_mul_le
      (.of_forall fun n ↦ .of_forall fun ω ↦ isHermitian_sampleCovariance _) fun r hr ↦ ?_
    obtain ⟨t, B, C, d, k, ht, htr, hB, hk, hb⟩ := htrace r hr
    refine ⟨t, B, C, d, k, ht, htr, hB, hk, .of_forall fun n ↦ ?_, hb⟩
    exact (integrable_trace_pow_sampleCovariance (fun _ ↦ inferInstance) fun i j ↦
      (hx _).aemeasurable.aestronglyMeasurable.memLp_centeredTruncation _).re
  have happrox := SampleCovariance.ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt hx
    (fun i ↦ hindep.precomp (Prod.mk_right_injective i))
    (fun j ↦ hindep.precomp (Prod.mk_left_injective j)) h4 hmean hK ha
  filter_upwards [hnorm, happrox, marchenkoPastur_ae hx hindep hmean hvar hy hp]
    with ω hT hXT hMP
  -- By the global law, only the upper bound remains.
  refine (tendsto_eigenvalues₀_zero_iff_of_tendsto_marchenkoPastur hMP).2 fun c hc ↦ ?_
  have hc₀ : 0 ≤ c := (sq_nonneg _).trans hc.le
  have hs : 1 + √y < √c := (Real.lt_sqrt (by positivity)).2 hc
  let m := (1 + √y + √c) / 2
  filter_upwards [hT (m ^ 2) (pow_lt_pow_left₀ (by simp only [m]; linarith) (by positivity)
      two_ne_zero),
    hXT.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (√c - (1 + √y)) / 2))] with n hTn hXTn
  rw [eigenvalues₀_zero_sampleCovariance, Fintype.card_fin]
  rw [l2_opNorm_sampleCovariance, Fintype.card_fin] at hTn
  -- Compare the normalized operator norms `‖X‖ / √n` and `‖T‖ / √n`.
  have hTm : ‖T n ω‖ / √n < m := by
    refine (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rwa [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hX : ‖X n ω‖ / √n < √c := calc
    _ ≤ ‖T n ω‖ / √n + ‖X n ω - T n ω‖ / √n := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (norm_le_norm_add_norm_sub' _ _) (Real.sqrt_nonneg _)
    _ < m + (√c - (1 + √y)) / 2 := add_lt_add hTm hXTn
    _ = √c := by ring
  calc
    _ = (‖X n ω‖ / √n) ^ 2 := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    _ < √c ^ 2 := pow_lt_pow_left₀ hX (by positivity) two_ne_zero
    _ = c := Real.sq_sqrt hc₀

/-- At a truncation radius `R` with `(2 * R) ^ 2 ≤ γ ^ 4 * √(m * n)` and `0 ≤ γ ≤ 1`, the
expected real traces of the powers of the sample covariance of the matrices of centered
truncations of the `m × n` corner obey the Füredi–Komlós bound with variance `1`. -/
private theorem integral_re_trace_pow_sampleCovariance_centeredTruncation_le
    {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hindep : iIndepFun x P) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) {m n : ℕ} {γ : ℝ} {R : ℝ≥0}
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) (hR : (2 * (R : ℝ)) ^ 2 ≤ γ ^ 4 * √(m * n)) (k : ℕ) :
    ∫ ω, RCLike.re ((sampleCovariance (Matrix.of fun (i : Fin m) (j : Fin n) ↦
        centeredTruncation (x (i, j)) P R ω)) ^ k).trace ∂P ≤
      m * (1 * (1 + √(m / n) + 2 * k * γ * √(m / n)) * (1 + √(m / n) + 2 * k * γ)) ^ k := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have h2 : MemLp id 2 ν := (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2
    (integrable_of_integral_eq_one hvar)
  have hinj : Function.Injective fun ij : Fin m × Fin n ↦ ((ij.1 : ℕ), (ij.2 : ℕ)) :=
    fun a b h ↦ Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  have hint := integrable_trace_pow_sampleCovariance (P := P) (k := k)
    (X := fun ω ↦ Matrix.of fun (i : Fin m) (j : Fin n) ↦ centeredTruncation (x (i, j)) P R ω)
    (fun _ ↦ inferInstance) fun i j ↦
      (hx _).aemeasurable.aestronglyMeasurable.memLp_centeredTruncation _
  have hbound := ProbabilityTheory.iIndepFun.norm_integral_trace_pow_sampleCovariance_le
    (X := fun ω ↦ Matrix.of fun (i : Fin m) (j : Fin n) ↦ centeredTruncation (x (i, j)) P R ω)
    ((hindep.centeredTruncation fun _ ↦ R).precomp hinj)
    (fun i j ↦ (hx _).aemeasurable.aestronglyMeasurable.centeredTruncation R)
    (fun i j ↦ (hx _).aemeasurable.aestronglyMeasurable.integral_centeredTruncation R)
    (fun i j ↦ .of_forall fun ω ↦ norm_centeredTruncation_le R ω)
    (fun i j ↦ (((hx _).memLp h2).integral_norm_centeredTruncation_sq_le R).trans
      ((hx _).integral_comp (f := fun z : ℂ ↦ ‖z‖ ^ 2) (by fun_prop) |>.trans hvar).le)
    zero_le_one hγ₀ hγ₁ (by simpa only [one_mul, Fintype.card_fin] using hR) k
  rw [Fintype.card_fin, Fintype.card_fin] at hbound
  rw [integral_re hint]
  exact (RCLike.re_le_norm _).trans hbound

omit [∀ n, NeZero (p n)] in
/-- The bases `(1 + sₙ + δₙ * sₙ) * (1 + sₙ + δₙ)` of the trace bounds, with `sₙ = √(p n / n)`,
`δₙ = 2 * (2 * kₙ) * C / n ^ (1 / 12)` and `kₙ = ⌈B * log (n + 1)⌉₊`, tend to the upper edge
`(1 + √y)²`. -/
private theorem tendsto_one_add_sqrt_mul_one_add_sqrt (hp : Tendsto (fun n ↦ (p n : ℝ) / n)
    atTop (𝓝 y)) (B C : ℝ) :
    Tendsto (fun n : ℕ ↦ 1 * (1 + √((p n : ℝ) / n) +
        2 * ((2 * ⌈B * Real.log (n + 1)⌉₊ : ℕ) : ℝ) * (C / (n : ℝ) ^ (1 / 12 : ℝ)) *
          √((p n : ℝ) / n)) * (1 + √((p n : ℝ) / n) +
        2 * ((2 * ⌈B * Real.log (n + 1)⌉₊ : ℕ) : ℝ) * (C / (n : ℝ) ^ (1 / 12 : ℝ))))
      atTop (𝓝 ((1 + √y) ^ 2)) := by
  have hδ : Tendsto (fun n : ℕ ↦ 2 * ((2 * ⌈B * Real.log (n + 1)⌉₊ : ℕ) : ℝ) *
      (C / (n : ℝ) ^ (1 / 12 : ℝ))) atTop (𝓝 0) := by
    have := ((Real.tendsto_natCeil_mul_log_add_div_rpow_atTop_nhds_zero B 1
      (by norm_num : (0 : ℝ) < 1 / 12)).comp tendsto_natCast_atTop_atTop).const_mul (4 * C)
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hs : Tendsto (fun n ↦ √((p n : ℝ) / n)) atTop (𝓝 (√y)) :=
    (Real.continuous_sqrt.tendsto _).comp hp
  have h₁ : Tendsto (fun n ↦ 1 + √((p n : ℝ) / n)) atTop (𝓝 (1 + √y)) :=
    tendsto_const_nhds.add hs
  simpa [sq] using ((h₁.add (hδ.mul hs)).mul (h₁.add hδ)).const_mul 1

omit [∀ n, NeZero (p n)] in
/-- At truncation radius `n ^ (1 / 3)` and orders `kₙ = ⌈B * log (n + 1)⌉₊`, the expected real
traces of the `2 * kₙ`-th powers of the sample covariances of the centered truncated corners are
eventually at most `(y + 1) * (n + 1) * t ^ (2 * kₙ)`, for every `t > (1 + √y)²`. -/
private theorem eventually_integral_re_trace_pow_sampleCovariance_centeredTruncation_le
    {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hindep : iIndepFun x P) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1) (hy : 0 < y)
    (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y)) {t : ℝ} (ht : (1 + √y) ^ 2 < t) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∫ ω, RCLike.re ((sampleCovariance (Matrix.of fun (i : Fin (p n))
        (j : Fin n) ↦ centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ (1 / 3 : ℝ)) ω)) ^
          (2 * ⌈B * Real.log (n + 1)⌉₊)).trace ∂P ≤
      (y + 1) * (n + 1 : ℝ) ^ (1 : ℝ) * t ^ (2 * ⌈B * Real.log (n + 1)⌉₊) := by
  -- The parameter of the Füredi–Komlós bound is `γ = C / n ^ (1 / 12)`, with
  -- `C = 1 + 4 / √(y / 2)`, so that `4 ≤ C * √(y / 2) ≤ C ^ 4 * √(y / 2)`.
  have hc : 0 < √((y : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  set C := 1 + 4 / √((y : ℝ) / 2)
  have hC : 4 ≤ C ^ 4 * √((y : ℝ) / 2) := calc
    (4 : ℝ) ≤ C * √((y : ℝ) / 2) := by simp only [C]; field_simp; linarith
    _ ≤ _ := by gcongr; exact le_self_pow₀ (le_add_of_nonneg_right (by positivity)) (by norm_num)
  -- `γ` is eventually at most `1`.
  have hγ₁ : ∀ᶠ n : ℕ in atTop, C / (n : ℝ) ^ (1 / 12 : ℝ) ≤ 1 := by
    filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C, eventually_gt_atTop 0] with n hn hn₀
    exact (div_le_one (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn₀) _)).mpr hn
  -- Eventually `y / 2 < p n / n < y + 1`.
  filter_upwards [hp.eventually (lt_mem_nhds (half_lt_self (by exact_mod_cast hy))),
    hp.eventually (gt_mem_nhds (lt_add_one (y : ℝ))), hγ₁,
    (tendsto_one_add_sqrt_mul_one_add_sqrt hp B C).eventually (gt_mem_nhds ht),
    eventually_gt_atTop 0] with n hpc hpy hγ₁ hb hn
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- The truncation radius `r = n ^ (1 / 3)` satisfies `(2 * r) ^ 2 ≤ γ ^ 4 * √(p n * n)`, since
  -- `γ ^ 4 = C ^ 4 / r`, `r ^ 3 = n` and `√(y / 2) * n ≤ √(p n * n)`.
  have hR : (2 * (((n : ℝ≥0) ^ (1 / 3 : ℝ) : ℝ≥0) : ℝ)) ^ 2 ≤
      (C / (n : ℝ) ^ (1 / 12 : ℝ)) ^ 4 * √(p n * n) := by
    have h₄ : ((n : ℝ) ^ (1 / 12 : ℝ)) ^ 4 = (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_mul_natCast hn₀.le]
      norm_num
    have h₃ : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = n := by
      simpa [one_div] using Real.rpow_inv_natCast_pow hn₀.le (n := 3) three_ne_zero
    have hsqrt : √((y : ℝ) / 2) * n ≤ √(p n * n) := calc
      _ = √((y : ℝ) / 2 * n ^ 2) := by rw [Real.sqrt_mul_sq, abs_of_nonneg hn₀.le]
      _ ≤ √(p n * n) := by
        refine Real.sqrt_le_sqrt ?_
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_div_iff₀ hn₀).1 hpc.le) hn₀.le
    rw [NNReal.coe_rpow, NNReal.coe_natCast, div_pow, h₄, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    calc (2 * (n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 * (n : ℝ) ^ (1 / 3 : ℝ) =
          4 * ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by ring
      _ ≤ C ^ 4 * √((y : ℝ) / 2) * n := by rw [h₃]; gcongr
      _ ≤ C ^ 4 * √(p n * n) := by rw [mul_assoc]; gcongr
  replace hpy := (div_le_iff₀ hn₀).1 hpy.le
  refine (integral_re_trace_pow_sampleCovariance_centeredTruncation_le hx hindep hvar
    (by positivity) hγ₁ hR _).trans ?_
  rw [Real.rpow_one]
  exact mul_le_mul (hpy.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
    (pow_le_pow_left₀ (by positivity) hb.le _) (by positivity) (by positivity)

/-- **Largest eigenvalue of a sample covariance matrix.** Let the entries of an array indexed by
`ℕ × ℕ` be independent with a common centred law `ν` of unit second absolute moment and finite
fourth moment, let `p(n) ≥ 1` with `p(n) / n → y > 0`, and let `Xₙ` be the top-left `p(n) × n`
corner. Then almost surely the largest eigenvalue of the sample covariance `XₙXₙᴴ/n` converges to
`(1 + √y)²`, the upper edge of the Marchenko–Pastur law `MP_y`. -/
theorem ae_tendsto_eigenvalues₀_zero_sampleCovariance
    {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hindep : iIndepFun x P) (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1)
    (h4 : MemLp id 4 ν) (hy : 0 < y) (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (isHermitian_sampleCovariance
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω)).eigenvalues₀
        ⟨0, Fintype.card_pos⟩) atTop (𝓝 ((1 + √y) ^ 2)) := by
  refine ae_tendsto_eigenvalues₀_zero_sampleCovariance_of_integral_re_trace_pow_two_mul_le hx
    hindep hmean hvar h4 hy hp (a := 1 / 3) (by norm_num) fun r hr ↦ ?_
  -- Choose `(1 + √y)² < t < r` and orders `k n = ⌈B * log (n + 1)⌉₊` with `B = 2 / log (r / t)`.
  obtain ⟨t, ht, htr⟩ := exists_between hr
  have ht₀ : 0 < t := lt_of_le_of_lt (sq_nonneg _) ht
  have hlog : 0 < Real.log (r / t) := Real.log_pos ((one_lt_div ht₀).mpr htr)
  refine ⟨t, 2 / Real.log (r / t), y + 1, 1, fun n ↦ ⌈2 / Real.log (r / t) * Real.log (n + 1)⌉₊,
    ht₀, htr, ?_, .of_forall fun n ↦ Nat.le_ceil _,
    eventually_integral_re_trace_pow_sampleCovariance_centeredTruncation_le hx hindep hvar hy hp
      ht (2 / Real.log (r / t))⟩
  rw [mul_assoc, div_mul_cancel₀ _ hlog.ne']
  norm_num

end TauCeti.Probability
