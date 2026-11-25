/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# The Paley–Zygmund inequality and anti-concentration

The **Paley–Zygmund inequality** bounds the probability that a nonnegative square-integrable
random variable exceeds a fraction of its mean from below: for `0 ≤ θ ≤ 1`,

`(1 - θ)² (E Z)² ≤ E Z² · P(Z > θ E Z)`

(`TauCeti.one_sub_sq_mul_sq_integral_le_integral_sq_mul_measureReal_lt`). It is the lower-tail
counterpart of Chebyshev's inequality.

Applied to `Z = (X - v)²`, it shows that a centred random variable `X` with `E X² ≥ 1` and a finite
fourth moment is not concentrated near any point: for `|r| ≤ 1` and every `v`,

`P(|X - v| ≤ r) ≤ 1 - (1 - r²)² / (8 B)` whenever `E X⁴ ≤ B`

(`TauCeti.measureReal_abs_sub_le_le_one_sub_div`). Bounds of this kind on the concentration
function `sup_v P(|X - v| ≤ r)` of the entries are the input of small-ball estimates for sums of
independent random variables, and so of lower bounds for the least singular value of random
matrices. The radius must be below `1` for the bound to be informative: a variable equal to
`±(1 - δ)` with probability close to `1` has `E X² ≥ 1` for a suitable small mass far away,
yet puts almost all of its mass in the open interval of radius `1` around `0`.

## References

* R. E. A. C. Paley and A. Zygmund, *On some series of functions (3)*, Proc. Cambridge Philos.
  Soc. 28 (1932), 190–205.
* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009), Lemma 3.2 of the preprint
  arXiv:0802.3956v4, which bounds the concentration function of a variable with unit variance
  and finite fourth moment by the same argument.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The Paley–Zygmund inequality.** A nonnegative square-integrable random variable `Z`
exceeds `θ E Z`, for `0 ≤ θ ≤ 1`, with probability at least `(1 - θ)² (E Z)² / E Z²`; this is
stated without division, as `(1 - θ)² (E Z)² ≤ E Z² · P(Z > θ E Z)`. It holds for every measure
of total mass at most `1`. -/
theorem one_sub_sq_mul_sq_integral_le_integral_sq_mul_measureReal_lt
    {Z : Ω → ℝ} (hZ0 : 0 ≤ᵐ[μ] Z) (hZ : MemLp Z 2 μ) (hμ : μ Set.univ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω, Z ω ∂μ < Z ω} := by
  have : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  set m := ∫ ω, Z ω ∂μ
  set S := {ω | θ * m < Z ω}
  have hm : 0 ≤ m := integral_nonneg_of_ae hZ0
  have hZi : Integrable Z μ := hZ.integrable one_le_two
  have hS : NullMeasurableSet S μ :=
    nullMeasurableSet_lt aemeasurable_const hZ.aestronglyMeasurable.aemeasurable
  -- Off `S` the variable is at most `θ m`, so `S` carries at least `(1 - θ) m` of the mean.
  have hout : ∫ ω in Sᶜ, Z ω ∂μ ≤ θ * m := by
    calc ∫ ω in Sᶜ, Z ω ∂μ ≤ ∫ _ in Sᶜ, θ * m ∂μ :=
          setIntegral_mono_on₀ hZi.integrableOn integrableOn_const hS.compl
            fun ω hω ↦ not_lt.1 hω
      _ = μ.real Sᶜ * (θ * m) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ θ * m := mul_le_of_le_one_left (by positivity) ((measureReal_mono (Set.subset_univ _)
          (measure_ne_top _ _)).trans (ENNReal.toReal_le_of_le_ofReal zero_le_one
            (by rwa [ENNReal.ofReal_one])))
  have hin : (1 - θ) * m ≤ ∫ ω in S, Z ω ∂μ := by
    linarith [integral_add_compl₀ hS hZi]
  -- The Cauchy–Schwarz inequality on `S` bounds that part of the mean.
  calc (1 - θ) ^ 2 * m ^ 2 = ((1 - θ) * m) ^ 2 := by ring
    _ ≤ (∫ ω in S, Z ω ∂μ) ^ 2 := pow_le_pow_left₀ (by nlinarith) hin 2
    _ ≤ μ.real S * ∫ ω in S, Z ω ^ 2 ∂μ :=
        sq_setIntegral_le_measureReal_mul_setIntegral_sq Z S (measure_ne_top _ _)
          hZ.integrable_sq.integrableOn
    _ ≤ μ.real S * ∫ ω, Z ω ^ 2 ∂μ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hZ.integrable_sq (.of_forall fun _ ↦ sq_nonneg _))
        measureReal_nonneg
    _ = _ := mul_comm _ _

/-- The moments of `Z = (X - v)²` for a centred `X` with `E X² ≥ 1` and `E X⁴ ≤ B`: the bound
`B` is at least `1`, and `Z` is square integrable with `E Z = E X² + v²` and
`E Z² ≤ 8 (B + v⁴)`. -/
private theorem one_le_and_memLp_sub_sq_and_integral [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 4 μ)
    (hmean : ∫ ω, X ω ∂μ = 0) (hvar : 1 ≤ ∫ ω, X ω ^ 2 ∂μ) {B : ℝ}
    (hB : ∫ ω, X ω ^ 4 ∂μ ≤ B) (v : ℝ) :
    1 ≤ B ∧ MemLp (fun ω ↦ (X ω - v) ^ 2) 2 μ ∧
      ∫ ω, (X ω - v) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ + v ^ 2 ∧
      ∫ ω, ((X ω - v) ^ 2) ^ 2 ∂μ ≤ 8 * (B + v ^ 4) := by
  have hpow (Y : Ω → ℝ) (hY : MemLp Y 4 μ) : Integrable (fun ω ↦ Y ω ^ 4) μ := by
    simpa [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩] using
      hY.integrable_norm_pow (p := 4) (by norm_num)
  have hX4 := hpow X hX
  have hX2 : MemLp X 2 μ := hX.mono_exponent (by norm_num)
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hXv : MemLp (fun ω ↦ X ω - v) 4 μ := hX.sub (memLp_const v)
  have hm2 : AEStronglyMeasurable (fun ω ↦ (X ω - v) ^ 2) μ := hXv.aestronglyMeasurable.pow 2
  have hZ : MemLp (fun ω ↦ (X ω - v) ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq hm2).2 (by simpa only [← pow_mul] using hpow _ hXv)
  refine ⟨?_, hZ, ?_, ?_⟩
  · -- The fourth moment is at least the square of the second moment.
    have hX4' : Integrable (fun ω ↦ (X ω ^ 2) ^ 2) μ := by simpa only [← pow_mul] using hX4
    have h := hX4'.abs_integral_le_sqrt_integral_sq measure_univ.le
    simp only [← pow_mul] at h
    nlinarith [Real.sq_sqrt (integral_nonneg fun ω ↦ by positivity : (0 : ℝ) ≤ ∫ ω, X ω ^ 4 ∂μ),
      le_abs_self (∫ ω, X ω ^ 2 ∂μ), Real.sqrt_nonneg (∫ ω, X ω ^ 4 ∂μ)]
  · have h (ω : Ω) : (X ω - v) ^ 2 = X ω ^ 2 - 2 * v * X ω + v ^ 2 := by ring
    have hi : Integrable (fun ω ↦ X ω ^ 2 - 2 * v * X ω) μ :=
      hX2.integrable_sq.sub (hXi.const_mul _)
    simp_rw [h]
    rw [integral_add hi (integrable_const _), integral_sub hX2.integrable_sq (hXi.const_mul _),
      integral_const_mul, hmean]
    simp
  · calc ∫ ω, ((X ω - v) ^ 2) ^ 2 ∂μ ≤ ∫ ω, 8 * (X ω ^ 4 + v ^ 4) ∂μ :=
          integral_mono hZ.integrable_sq ((hX4.add (integrable_const _)).const_mul _)
            fun ω ↦ by
              nlinarith [sq_nonneg (X ω + v), sq_nonneg (X ω - v), sq_nonneg (X ω ^ 2 - v ^ 2)]
      _ ≤ 8 * (B + v ^ 4) := by
          rw [integral_const_mul, integral_add hX4 (integrable_const _)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          linarith

/-- **Anti-concentration from the fourth moment.** A centred random variable `X` with
`E X² ≥ 1` and fourth moment `E X⁴ ≤ B` puts mass at most `1 - (1 - r²)² / (8 B)` in every
closed interval `[v - r, v + r]` of radius `|r| ≤ 1`. -/
theorem measureReal_abs_sub_le_le_one_sub_div [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 4 μ)
    (hmean : ∫ ω, X ω ∂μ = 0) (hvar : 1 ≤ ∫ ω, X ω ^ 2 ∂μ) {B : ℝ}
    (hB : ∫ ω, X ω ^ 4 ∂μ ≤ B) (v : ℝ) {r : ℝ} (hr : |r| ≤ 1) :
    μ.real {ω | |X ω - v| ≤ r} ≤ 1 - (1 - r ^ 2) ^ 2 / (8 * B) := by
  obtain ⟨hM, hZ, hEZ, hEZ2⟩ := one_le_and_memLp_sub_sq_and_integral hX hmean hvar hB v
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [abs_nonneg r, sq_abs r]
  rcases lt_or_ge r 0 with hr0 | hr0
  · have hempty : {ω | |X ω - v| ≤ r} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω ↦ (abs_nonneg _).not_gt (hω.trans_lt hr0)
    rw [hempty, measureReal_empty, sub_nonneg, div_le_one (by positivity)]
    nlinarith
  -- Paley–Zygmund for `Z = (X - v)²` at the level `r² = θ E Z`, where `E Z ≥ 1 + v²`.
  obtain ⟨E, hE⟩ : ∃ E, ∫ ω, (X ω - v) ^ 2 ∂μ = E := ⟨_, rfl⟩
  rw [hE] at hEZ
  have hE1 : 1 + v ^ 2 ≤ E := by rw [hEZ]; linarith
  have hEpos : 0 < E := by nlinarith [sq_nonneg v, hE1]
  have hpz := one_sub_sq_mul_sq_integral_le_integral_sq_mul_measureReal_lt
    (.of_forall fun _ ↦ sq_nonneg _) hZ measure_univ.le (θ := r ^ 2 / E) (by positivity)
    ((div_le_one hEpos).2 (by linarith [sq_nonneg v, hE1]))
  have hset : {ω | r ^ 2 / E * E < (X ω - v) ^ 2} = {ω | |X ω - v| ≤ r}ᶜ := by
    ext ω
    simp [div_mul_cancel₀ _ hEpos.ne', sq_lt_sq, abs_of_nonneg hr0]
  have habs : AEMeasurable (fun ω ↦ |X ω - v|) μ := continuous_abs.measurable.comp_aemeasurable
    ((hX.sub (memLp_const v)).aestronglyMeasurable.aemeasurable)
  rw [hE, hset, probReal_compl_eq_one_sub₀ (nullMeasurableSet_le habs aemeasurable_const)]
    at hpz
  set p := μ.real {ω | |X ω - v| ≤ r}
  have hq : 0 ≤ 1 - p := sub_nonneg.2 measureReal_le_one
  -- `(1 - r² / E) E = E - r² ≥ (1 - r²) (1 + v²)`, and `(1 + v²)² ≥ 1 + v⁴`.
  have hlow : (1 - r ^ 2) * (1 + v ^ 2) ≤ (1 - r ^ 2 / E) * E := by
    rw [(by field_simp : (1 - r ^ 2 / E) * E = E - r ^ 2)]
    nlinarith [hE1]
  have hA : (1 - r ^ 2) ^ 2 * (1 + v ^ 4) ≤ 8 * (B + v ^ 4) * (1 - p) := by
    have h1 : 0 ≤ (1 - r ^ 2) * (1 + v ^ 2) := by nlinarith [sq_nonneg v]
    have h2 : ((1 - r ^ 2) * (1 + v ^ 2)) ^ 2 ≤ (1 - r ^ 2 / E) ^ 2 * E ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h1 hlow 2
    nlinarith [sq_nonneg v, sq_nonneg (1 - r ^ 2), mul_le_mul_of_nonneg_right hEZ2 hq]
  -- Since `B ≥ 1`, the factor `(1 + v⁴) / (B + v⁴)` is at least `1 / B`.
  have hAB : (1 - r ^ 2) ^ 2 ≤ 8 * B * (1 - p) := by
    by_contra! h
    nlinarith [mul_nonneg hq (sq_nonneg (v ^ 2)), sq_nonneg (v ^ 2)]
  rw [le_sub_comm, div_le_iff₀ (by positivity)]
  linarith

end TauCeti
