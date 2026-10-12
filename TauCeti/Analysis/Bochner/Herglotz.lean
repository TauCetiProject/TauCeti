/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.PontryaginMeasure
public import TauCeti.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Group.Circle
import TauCeti.MeasureTheory.Group.Circle
import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Herglotz's theorem: Bochner's theorem on the integers

A function `φ : ℤ → ℂ` is positive definite, `∑ᵢ ∑ⱼ cᵢ conj(cⱼ) φ(nᵢ - nⱼ) ≥ 0` for every finite
family, if and only if it is the sequence of moments `φ n = ∫ zⁿ dμ(z)` of a finite positive
measure `μ` on the unit circle. This is Herglotz's theorem. The unit circle is the Pontryagin dual
of `ℤ`, the point `z` corresponding to the character `n ↦ zⁿ`, so the theorem is Bochner's
theorem for the discrete group `ℤ`: the positive-definite functions on `ℤ` are exactly the
Fourier–Stieltjes transforms `MeasureTheory.FiniteMeasure.pontryaginMeasureTransform` of finite
measures on its dual, identified with the circle by `TauCeti.circleEquivPontryaginDualInt`.
In that Pontryagin form it is the case `G = ℤ` of
`TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq` in
`TauCeti.Analysis.Bochner.DiscreteGroup`.
Every function on the discrete group `ℤ` is continuous, so no continuity hypothesis appears.

The measure is obtained from Fejér means. For `N ≥ 1` the trigonometric polynomial

`F_N(z) = N⁻¹ ∑_{a, b < N} φ(a - b) conj(z)ᵃ zᵇ`

is `N⁻¹` times the positive-definiteness form of `φ` at the points `0, …, N - 1` with weights
`conj(z)ᵃ`, hence nonnegative. The measure `ν_N` with density `F_N` against normalized arc length
has total mass `φ 0`, and by the orthogonality of the characters `z ↦ zⁿ` its moments are
`∫ zⁿ dν_N = (1 - |n| / N)₊ φ n`, the number of pairs `(a, b)` with `a - b = n` divided by `N`.
A weak cluster point of the `ν_N`, which exists by Prokhorov's theorem on the compact circle,
has moments `φ n`.

## Main declarations

* `TauCeti.exists_isFiniteMeasure_integral_zpow_eq`: **Herglotz's theorem**, a positive-definite
  function on `ℤ` is the moment sequence of a finite measure on the circle.
* `TauCeti.isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq`: the resulting
  characterization of positive-definite functions on `ℤ`.
* `MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_map_circleEquivPontryaginDualInt`: the
  Fourier–Stieltjes transform of a measure carried from the circle to the dual of `ℤ` is its moment
  sequence.

## References

* G. Herglotz, *Über Potenzreihen mit positivem, reellem Teil im Einheitskreis*, Ber. Verh.
  Sächs. Akad. Wiss. Leipzig **63** (1911), 501–511.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press
  (2004), Chapter I, §7 (positive-definite sequences and Herglotz's theorem via Fejér means).
* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), §1.4 (Bochner's theorem on a
  locally compact abelian group).
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory Metric Set Filter Finset
open scoped ComplexOrder Topology NNReal

namespace TauCeti

/-! ### Fejér means of a positive-definite function -/

variable {φ : ℤ → ℂ}

/-- The Fejér quadratic form `∑_{a, b < N} conj(z)ᵃ conj(conj(z)ᵇ) φ(a - b)`: the
positive-definiteness form of `φ` at the points `0, …, N - 1` with weights `conj(z)ᵃ`. -/
private def fejerSum (φ : ℤ → ℂ) (N : ℕ) (ζ : ℂ) : ℂ :=
  ∑ a ∈ range N, ∑ b ∈ range N, conj ζ ^ a * conj (conj ζ ^ b) * φ (a - b)

private lemma fejerSum_nonneg (hφ : IsPositiveDefiniteSub φ) (N : ℕ) (ζ : ℂ) :
    0 ≤ fejerSum φ N ζ := by
  have h := isPositiveDefiniteSub_iff_forall_sum_nonneg.mp hφ N (fun i ↦ conj ζ ^ (i : ℕ))
    (fun i ↦ ((i : ℕ) : ℤ))
  simpa only [fejerSum, Finset.sum_range] using h

private lemma continuous_fejerSum (N : ℕ) : Continuous (fejerSum φ N) := by
  unfold fejerSum
  fun_prop

/-- On the unit circle, `conj z = z⁻¹`, so each term of the Fejér form times `zᵐ` is a power of
`z`. -/
private lemma fejerSum_mul_zpow {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (N : ℕ) (m : ℤ) :
    fejerSum φ N ζ * ζ ^ m =
      ∑ p ∈ range N ×ˢ range N, φ (p.1 - p.2) * ζ ^ (m + p.2 - p.1) := by
  have hnorm : ‖ζ‖ = 1 := by simpa using hζ
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hnorm
  rw [fejerSum, Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have key : ζ⁻¹ ^ a * ζ ^ b * ζ ^ m = ζ ^ (m + b - a) := by
    simp only [← zpow_natCast, inv_zpow', ← zpow_add₀ hζ0]
    ring_nf
  rw [map_pow, conj_conj, ← inv_eq_conj hnorm, ← key]
  ring

/-- The number of pairs `(a, b)` with `a, b < N` and `a - b = m`. -/
private def fejerCount (N : ℕ) (m : ℤ) : ℕ :=
  #{p ∈ range N ×ˢ range N | (p.1 : ℤ) - p.2 = m}

private lemma fejerCount_le (N : ℕ) (m : ℤ) : fejerCount N m ≤ N := by
  refine (Finset.card_le_card_of_injOn Prod.fst (fun p hp ↦ ?_) fun p hp q hq hpq ↦ ?_).trans
    (card_range N).le
  · simp only [coe_filter, mem_product, Finset.mem_range, Set.mem_ofPred_eq] at hp
    simpa using hp.1.1
  · simp only [coe_filter, mem_product, Finset.mem_range, Set.mem_ofPred_eq] at hp hq
    exact Prod.ext hpq (by omega)

private lemma le_fejerCount_add (N : ℕ) (m : ℤ) : N ≤ fejerCount N m + m.natAbs := by
  have h : N - m.natAbs ≤ fejerCount N m := by
    rw [← card_range (N - m.natAbs)]
    refine Finset.card_le_card_of_injOn (fun k ↦ (k + m.toNat, k + (-m).toNat))
      (fun k hk ↦ ?_) fun k _ l _ hkl ↦ by simpa using congrArg Prod.fst hkl
    simp only [coe_range, Set.mem_Iio] at hk
    simp only [coe_filter, mem_product, Finset.mem_range, Set.mem_ofPred_eq]
    omega
  omega

/-- The Fejér count, normalized by `N`, tends to `1`. -/
private lemma tendsto_fejerCount (m : ℤ) :
    Tendsto (fun N : ℕ ↦ (fejerCount (N + 1) m : ℝ) / (N + 1)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun N : ℕ ↦ 1 - (m.natAbs : ℝ) / (N + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat
      (m.natAbs : ℝ) |>.comp (tendsto_add_atTop_nat 1))
  have hpos (N : ℕ) : (0 : ℝ) < N + 1 := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N ↦ ?_)
    fun N ↦ ?_
  · have h : ((N + 1 : ℕ) : ℝ) ≤ ((fejerCount (N + 1) m + m.natAbs : ℕ) : ℝ) :=
      Nat.cast_le.mpr (le_fejerCount_add (N + 1) m)
    push_cast at h
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ (hpos N), one_mul]
    linarith
  · have h : ((fejerCount (N + 1) m : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (fejerCount_le (N + 1) m)
    push_cast at h
    rw [div_le_one (hpos N)]
    exact h

/-- The Fejér density `N⁻¹ F_N` of `φ`, a nonnegative trigonometric polynomial on the circle. -/
private def fejerDensity (φ : ℤ → ℂ) (N : ℕ) (ζ : ℂ) : ℝ :=
  (N : ℝ)⁻¹ * (fejerSum φ N ζ).re

private lemma fejerDensity_nonneg (hφ : IsPositiveDefiniteSub φ) (N : ℕ) (ζ : ℂ) :
    0 ≤ fejerDensity φ N ζ :=
  mul_nonneg (by positivity) (Complex.nonneg_iff.mp (fejerSum_nonneg hφ N ζ)).1

private lemma continuous_fejerDensity (N : ℕ) : Continuous (fejerDensity φ N) :=
  continuous_const.mul (continuous_re.comp (continuous_fejerSum N))

/-- The moments of the Fejér measure: `∫ zᵐ dν_N = (#{(a, b) | a - b = m} / N) φ m`. -/
private lemma integral_zpow_fejerMeasure (hφ : IsPositiveDefiniteSub φ) (N : ℕ) (m : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ m ∂circleDensityMeasure (fejerDensity φ N) =
      ((fejerCount N m / N : ℝ) : ℂ) * φ m := by
  have hzpow (k : ℤ) : ContinuousOn (fun ζ : ℂ ↦ ζ ^ k) (sphere 0 1) :=
    (continuousOn_zpow₀ k).mono fun ζ hζ ↦ by
      rintro rfl
      simp at hζ
  have hav (c : ℂ) (k : ℤ) :
      Real.circleAverage (fun ζ : ℂ ↦ c * ζ ^ k) 0 1 = if k = 0 then c else 0 := by
    have h := Real.circleAverage_fun_smul (a := c) (f := fun ζ : ℂ ↦ ζ ^ k) (c := 0) (R := 1)
    have h0 := circleAverage_sub_zpow (c := 0) (R := 1) k
    simp only [smul_eq_mul, sub_zero] at h h0
    rw [h, h0, mul_ite, mul_one, mul_zero]
  rw [integral_circleDensityMeasure (continuous_fejerDensity N).continuousOn
    (fun ζ _ ↦ fejerDensity_nonneg hφ N ζ) (hzpow m)]
  have hsphere : EqOn (fun ζ : ℂ ↦ fejerDensity φ N ζ • ζ ^ m)
      (fun ζ ↦ ∑ p ∈ range N ×ˢ range N, ((N : ℂ)⁻¹ * φ (p.1 - p.2)) * ζ ^ (m + p.2 - p.1))
      (sphere 0 |1|) := fun ζ hζ ↦ by
    rw [abs_one] at hζ
    have hre : fejerSum φ N ζ = ((fejerSum φ N ζ).re : ℂ) :=
      eq_re_of_ofReal_le (by rw [ofReal_zero]; exact fejerSum_nonneg hφ N ζ)
    simp only [fejerDensity, Complex.real_smul, ofReal_mul, ofReal_inv, ofReal_natCast, ← hre,
      mul_assoc, fejerSum_mul_zpow hζ, Finset.mul_sum]
  have hint (c : ℂ) (k : ℤ) : CircleIntegrable (fun ζ : ℂ ↦ c * ζ ^ k) 0 1 :=
    (continuousOn_const.mul (hzpow k)).circleIntegrable zero_le_one
  rw [Real.circleAverage_congr_sphere hsphere, Real.circleAverage_fun_sum fun p _ ↦ hint _ _]
  simp only [hav]
  -- Only the pairs with `a - b = m` contribute, each by `N⁻¹ φ m`.
  rw [Finset.sum_congr rfl (g := fun p ↦ if (p.1 : ℤ) - p.2 = m then (N : ℂ)⁻¹ * φ m else 0)
    fun p _ ↦ ?_, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, fejerCount]
  · push_cast
    ring
  by_cases h : (p.1 : ℤ) - p.2 = m
  · rw [ite_eq_left (by omega), ite_eq_left h, h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-! ### Herglotz's theorem -/

/-- **Herglotz's theorem.** A positive-definite function `φ` on `ℤ` is the moment sequence
`φ n = ∫ zⁿ dμ(z)` of a finite positive measure `μ` on the unit circle. -/
theorem exists_isFiniteMeasure_integral_zpow_eq (φ : ℤ → ℂ) (hφ : IsPositiveDefiniteSub φ) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧ ∀ n : ℤ, φ n = ∫ z : Circle, (z : ℂ) ^ n ∂μ := by
  -- The Fejér measures `ν N` at levels `N + 1`.
  set ν : ℕ → Measure Circle := fun N ↦ circleDensityMeasure (fejerDensity φ (N + 1))
  have hνfin (N : ℕ) : IsFiniteMeasure (ν N) :=
    isFiniteMeasure_circleDensityMeasure (continuous_fejerDensity _).continuousOn
  have hmoment (N : ℕ) (m : ℤ) : ∫ z : Circle, (z : ℂ) ^ m ∂ν N =
      ((fejerCount (N + 1) m / (N + 1) : ℝ) : ℂ) * φ m := by
    simpa using integral_zpow_fejerMeasure hφ (N + 1) m
  -- Each `ν N` has mass at most `(φ 0).re`.
  let C : ℝ≥0 := ⟨(φ 0).re, hφ.map_zero_re_nonneg⟩
  have hmass (N : ℕ) : ν N univ ≤ C := by
    have h := hmoment N 0
    rw [hφ.map_zero_eq_ofReal_re] at h
    simp only [zpow_zero, integral_const, Complex.real_smul, mul_one, ← ofReal_mul,
      ofReal_inj] at h
    rw [← ofReal_measureReal (measure_ne_top _ _), h, ENNReal.ofReal_le_iff_le_toReal
      ENNReal.coe_ne_top, ENNReal.coe_toReal]
    refine mul_le_of_le_one_left hφ.map_zero_re_nonneg ?_
    rw [div_le_one (by positivity)]
    exact_mod_cast fejerCount_le (N + 1) 0
  -- By Prokhorov's theorem on the compact circle, the `ν N` cluster weakly at some `μ`.
  obtain ⟨μ, U, hU, hμ, -, hlim⟩ :=
    finite_measure_cluster_limit ν C hmass IsTightMeasureSet.of_compactSpace
  refine ⟨μ, hμ, fun m ↦ ?_⟩
  let νf : ℕ → FiniteMeasure Circle := fun N ↦ ⟨ν N, hνfin N⟩
  let μf : FiniteMeasure Circle := ⟨μ, hμ⟩
  have hweak : Tendsto νf U (𝓝 μf) := FiniteMeasure.tendsto_iff_forall_integral_tendsto.2 hlim
  have hcont : Continuous fun z : Circle ↦ (z : ℂ) ^ m :=
    (continuous_subtype_val.comp (continuous_zpow (G := Circle) m)).congr fun z ↦
      Circle.coe_zpow z m
  have hconv := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hweak
    (.mkOfCompact ⟨_, hcont⟩)
  -- The moments of `ν N` converge to `φ m`, and to the moment of `μ`.
  have hφlim : Tendsto (fun N ↦ ∫ z : Circle, (z : ℂ) ^ m ∂ν N) U (𝓝 (φ m)) := by
    simp only [hmoment]
    simpa using (((continuous_ofReal.tendsto 1).comp (tendsto_fejerCount m)).mul_const
      (φ m)).mono_left hU
  exact tendsto_nhds_unique hφlim hconv

section Pontryagin

variable [MeasurableSpace (PontryaginDual (Multiplicative ℤ))]
  [BorelSpace (PontryaginDual (Multiplicative ℤ))]

/-- The Fourier–Stieltjes transform of the image of a finite measure on the circle under
`TauCeti.circleEquivPontryaginDualInt` is its moment sequence. -/
@[simp]
theorem
    _root_.MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_map_circleEquivPontryaginDualInt
    (μ : FiniteMeasure Circle) (n : ℤ) :
    (μ.map circleEquivPontryaginDualInt).pontryaginMeasureTransform n =
      ∫ z : Circle, (z : ℂ) ^ n ∂μ.toMeasure := by
  rw [FiniteMeasure.pontryaginMeasureTransform_apply, FiniteMeasure.toMeasure_map,
    integral_map (map_continuous circleEquivPontryaginDualInt).aemeasurable
      (PontryaginDual.continuous_coe_eval_const _).aestronglyMeasurable]
  simp

end Pontryagin

/-- **Herglotz's theorem**, as a characterization: a function `φ` on `ℤ` is positive definite if
and only if it is the moment sequence `φ n = ∫ zⁿ dμ(z)` of a finite positive measure on the unit
circle. -/
theorem isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq (φ : ℤ → ℂ) :
    IsPositiveDefiniteSub φ ↔
      ∃ μ : Measure Circle, IsFiniteMeasure μ ∧ ∀ n : ℤ, φ n = ∫ z : Circle, (z : ℂ) ^ n ∂μ := by
  refine ⟨exists_isFiniteMeasure_integral_zpow_eq φ, fun ⟨μ, hμ, hrep⟩ ↦ ?_⟩
  -- The moment sequence is the transform of the image measure on the dual of `ℤ`.
  borelize (PontryaginDual (Multiplicative ℤ))
  let μf : FiniteMeasure Circle := ⟨μ, hμ⟩
  have hφ : φ = (μf.map circleEquivPontryaginDualInt).pontryaginMeasureTransform := funext fun n ↦
    (hrep n).trans
      (FiniteMeasure.pontryaginMeasureTransform_map_circleEquivPontryaginDualInt μf n).symm
  exact hφ ▸ (μf.map circleEquivPontryaginDualInt).isPositiveDefiniteSub_pontryaginMeasureTransform

end TauCeti
