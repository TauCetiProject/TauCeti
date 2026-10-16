/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.PrekopaLeindler

/-!
# Brunn–Minkowski in finite-dimensional Euclidean spaces

The Brunn–Minkowski inequality bounds the outer volume of a Minkowski sum from below
by the sum of the dimension roots of the input volumes. We work with Lebesgue-measurable
sets and do not require their sum to be measurable. Nonemptiness is retained even when
an input has zero volume.

First, indicator functions in the Prékopa–Leindler inequality give the multiplicative
volume inequality. Measurable subsets of the inputs and a measurable hull of the sum
allow this argument without assuming that a Minkowski sum is measurable. Rescaling
positive finite-volume inputs to equal volumes then gives the additive inequality.

## References

* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002),
  355–405, for the deduction from Prékopa–Leindler by indicators and rescaling.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The multiplicative Brunn–Minkowski inequality, with outer volume on the right.
The weight is strictly between zero and one; input volumes may be zero or infinite. -/
theorem volume_rpow_mul_volume_rpow_le {A B : Set E}
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    volume A ^ (1 - θ) * volume B ^ θ ≤ volume ((1 - θ) • A + θ • B) := by
  obtain ⟨K, hKA, hK, hKv⟩ := hA.exists_measurable_subset_ae_eq
  obtain ⟨L, hLB, hL, hLv⟩ := hB.exists_measurable_subset_ae_eq
  let S := toMeasurable volume ((1 - θ) • A + θ • B)
  have hS : MeasurableSet S := measurableSet_toMeasurable _ _
  have hPL := hasPrekopaLeindler_volume E hθ₀.le hθ₁.le
  rw [Measure.hasPrekopaLeindler_def] at hPL
  have key := hPL (f := K.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    (g := L.indicator (fun _ ↦ (1 : ℝ≥0∞))) (h := S.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    (measurable_const.indicator hK) (measurable_const.indicator hL)
    (measurable_const.indicator hS)
    (fun x y ↦ by
      by_cases hx : x ∈ K
      · by_cases hy : y ∈ L
        · have hz : (1 - θ) • x + θ • y ∈ S :=
            subset_toMeasurable volume _ (add_mem_add (smul_mem_smul_set (hKA hx))
              (smul_mem_smul_set (hLB hy)))
          simp [hx, hy, hz]
        · simp [hy, ENNReal.zero_rpow_of_pos hθ₀]
      · simp [hx, ENNReal.zero_rpow_of_pos (sub_pos.2 hθ₁)])
  simpa only [lintegral_indicator_const hK, lintegral_indicator_const hL,
    lintegral_indicator_const hS, one_mul, measure_congr hKv, measure_congr hLv,
    S, measure_toMeasurable, ENNReal.rpow_eq_pow] using key

/-- Dimension-root volume scales linearly under every real dilation, including zero.
This identity holds for arbitrary sets and infinite outer volumes. -/
theorem volume_smul_rpow {A : Set E} (hn : Module.finrank ℝ E ≠ 0) (c : ℝ) :
    volume (c • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      ENNReal.ofReal |c| * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  rw [Measure.addHaar_smul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    abs_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (abs_nonneg c) hn]

/-- The additive lower bound in terms of positive dimension roots of the input volumes. -/
private theorem volume_pow_add_root_le {A B : Set E}
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hAv : volume A = ENNReal.ofReal (a ^ Module.finrank ℝ E))
    (hBv : volume B = ENNReal.ofReal (b ^ Module.finrank ℝ E)) :
    ENNReal.ofReal ((a + b) ^ Module.finrank ℝ E) ≤ volume (A + B) := by
  -- Both rescaled volumes are `(a + b) ^ dim`, and their weighted sum is `A + B`.
  let θ := b / (a + b)
  have hθ₀ : 0 < θ := div_pos hb (add_pos ha hb)
  have hθ₁ : θ < 1 := (div_lt_one (add_pos ha hb)).2 (lt_add_of_pos_left _ ha)
  have hscale {S : Set E} {r : ℝ} (hr : 0 < r)
      (hSv : volume S = ENNReal.ofReal (r ^ Module.finrank ℝ E)) :
      volume (((a + b) / r) • S) =
        ENNReal.ofReal ((a + b) ^ Module.finrank ℝ E) := by
    rw [Measure.addHaar_smul_of_nonneg volume (by positivity), hSv,
      ← ENNReal.ofReal_mul (by positivity), div_pow,
      div_mul_cancel₀ _ (pow_ne_zero _ hr.ne')]
  have hleft : (1 - θ) * ((a + b) / a) = 1 := by
    dsimp [θ]
    field_simp
    ring
  have hright : θ * ((a + b) / b) = 1 := by
    dsimp [θ]
    field_simp
  have key := volume_rpow_mul_volume_rpow_le
    (Measure.NullMeasurableSet.const_smul hA ((a + b) / a))
    (Measure.NullMeasurableSet.const_smul hB ((a + b) / b)) hθ₀ hθ₁
  rw [hscale ha hAv, hscale hb hBv,
    ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hθ₁.le) hθ₀.le,
    sub_add_cancel, ENNReal.rpow_one, smul_smul, smul_smul,
    hleft, hright, one_smul, one_smul] at key
  exact key

/-- **Brunn–Minkowski inequality** for nonempty Lebesgue-measurable sets
in a positive-dimensional real inner product space. The sum has its outer volume and
need not be measurable or have finite volume. -/
theorem volume_rpow_add_volume_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume) :
    volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      volume B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume (A + B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  have hp : 0 < (Module.finrank ℝ E : ℝ)⁻¹ := by positivity
  have hAle : volume A ≤ volume (A + B) := by
    obtain ⟨b, hb⟩ := hBn
    calc
      volume A = volume (A + {b}) := by simp
      _ ≤ volume (A + B) := measure_mono (add_subset_add Subset.rfl (by simpa using hb))
  have hBle : volume B ≤ volume (A + B) := by
    obtain ⟨a, ha⟩ := hAn
    calc
      volume B = volume ({a} + B) := by simp
      _ ≤ volume (A + B) := measure_mono (add_subset_add (by simpa using ha) Subset.rfl)
  by_cases hAfin : volume A = ∞
  · have hsum : volume (A + B) = ∞ := top_unique (hAfin ▸ hAle)
    simp [hAfin, hsum, ENNReal.top_rpow_of_pos hp]
  by_cases hBfin : volume B = ∞
  · have hsum : volume (A + B) = ∞ := top_unique (hBfin ▸ hBle)
    simp [hBfin, hsum, ENNReal.top_rpow_of_pos hp]
  by_cases hAz : volume A = 0
  · simpa only [hAz, ENNReal.zero_rpow_of_pos hp, zero_add] using
      ENNReal.rpow_le_rpow hBle hp.le
  by_cases hBz : volume B = 0
  · simpa only [hBz, ENNReal.zero_rpow_of_pos hp, add_zero] using
      ENNReal.rpow_le_rpow hAle hp.le
  let a := (volume A).toReal ^ ((Module.finrank ℝ E : ℝ)⁻¹)
  let b := (volume B).toReal ^ ((Module.finrank ℝ E : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos (ENNReal.toReal_pos hAz hAfin) _
  have hb : 0 < b := Real.rpow_pos_of_pos (ENNReal.toReal_pos hBz hBfin) _
  have hAv : volume A = ENNReal.ofReal (a ^ Module.finrank ℝ E) := by
    rw [Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn, ENNReal.ofReal_toReal hAfin]
  have hBv : volume B = ENNReal.ofReal (b ^ Module.finrank ℝ E) := by
    rw [Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg hn, ENNReal.ofReal_toReal hBfin]
  have key := ENNReal.rpow_le_rpow (volume_pow_add_root_le hA hB ha hb hAv hBv) hp.le
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
    Real.pow_rpow_inv_natCast (by positivity) hn, ENNReal.ofReal_add ha.le hb.le] at key
  simpa only [a, b, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
    ENNReal.ofReal_toReal hAfin, ENNReal.ofReal_toReal hBfin] using key

/-- Weighted **Brunn–Minkowski inequality** with arbitrary nonnegative coefficients.
It includes the convex-combination weights `1 - θ, θ` for every `θ ∈ [0,1]`.
Zero coefficients and infinite input volumes use extended multiplication `0 * ∞ = 0`. -/
theorem mul_volume_rpow_add_mul_volume_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal c * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      ENNReal.ofReal d * volume B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  simpa only [volume_smul_rpow hn, abs_of_nonneg hc, abs_of_nonneg hd] using
    volume_rpow_add_volume_rpow_le hn hAn.smul_set
      (Measure.NullMeasurableSet.const_smul hA c) hBn.smul_set
      (Measure.NullMeasurableSet.const_smul hB d)

/-- Real-valued **Brunn–Minkowski inequality**. The sum's outer volume must be finite;
this implies finiteness of both input volumes. -/
theorem volume_real_rpow_add_volume_real_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume) (hfin : volume (A + B) ≠ ∞) :
    volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume.real (A + B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  have h := volume_rpow_add_volume_rpow_le hn hAn hA hBn hB
  have hsum := ENNReal.rpow_ne_top_of_nonneg (by positivity :
    0 ≤ (Module.finrank ℝ E : ℝ)⁻¹) hfin
  have hAfin := ne_top_of_le_ne_top hsum (le_self_add.trans h)
  have hBfin := ne_top_of_le_ne_top hsum (le_add_self.trans h)
  simpa only [ENNReal.toReal_add hAfin hBfin, ← ENNReal.toReal_rpow, measureReal_def] using
    ENNReal.toReal_mono hsum h

/-- Real-valued weighted **Brunn–Minkowski inequality**. Only the weighted sum is
required to have finite outer volume: an input with zero coefficient may have infinite volume. -/
theorem mul_volume_real_rpow_add_mul_volume_real_rpow_le {A B : Set E}
    (hn : Module.finrank ℝ E ≠ 0) (hAn : A.Nonempty) (hA : NullMeasurableSet A volume)
    (hBn : B.Nonempty) (hB : NullMeasurableSet B volume)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hfin : volume (c • A + d • B) ≠ ∞) :
    c * volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) +
      d * volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹) ≤
        volume.real (c • A + d • B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  have h := mul_volume_rpow_add_mul_volume_rpow_le hn hAn hA hBn hB hc hd
  have hsum := ENNReal.rpow_ne_top_of_nonneg (by positivity :
    0 ≤ (Module.finrank ℝ E : ℝ)⁻¹) hfin
  have hAfin := ne_top_of_le_ne_top hsum (le_self_add.trans h)
  have hBfin := ne_top_of_le_ne_top hsum (le_add_self.trans h)
  simpa only [ENNReal.toReal_add hAfin hBfin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hd, ← ENNReal.toReal_rpow,
    measureReal_def] using ENNReal.toReal_mono hsum h

end TauCeti
