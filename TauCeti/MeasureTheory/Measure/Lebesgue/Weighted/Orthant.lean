/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.Gamma.PDF
import TauCeti.Probability.Distributions.Gamma.Pi

/-!
# Lebesgue measure on the positive orthant pushed forward by a positive linear form

Let `ι` be a nonempty finite type with `n` elements and let `a : ι → ℝ` be positive weights. The
linear form `x ↦ ∑ i, a i * x i` sends Lebesgue measure on the closed positive orthant
`[0, ∞)^ι` to the measure on `[0, ∞)` with density

`s ↦ s^(n-1) / ((n-1)! ∏ i, a i)`

(`TauCeti.map_volume_restrict_pi_Ici_sum_mul`). Equivalently, the region
`{x ∈ [0, ∞)^ι | ∑ i, a i * x i ≤ c}` has volume `c^n / (n! ∏ i, a i)` for `c ≥ 0`
(`TauCeti.volume_setOf_forall_nonneg_and_sum_mul_le`). For unit weights the density is
`s^(n-1) / (n-1)!` and the region is the simplex of size `c`, of volume `c^n / n!`.

The proof tilts Lebesgue measure on the orthant by `exp (-∑ i, x i)`. The tilted measure is the
product of `n` exponential distributions, that is of Gamma distributions of shape one, so its sum
has the Gamma law of shape `n` (`TauCeti.Probability.map_sum_pi_gammaMeasure`). Since the tilt
only depends on the sum, it can be removed after pushing forward, which turns the Gamma density
`s^(n-1) e^(-s) / (n-1)!` into `s^(n-1) / (n-1)!`. Positive weights are reduced to unit weights
by the diagonal linear change of variables `x ↦ (a i * x i)_i`, of determinant `∏ i, a i`.

When the weights are those of a circle acting linearly on `ℂ^ι`, composing with the pushforward of
`TauCeti.map_volume_pi_half_sq_add_sq` computes the Duistermaat–Heckman measure of that action.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17 (sums of exponential variables).
-/

public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The tilt `exp (-s)` of Lebesgue measure on `[0, ∞)` is the exponential distribution, the
Gamma distribution of shape and rate one. -/
private theorem gammaPDF_one_one (s : ℝ) :
    gammaPDF 1 1 s = (Ici (0 : ℝ)).indicator (fun s ↦ ENNReal.ofReal (Real.exp (-s))) s := by
  by_cases hs : 0 ≤ s
  · simp [gammaPDF_of_nonneg hs, indicator_of_mem (mem_Ici.mpr hs)]
  · rw [gammaPDF_of_neg (not_le.mp hs), indicator_of_notMem (show s ∉ Ici 0 by simpa using hs)]

/-- The product of `n` exponential distributions is Lebesgue measure on the closed positive orthant
tilted by `exp (-∑ i, x i)`. -/
private theorem pi_gammaMeasure_one_one :
    (Measure.pi fun _ : ι ↦ gammaMeasure 1 1) =
      (volume.restrict (univ.pi fun _ : ι ↦ Ici (0 : ℝ))).withDensity
        ((fun s ↦ ENNReal.ofReal (Real.exp (-s))) ∘ fun x ↦ ∑ i, x i) := by
  have hS : MeasurableSet (univ.pi fun _ : ι ↦ Ici (0 : ℝ)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici
  rw [Probability.pi_gammaMeasure_eq_withDensity, ← withDensity_indicator hS]
  congr 1
  funext x
  simp_rw [gammaPDF_one_one]
  by_cases hx : x ∈ univ.pi fun _ : ι ↦ Ici (0 : ℝ)
  · have hx' : ∀ i, 0 ≤ x i := fun i ↦ hx i (mem_univ i)
    rw [indicator_of_mem hx, Function.comp_apply, Finset.prod_congr rfl fun i _ ↦
      indicator_of_mem (mem_Ici.mpr (hx' i)) _, ← ENNReal.ofReal_prod_of_nonneg
      fun i _ ↦ (Real.exp_pos _).le, ← Real.exp_sum, Finset.sum_neg_distrib]
  · obtain ⟨i, hi⟩ : ∃ i, x i < 0 := by
      simpa only [mem_univ_pi, mem_Ici, not_forall, not_le] using hx
    rw [indicator_of_notMem hx]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (indicator_of_notMem (by simpa using hi) _)

/-- The Gamma density of shape `n + 1` and rate one, with its tilt `exp (-s)` removed, is the
density `s^n / n!` on `[0, ∞)`. -/
private theorem gammaPDF_mul_ofReal_exp (n : ℕ) (s : ℝ) :
    gammaPDF (n + 1) 1 s * ENNReal.ofReal (Real.exp s) =
      (Ici (0 : ℝ)).indicator (fun s ↦ ENNReal.ofReal (s ^ n / n.factorial)) s := by
  by_cases hs : 0 ≤ s
  · rw [gammaPDF_of_nonneg hs, indicator_of_mem (mem_Ici.mpr hs), ← ENNReal.ofReal_mul
      (by positivity), Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast,
      Real.one_rpow, one_mul]
    congr 1
    rw [Real.exp_neg]
    field_simp
  · rw [gammaPDF_of_neg (not_le.mp hs), zero_mul,
      indicator_of_notMem (show s ∉ Ici 0 by simpa using hs)]

/-- **The simplex law.** The sum of the coordinates sends Lebesgue measure on the closed positive
orthant `[0, ∞)^ι`, for a nonempty finite type `ι` with `n` elements, to the measure on `[0, ∞)`
with density `s^(n-1) / (n-1)!`. -/
theorem map_volume_restrict_pi_Ici_sum [Nonempty ι] :
    (volume.restrict (univ.pi fun _ : ι ↦ Ici (0 : ℝ))).map (fun x ↦ ∑ i, x i) =
      (volume.restrict (Ici 0)).withDensity
        fun s ↦ ENNReal.ofReal (s ^ (Fintype.card ι - 1) / (Fintype.card ι - 1).factorial) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  rw [hm, add_tsub_cancel_right]
  set ν := (volume.restrict (univ.pi fun _ : ι ↦ Ici (0 : ℝ))).map (fun x ↦ ∑ i, x i)
  have hsum : Measurable fun x : ι → ℝ ↦ ∑ i, x i := by fun_prop
  have hexp : Measurable fun s : ℝ ↦ ENNReal.ofReal (Real.exp (-s)) := by fun_prop
  have hexp' : Measurable fun s : ℝ ↦ ENNReal.ofReal (Real.exp s) := by fun_prop
  -- Tilting by `exp (-s)` turns `ν` into the Gamma law of shape `m + 1`.
  have htilt : ν.withDensity (fun s ↦ ENNReal.ofReal (Real.exp (-s))) = gammaMeasure (m + 1) 1 := by
    rw [← Measure.map_withDensity_comp hsum hexp, ← pi_gammaMeasure_one_one,
      Probability.map_sum_pi_gammaMeasure (fun _ ↦ one_pos) one_pos]
    simp [hm]
  -- Untilting by `exp s` recovers `ν`.
  have huntilt : ν = (ν.withDensity fun s ↦ ENNReal.ofReal (Real.exp (-s))).withDensity
      fun s ↦ ENNReal.ofReal (Real.exp s) := by
    rw [← withDensity_mul ν hexp hexp']
    conv_lhs => rw [← withDensity_one (μ := ν)]
    congr 1
    funext s
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one, Pi.one_apply]
  rw [huntilt, htilt, gammaMeasure, ← withDensity_mul _ (Probability.measurable_gammaPDF _ _) hexp',
    ← withDensity_indicator measurableSet_Ici]
  congr 1
  funext s
  rw [Pi.mul_apply, gammaPDF_mul_ofReal_exp]

/-- The diagonal linear map `x ↦ (a i * x i)_i` with positive entries rescales Lebesgue measure on
the closed positive orthant by `(∏ i, a i)⁻¹`. -/
private theorem map_volume_restrict_pi_Ici_mul {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (volume.restrict (univ.pi fun _ : ι ↦ Ici (0 : ℝ))).map (fun x i ↦ a i * x i) =
      ENNReal.ofReal (∏ i, a i)⁻¹ • volume.restrict (univ.pi fun _ : ι ↦ Ici (0 : ℝ)) := by
  classical
  let D : (ι → ℝ) →ₗ[ℝ] ι → ℝ := Matrix.toLin' (Matrix.diagonal a)
  have hD : ⇑D = fun x i ↦ a i * x i := by
    funext x i
    simp [D, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det D = ∏ i, a i := by
    simp [D, LinearMap.det_toLin', Matrix.det_diagonal]
  have hpos : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  have hS : MeasurableSet (univ.pi fun _ : ι ↦ Ici (0 : ℝ)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici
  have hpre : (fun x i ↦ a i * x i) ⁻¹' (univ.pi fun _ : ι ↦ Ici (0 : ℝ)) =
      univ.pi fun _ : ι ↦ Ici (0 : ℝ) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, mem_Ici]
    exact forall_congr' fun i ↦ mul_nonneg_iff_of_pos_left (ha i)
  have hmeas : Measurable fun (x : ι → ℝ) (i : ι) ↦ a i * x i := by
    rw [← hD]
    exact D.continuous_of_finiteDimensional.measurable
  -- The diagonal map preserves the orthant, so it commutes with the restriction to it.
  rw [← hpre, ← Measure.restrict_map hmeas hS, hpre, ← hD,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [hdet]; exact hpos.ne'), hdet,
    abs_of_pos (inv_pos.mpr hpos), Measure.restrict_smul]

/-- **The weighted simplex law.** For positive weights `a`, the linear form `x ↦ ∑ i, a i * x i`
sends Lebesgue measure on the closed positive orthant `[0, ∞)^ι`, for a nonempty finite type `ι`
with `n` elements, to the measure on `[0, ∞)` with density `s^(n-1) / ((n-1)! ∏ i, a i)`. -/
theorem map_volume_restrict_pi_Ici_sum_mul [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (volume.restrict (univ.pi fun _ : ι ↦ Ici (0 : ℝ))).map (fun x ↦ ∑ i, a i * x i) =
      (volume.restrict (Ici 0)).withDensity fun s ↦ ENNReal.ofReal
        (s ^ (Fintype.card ι - 1) / ((Fintype.card ι - 1).factorial * ∏ i, a i)) := by
  have hpos : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  have hmeas : Measurable fun (x : ι → ℝ) (i : ι) ↦ a i * x i := by fun_prop
  have hcomp : (fun x : ι → ℝ ↦ ∑ i, a i * x i) =
      (fun y : ι → ℝ ↦ ∑ i, y i) ∘ fun x i ↦ a i * x i := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) hmeas, map_volume_restrict_pi_Ici_mul ha,
    Measure.map_smul, map_volume_restrict_pi_Ici_sum, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  · congr 1
    funext s
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (inv_pos.mpr hpos).le]
    congr 1
    field_simp
  · fun_prop

/-- **The volume of a weighted simplex.** For positive weights `a` and `c ≥ 0`, the region
`{x ∈ [0, ∞)^ι | ∑ i, a i * x i ≤ c}` has volume `c^n / (n! ∏ i, a i)`, where `n` is the number of
elements of `ι`. -/
theorem volume_setOf_forall_nonneg_and_sum_mul_le {a : ι → ℝ} (ha : ∀ i, 0 < a i) {c : ℝ}
    (hc : 0 ≤ c) :
    volume {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i ≤ c} =
      ENNReal.ofReal (c ^ Fintype.card ι / ((Fintype.card ι).factorial * ∏ i, a i)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [volume_pi, hc]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  have hsum : Measurable fun x : ι → ℝ ↦ ∑ i, a i * x i := by fun_prop
  have hset : {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i ≤ c} =
      (fun x ↦ ∑ i, a i * x i) ⁻¹' Iic c ∩ univ.pi fun _ : ι ↦ Ici (0 : ℝ) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic, mem_univ_pi, mem_Ici]
    exact and_comm
  have hdens : Continuous fun s : ℝ ↦
      s ^ (Fintype.card ι - 1) / ((Fintype.card ι - 1).factorial * ∏ i, a i) := by fun_prop
  -- The region is the preimage of `Iic c` under the pushforward, whose density is integrated
  -- over `[0, c]` as an interval integral of a power.
  rw [hset, ← Measure.restrict_apply (hsum measurableSet_Iic), ← Measure.map_apply hsum
    measurableSet_Iic, map_volume_restrict_pi_Ici_sum_mul ha, withDensity_apply _
    measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (hdens.integrableOn_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc fun s hs ↦ by
        have : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
        exact div_nonneg (pow_nonneg hs.1 _) (by positivity)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc,
    intervalIntegral.integral_div, integral_pow, hm, add_tsub_cancel_right, Nat.factorial_succ]
  congr 1
  push_cast
  have : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  field_simp
  ring

end TauCeti
