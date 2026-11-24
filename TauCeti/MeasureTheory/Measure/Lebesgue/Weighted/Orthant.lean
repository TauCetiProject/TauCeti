/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.HalfSqRadius
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.Gamma.PDF
import TauCeti.Probability.Distributions.Sums

/-!
# Lebesgue measure on the positive orthant pushed forward by a positive linear form

Let `ι` be a nonempty finite type with `n` elements and let `a : ι → ℝ` be positive weights. The
linear form `x ↦ ∑ i, a i * x i` sends Lebesgue measure on the closed positive orthant
`[0, ∞)^ι` to the measure on `[0, ∞)` with density

`s ↦ s^(n-1) / ((n-1)! ∏ i, a i)`

(`TauCeti.map_volume_restrict_pi_Ici_sum_mul`). Equivalently, the region
`{x ∈ [0, ∞)^ι | ∑ i, a i * x i ≤ c}` has volume `c^n / (n! ∏ i, a i)` for `c ≥ 0`
(`TauCeti.volume_setOf_forall_nonneg_and_sum_mul_le`), and so does the region cut out by the
strict inequality `∑ i, a i * x i < c` for `c > 0`
(`TauCeti.volume_setOf_forall_nonneg_and_sum_mul_lt`). For unit weights the density is
`s^(n-1) / (n-1)!` and the region is the simplex of size `c`, of volume `c^n / n!`.

The proof tilts Lebesgue measure on the orthant by `exp (-∑ i, x i)`. The tilted measure is the
product of `n` exponential distributions, so its sum has the Gamma law of shape `n`
(`TauCeti.Probability.map_sum_pi_expMeasure`). Since the tilt
only depends on the sum, it can be removed after pushing forward, which turns the Gamma density
`s^(n-1) e^(-s) / (n-1)!` into `s^(n-1) / (n-1)!`. Positive weights are reduced to unit weights
by the diagonal linear change of variables `x ↦ (a i * x i)_i`, of determinant `∏ i, a i`.

Composing with the pushforward `TauCeti.map_volume_euclideanSpace_half_sq_add_sq` of Lebesgue
measure by `(q, p) ↦ ((q_i² + p_i²) / 2)_i`, the map `(q, p) ↦ ∑ i, a i * (q_i² + p_i²) / 2` on
`EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` sends Lebesgue measure to `(2π)^n` times the measure
above (`TauCeti.map_volume_sum_mul_half_sq_add_sq`), and the ellipsoid
`{∑ i, a i * (q_i² + p_i²) / 2 ≤ c}` has volume `(2π c)^n / (n! ∏ i, a i)`
(`TauCeti.volume_setOf_sum_mul_half_sq_add_sq_le`). Read on `ℂ^ι`, this map is the moment map of
the circle acting by `z_i ↦ exp(-i a_i θ) z_i`, so this computes the Duistermaat–Heckman measure of
that action.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17 (sums of exponential variables).
-/

public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal Real

namespace TauCeti

variable {ι : Type*} [Fintype ι]

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
    rw [← Measure.map_withDensity_comp hsum.aemeasurable hexp.aemeasurable,
      ← Probability.pi_expMeasure_one_eq_withDensity,
      Probability.map_sum_pi_expMeasure one_pos, hm, Nat.cast_succ]
  -- Untilting by `exp s`, the inverse of `exp (-s)`, recovers `ν`.
  have hinv : (fun s ↦ (ENNReal.ofReal (Real.exp (-s)))⁻¹) =
      fun s ↦ ENNReal.ofReal (Real.exp s) := by
    funext s
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg, inv_inv]
  have huntilt : ν = (ν.withDensity fun s ↦ ENNReal.ofReal (Real.exp (-s))).withDensity
      fun s ↦ ENNReal.ofReal (Real.exp s) := by
    rw [← hinv]
    exact (withDensity_inv_same hexp
      (ae_of_all _ fun _ ↦ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top)).symm
  rw [huntilt, htilt, gammaMeasure, ← withDensity_mul _ (Probability.measurable_gammaPDF _ _) hexp',
    ← withDensity_indicator measurableSet_Ici]
  congr 1
  funext s
  rw [Pi.mul_apply, Probability.gammaPDF_mul_ofReal_exp]

/-- The diagonal linear map `x ↦ (a i * x i)_i` with positive entries rescales Lebesgue measure on
the closed positive orthant by `(∏ i, a i)⁻¹`. -/
theorem map_volume_restrict_pi_Ici_mul {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
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
  have hpos : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  have hsum : Measurable fun x : ι → ℝ ↦ ∑ i, a i * x i := by fun_prop
  have hset : {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i ≤ c} =
      (fun x ↦ ∑ i, a i * x i) ⁻¹' Iic c ∩ univ.pi fun _ : ι ↦ Ici (0 : ℝ) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic, mem_univ_pi, mem_Ici]
    exact and_comm
  set f : ℝ → ℝ := fun s ↦ s ^ (Fintype.card ι - 1) / ((Fintype.card ι - 1).factorial * ∏ i, a i)
  have hf : Continuous f := by fun_prop
  have hf_nonneg : ∀ s ∈ Icc 0 c, 0 ≤ f s := fun s hs ↦
    div_nonneg (pow_nonneg hs.1 _) (by positivity)
  -- The region is the preimage of `Iic c` under the pushforward, so its volume is the integral
  -- of the pushforward density over `[0, c]`.
  have hpush : volume {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i ≤ c} =
      ∫⁻ s in Icc 0 c, ENNReal.ofReal (f s) := by
    rw [hset, ← Measure.restrict_apply (hsum measurableSet_Iic), ← Measure.map_apply hsum
      measurableSet_Iic, map_volume_restrict_pi_Ici_sum_mul ha, withDensity_apply _
      measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici]
  -- The density is a multiple of a power, integrated as an interval integral.
  rw [hpush, ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn_Icc
      (ae_restrict_of_forall_mem measurableSet_Icc hf_nonneg),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc,
    intervalIntegral.integral_div, integral_pow, hm, add_tsub_cancel_right, Nat.factorial_succ]
  congr 1
  push_cast
  field_simp
  ring

/-- **The volume of a weighted simplex without its slanted face.** For positive weights `a` and
`c > 0`, the region `{x ∈ [0, ∞)^ι | ∑ i, a i * x i < c}` has the volume `c^n / (n! ∏ i, a i)` of
the closed region, where `n` is the number of elements of `ι`: the face `∑ i, a i * x i = c` is a
null set. -/
theorem volume_setOf_forall_nonneg_and_sum_mul_lt {a : ι → ℝ} (ha : ∀ i, 0 < a i) {c : ℝ}
    (hc : 0 < c) :
    volume {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i < c} =
      ENNReal.ofReal (c ^ Fintype.card ι / ((Fintype.card ι).factorial * ∏ i, a i)) := by
  rw [← volume_setOf_forall_nonneg_and_sum_mul_le ha hc.le]
  rcases isEmpty_or_nonempty ι with hι | hι
  · congr 1
    ext x
    simp [hc, hc.le]
  have hsum : Measurable fun x : ι → ℝ ↦ ∑ i, a i * x i := by fun_prop
  -- The face `∑ i, a i * x i = c` of the orthant is null: the weighted sum pushes the volume of
  -- the orthant to a measure with a density, which has no atoms.
  have hnull : volume {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i = c} = 0 := by
    have hset : {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i = c} =
        (fun x ↦ ∑ i, a i * x i) ⁻¹' {c} ∩ univ.pi fun _ : ι ↦ Ici (0 : ℝ) := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_univ_pi,
        mem_Ici]
      exact and_comm
    rw [hset, ← Measure.restrict_apply (hsum (measurableSet_singleton c)),
      ← Measure.map_apply hsum (measurableSet_singleton c), map_volume_restrict_pi_Ici_sum_mul ha]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (measurableSet_singleton c)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  have hsub : {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i ≤ c} ⊆
      {x | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i < c} ∪
        {x | (∀ i, 0 ≤ x i) ∧ ∑ i, a i * x i = c} := fun x hx ↦
    hx.2.lt_or_eq.imp (fun h ↦ ⟨hx.1, h⟩) fun h ↦ ⟨hx.1, h⟩
  refine le_antisymm (measure_mono fun x hx ↦ ⟨hx.1, hx.2.le⟩) ?_
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]

/-- **The Duistermaat–Heckman measure of a circle acting with positive weights.** Let the circle
act on `ℂ^ι` by `z_i ↦ exp(-i a_i θ) z_i` with weights `a_i > 0`, with moment map
`H = ∑_i a_i (q_i² + p_i²) / 2`. Then `H` pushes Lebesgue measure on `ℂ^ι`, for `ι` with `n ≥ 1`
elements, to `(2π)^n` times the measure on `[0, ∞)` with the polynomial density
`s^(n-1) / ((n-1)! ∏ i, a i)`. -/
theorem map_volume_sum_mul_half_sq_add_sq [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)).map
        (fun x ↦ ∑ i, a i * ((x.1 i ^ 2 + x.2 i ^ 2) / 2)) =
      ENNReal.ofReal (2 * π) ^ Fintype.card ι •
        (volume.restrict (Ici 0)).withDensity fun s ↦ ENNReal.ofReal
          (s ^ (Fintype.card ι - 1) / ((Fintype.card ι - 1).factorial * ∏ i, a i)) := by
  have hcomp : (fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      ∑ i, a i * ((x.1 i ^ 2 + x.2 i ^ 2) / 2)) =
      (fun y : ι → ℝ ↦ ∑ i, a i * y i) ∘ fun x i ↦ (x.1 i ^ 2 + x.2 i ^ 2) / 2 :=
    (rfl)
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_volume_euclideanSpace_half_sq_add_sq, Measure.map_smul,
    map_volume_restrict_pi_Ici_sum_mul ha]
  exact (by fun_prop : Measurable fun y : ι → ℝ ↦ ∑ i, a i * y i).aemeasurable

/-- **The volume of a sublevel of the moment map of a circle acting with positive weights.** For
weights `a_i > 0` and `c ≥ 0`, the ellipsoid `{∑_i a_i (q_i² + p_i²) / 2 ≤ c}` in `ℂ^ι` has
Lebesgue measure `(2π c)^n / (n! ∏ i, a i)`, where `n` is the number of elements of `ι`. -/
theorem volume_setOf_sum_mul_half_sq_add_sq_le {a : ι → ℝ} (ha : ∀ i, 0 < a i) {c : ℝ}
    (hc : 0 ≤ c) :
    volume {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι |
        ∑ i, a i * ((x.1 i ^ 2 + x.2 i ^ 2) / 2) ≤ c} =
      ENNReal.ofReal ((2 * π * c) ^ Fintype.card ι /
        ((Fintype.card ι).factorial * ∏ i, a i)) := by
  have hh : Measurable fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      fun i ↦ (x.1 i ^ 2 + x.2 i ^ 2) / 2 := by fun_prop
  have hS : MeasurableSet {y : ι → ℝ | ∑ i, a i * y i ≤ c} :=
    measurableSet_le (by fun_prop) measurable_const
  have hset : {y : ι → ℝ | ∑ i, a i * y i ≤ c} ∩ univ.pi (fun _ ↦ Ici 0) =
      {y : ι → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, a i * y i ≤ c} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, mem_univ_pi, mem_Ici]
    exact and_comm
  have hpre : {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι |
      ∑ i, a i * ((x.1 i ^ 2 + x.2 i ^ 2) / 2) ≤ c} =
      (fun x i ↦ (x.1 i ^ 2 + x.2 i ^ 2) / 2) ⁻¹' {y : ι → ℝ | ∑ i, a i * y i ≤ c} :=
    (rfl)
  -- Pass to the orthant coordinates `y_i = (q_i² + p_i²) / 2` and use the weighted simplex.
  rw [hpre, ← Measure.map_apply hh hS, map_volume_euclideanSpace_half_sq_add_sq,
    smul_apply, Measure.restrict_apply hS, hset, volume_setOf_forall_nonneg_and_sum_mul_le ha hc,
    smul_eq_mul, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end TauCeti
