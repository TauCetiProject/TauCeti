/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Probability.Distributions.IrwinHall.Cdf
-- Proof-only: the Irwin–Hall mgf, the bound on `(1 - exp (-l)) / l`, and the cdf of the
-- order-zero Irwin–Hall law.
import TauCeti.Probability.Distributions.Dirac
import TauCeti.Probability.Distributions.IrwinHall.Transforms
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# The volume of a simplex cut from the unit cube

For `m : ℕ` and `t : ℝ`, `TauCeti.simplexVolume m t` is the Lebesgue volume `V_m(t)` of
`{x ∈ [0, 1] ^ m | ∑ j, x j ≤ t}`. It is the proportion of the monomials `X ^ i` of a box
`0 ≤ i j ≤ d j` whose weighted degree `∑ j, i j / d j` is at most `t`, up to an error that
vanishes as every `d j` grows. This is the count that enters the dimension estimates for
auxiliary polynomials with prescribed index in Roth's theorem and in the Subspace Theorem
(Bombieri–Gubler, *Heights in Diophantine Geometry*, 6.3.3 and Lemma 6.3.5).

Equivalently, `V_m(t)` is the cdf at `t` of the Irwin–Hall law of order `m`, the law of a sum of
`m` independent unit-uniform variables (`TauCeti.simplexVolume_eq_cdf_irwinHallMeasure`). The
normalization facts below are read off from the cdf API of that law.

The main estimate is the **tail bound** `TauCeti.simplexVolume_le_exp_neg`: for `0 ≤ ε`,
`V_m((1 / 2 - ε) m) ≤ exp (-6 m ε ^ 2)`, so the volume concentrates around the centre `m / 2` of
the cube (Bombieri–Gubler, Lemma 6.3.5, without the restriction `ε ≤ 1 / 2`). It comes from the
exponential-moment bound `TauCeti.simplexVolume_le_exp_mul_pow`,
`V_m(s) ≤ exp (l s) ((1 - exp (-l)) / l) ^ m` for `0 < l`, the Chernoff bound
`ProbabilityTheory.measure_le_le_exp_mul_mgf` for the Irwin–Hall law at `-l`, together with
`Real.one_sub_exp_neg_div_le_exp` at `l = 12 ε`.

## Main declarations

* `TauCeti.simplexVolume`: the volume `V_m(t)`.
* `TauCeti.simplexVolume_eq_cdf_irwinHallMeasure`: `V_m(t)` is the Irwin–Hall cdf of order `m`.
* `TauCeti.simplexVolume_eq_zero_of_neg`, `TauCeti.simplexVolume_eq_one_of_le`,
  `TauCeti.simplexVolume_pos`, `TauCeti.simplexVolume_one`: `V_m(t) = 0` for `t < 0`,
  `V_m(t) = 1` for `m ≤ t`, `0 < V_m(t)` for `0 < t`, and `V_1(t) = min 1 t` for `0 ≤ t`.
* `TauCeti.simplexVolume_mono`, `TauCeti.simplexVolume_nonneg`, `TauCeti.simplexVolume_le_one`.
* `TauCeti.simplexVolume_le_exp_mul_pow` and `TauCeti.simplexVolume_le_exp_neg`: the
  exponential-moment bound and the tail bound.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

/-- The volume `V_m(t)` of `{x ∈ [0, 1] ^ m | ∑ j, x j ≤ t}`, the part of the unit cube of
`ℝ ^ m` on or below the hyperplane `∑ j, x j = t`. -/
noncomputable def simplexVolume (m : ℕ) (t : ℝ) : ℝ :=
  volume.real (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t})

/-- Unfolds `TauCeti.simplexVolume` to the volume of its defining region. -/
theorem simplexVolume_def (m : ℕ) (t : ℝ) :
    simplexVolume m t = volume.real (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t}) := (rfl)

/-- `V_m(t)` is the cdf at `t` of the Irwin–Hall law of order `m`: that law is the image of the
uniform measure on the unit cube under `x ↦ ∑ j, x j`. -/
theorem simplexVolume_eq_cdf_irwinHallMeasure (m : ℕ) (t : ℝ) :
    simplexVolume m t = cdf (Probability.irwinHallMeasure m) t := by
  have hu : Probability.uniformMeasure 0 1 = volume.restrict (Icc 0 1) := by
    rw [Probability.uniformMeasure_eq_smul, sub_zero, ENNReal.ofReal_one, inv_one, one_smul]
    exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  have h := Probability.map_sum_pi_uniformMeasure_zero_one (ι := Fin m)
  rw [Fintype.card_fin, hu, ← Measure.restrict_pi_pi, pi_univ_Icc] at h
  rw [cdf_eq_real, ← h, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    measureReal_restrict_apply (measurableSet_Iic.preimage (by fun_prop)), inter_comm,
    simplexVolume_def]
  rfl

/-- `V_m(t)` is nonnegative. -/
theorem simplexVolume_nonneg (m : ℕ) (t : ℝ) : 0 ≤ simplexVolume m t := by
  rw [simplexVolume_eq_cdf_irwinHallMeasure]
  exact cdf_nonneg _ _

/-- `V_m(t) ≤ 1`: it is a value of a cdf. -/
theorem simplexVolume_le_one (m : ℕ) (t : ℝ) : simplexVolume m t ≤ 1 := by
  rw [simplexVolume_eq_cdf_irwinHallMeasure]
  exact cdf_le_one _ _

/-- `V_m(t)` is monotone in `t`. -/
theorem simplexVolume_mono (m : ℕ) : Monotone (simplexVolume m) := fun _ _ hst ↦ by
  simpa only [simplexVolume_eq_cdf_irwinHallMeasure] using (cdf _).mono hst

/-- `V_m(t) = 0` for `t < 0`. At `m = 0` the Irwin–Hall law is the point mass at `0`, so the
hypothesis cannot be weakened to `t ≤ 0`. -/
@[simp]
theorem simplexVolume_eq_zero_of_neg (m : ℕ) {t : ℝ} (ht : t < 0) : simplexVolume m t = 0 := by
  rw [simplexVolume_eq_cdf_irwinHallMeasure]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [ht.not_ge]
  · exact Probability.cdf_irwinHallMeasure_of_nonpos hm ht.le

/-- `V_m(t) = 1` for `m ≤ t`: the coordinates of a point of the cube sum to at most `m`. -/
@[simp]
theorem simplexVolume_eq_one_of_le {m : ℕ} {t : ℝ} (ht : m ≤ t) : simplexVolume m t = 1 := by
  rw [simplexVolume_eq_cdf_irwinHallMeasure]
  exact Probability.cdf_irwinHallMeasure_of_natCast_le m ht

/-- `0 < V_m(t)` for `0 < t`. -/
theorem simplexVolume_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < simplexVolume m t := by
  rw [simplexVolume_eq_cdf_irwinHallMeasure]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [ht.le]
  · exact (Probability.cdf_irwinHallMeasure_pos_iff hm).2 ht

/-- `V_1(t) = min 1 t` for `0 ≤ t`, which pins the normalization: the Irwin–Hall law of order
`1` is the uniform law on the unit interval. -/
@[simp]
theorem simplexVolume_one {t : ℝ} (ht : 0 ≤ t) : simplexVolume 1 t = min 1 t := by
  rw [simplexVolume_eq_cdf_irwinHallMeasure, Probability.irwinHallMeasure_one,
    Probability.cdf_uniformMeasure zero_lt_one]
  split_ifs with h0 h1
  · simp [le_antisymm h0 ht]
  · exact (min_eq_left h1).symm
  · rw [sub_zero, sub_zero, div_one, min_eq_right (not_le.1 h1).le]

/-- **The exponential-moment bound.** For `0 < l`,
`V_m(s) ≤ exp (l s) ((1 - exp (-l)) / l) ^ m`, where `(1 - exp (-l)) / l` is the integral of
`exp (-l x)` over `[0, 1]`, so that its `m`-th power is the Irwin–Hall mgf at `-l`. -/
theorem simplexVolume_le_exp_mul_pow (m : ℕ) {l : ℝ} (hl : 0 < l) (s : ℝ) :
    simplexVolume m s ≤ Real.exp (l * s) * ((1 - Real.exp (-l)) / l) ^ m := by
  -- The Chernoff bound for the Irwin–Hall law at `-l`, whose mgf is `((exp (-l) - 1) / -l) ^ m`.
  have h := measure_le_le_exp_mul_mgf (μ := Probability.irwinHallMeasure m) (X := id) s
    (neg_nonpos.2 hl.le) (integrable_of_mem_integrableExpSet (by simp))
  rw [Probability.mgf_id_irwinHallMeasure m (neg_ne_zero.2 hl.ne'), neg_neg, div_neg,
    ← neg_div, neg_sub] at h
  rw [simplexVolume_eq_cdf_irwinHallMeasure, cdf_eq_real]
  exact h

/-- **The tail bound.** For `0 ≤ ε`, `V_m((1 / 2 - ε) m) ≤ exp (-6 m ε ^ 2)`: the part of the
unit cube of `ℝ ^ m` where the coordinates sum to at most `(1 / 2 - ε) m` has volume at most
`exp (-6 m ε ^ 2)`. -/
theorem simplexVolume_le_exp_neg (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    simplexVolume m ((1 / 2 - ε) * m) ≤ Real.exp (-(6 * m * ε ^ 2)) := by
  rcases hε.eq_or_lt with rfl | hε
  · simpa using simplexVolume_le_one m _
  have hl : 0 < 12 * ε := by positivity
  calc simplexVolume m ((1 / 2 - ε) * m)
      ≤ Real.exp (12 * ε * ((1 / 2 - ε) * m)) * ((1 - Real.exp (-(12 * ε))) / (12 * ε)) ^ m :=
        simplexVolume_le_exp_mul_pow m hl _
    _ ≤ Real.exp (12 * ε * ((1 / 2 - ε) * m)) *
          Real.exp (-(12 * ε / 2) + (12 * ε) ^ 2 / 24) ^ m := by
        gcongr
        · exact div_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith))) hl.le
        · exact Real.one_sub_exp_neg_div_le_exp _
    _ = Real.exp (-(6 * m * ε ^ 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        ring_nf

end TauCeti
