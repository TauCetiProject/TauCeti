/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Probability.Distributions.IrwinHall.Cdf
-- Proof-only: the Irwin–Hall mgf, the bound on `(1 - exp (-l)) / l`, the cdf of the
-- order-zero Irwin–Hall law, and the dilations of the coordinate simplex.
import TauCeti.Analysis.Convex.CoordinateSimplex
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
* `TauCeti.simplexVolume_eq_pow_div_factorial`: `V_m(t) = t ^ m / m!` for `0 ≤ t ≤ 1`.
* `TauCeti.volume_setOf_nonneg_sum_le`, `TauCeti.volume_setOf_nonneg_sum_lt`: the corner simplex
  `{x ∈ ℝ^κ | 0 ≤ x, ∑ k, x k ≤ a}` has volume `a ^ n / n!` for `n = #κ`, and so does its
  half-open version.
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

/-! ### The corner simplex -/

/-- `V_m(t) = t ^ m / m!` for `0 ≤ t ≤ 1`. On or below the hyperplane `∑ j, x j = 1`, the cube
imposes no constraint beyond nonnegativity, and only the first truncated power in the Irwin–Hall
cdf survives. -/
theorem simplexVolume_eq_pow_div_factorial (m : ℕ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    simplexVolume m t = t ^ m / m.factorial := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simpa using simplexVolume_eq_one_of_le (m := 0) (by simpa using ht₀)
  rw [simplexVolume_eq_cdf_irwinHallMeasure, Probability.cdf_irwinHallMeasure_eq hm,
    Finset.sum_range_succ', Finset.sum_eq_zero fun k _ ↦ ?_]
  · simp [max_eq_left ht₀]
  · rw [max_eq_right (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]),
      zero_pow hm.ne', mul_zero]

/-- **The volume of the corner simplex.** For `0 ≤ a`, the simplex
`{x ∈ ℝ^κ | 0 ≤ x k for every k, ∑ k, x k ≤ a}` has volume `a ^ n / n!`, where `n = #κ`. -/
theorem volume_setOf_nonneg_sum_le (κ : Type*) [Fintype κ] {a : ℝ} (ha : 0 ≤ a) :
    volume {x : κ → ℝ | (∀ k, 0 ≤ x k) ∧ ∑ k, x k ≤ a} =
      ENNReal.ofReal (a ^ Fintype.card κ / (Fintype.card κ).factorial) := by
  set m := Fintype.card κ
  -- The unit corner simplex of `ℝ ^ m` is the part of the unit cube below `∑ j, x j = 1`.
  have hfin : {x : Fin m → ℝ | (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ 1} =
      Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ 1} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    refine ⟨fun ⟨hx, hsum⟩ ↦ ⟨⟨hx, fun j ↦ ?_⟩, hsum⟩, fun ⟨⟨hx, _⟩, hsum⟩ ↦ ⟨hx, hsum⟩⟩
    exact (Finset.single_le_sum (fun k _ ↦ hx k) (Finset.mem_univ j)).trans hsum
  have hunit : volume {x : Fin m → ℝ | (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ 1} =
      ENNReal.ofReal (1 / m.factorial) := by
    have h1 := simplexVolume_eq_pow_div_factorial m zero_le_one le_rfl
    rw [one_pow, simplexVolume_def, ← hfin, measureReal_def] at h1
    rw [← h1, ENNReal.ofReal_toReal]
    exact measure_ne_top_of_subset (hfin ▸ inter_subset_left)
      (isCompact_Icc.measure_ne_top (μ := (volume : Measure (Fin m → ℝ))))
  -- Transport along a bijection `Fin m ≃ κ`, then dilate by `a`.
  have hκ : volume {x : κ → ℝ | (∀ k, 0 ≤ x k) ∧ ∑ k, x k ≤ 1} =
      ENNReal.ofReal (1 / m.factorial) := by
    let e : Fin m ≃ κ := (Fintype.equivFin κ).symm
    have hp := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
    have happ (x : Fin m → ℝ) (k : κ) :
        MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ) x k = x (e.symm k) := by
      simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]
    rw [← hp.measure_preimage_equiv, ← hunit]
    congr 1
    ext x
    simp only [mem_preimage, mem_ofPred_eq, happ]
    exact and_congr (e.symm.surjective.forall (p := fun j ↦ 0 ≤ x j)).symm
      (by rw [e.symm.sum_comp x])
  rw [← smul_coordinateSimplex κ ha, Measure.addHaar_smul_of_nonneg volume ha, coordinateSimplex,
    hκ,
    Module.finrank_fintype_fun_eq_card, ← ENNReal.ofReal_mul (pow_nonneg ha m), mul_one_div]

/-- **The volume of the half-open corner simplex.** For `0 < a`, the set
`{x ∈ ℝ^κ | 0 ≤ x k for every k, ∑ k, x k < a}` has volume `a ^ n / n!`, where `n = #κ`: it
contains the corner simplices of every size `t < a`. -/
theorem volume_setOf_nonneg_sum_lt (κ : Type*) [Fintype κ] {a : ℝ} (ha : 0 < a) :
    volume {x : κ → ℝ | (∀ k, 0 ≤ x k) ∧ ∑ k, x k < a} =
      ENNReal.ofReal (a ^ Fintype.card κ / (Fintype.card κ).factorial) := by
  refine le_antisymm ?_ ?_
  · rw [← volume_setOf_nonneg_sum_le κ ha.le]
    exact measure_mono fun x hx ↦ ⟨hx.1, hx.2.le⟩
  have hc : Continuous fun t : ℝ ↦
      ENNReal.ofReal (t ^ Fintype.card κ / (Fintype.card κ).factorial) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  refine le_of_tendsto (hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio a))) ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with t ht
  rw [← volume_setOf_nonneg_sum_le κ ht.1.le]
  exact measure_mono fun x hx ↦ ⟨hx.1, hx.2.trans_lt ht.2⟩

end TauCeti
