/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- Proof-only: the exponential-moment bound, the bound on `sinh`, and `∫ exp` on an interval.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.MeasureTheory.Integral.Pi

/-!
# The volume of a simplex cut from the unit cube

For `m : ℕ` and `t : ℝ`, `TauCeti.simplexVolume m t` is the Lebesgue volume `V_m(t)` of
`{x ∈ [0, 1] ^ m | ∑ j, x j ≤ t}`. It is the proportion of the monomials `X ^ i` of a box
`0 ≤ i j ≤ d j` whose weighted degree `∑ j, i j / d j` is at most `t`, up to an error that
vanishes as every `d j` grows. This is the count that enters the dimension estimates for
auxiliary polynomials with prescribed index in Roth's theorem and in the Subspace Theorem
(Bombieri–Gubler, *Heights in Diophantine Geometry*, 6.3.3 and Lemma 6.3.5).

The main estimate is the **tail bound** `TauCeti.simplexVolume_le_exp_neg`: for `0 ≤ ε`,
`V_m((1 / 2 - ε) m) ≤ exp (-6 m ε ^ 2)`, so the volume concentrates around the centre `m / 2` of
the cube (Bombieri–Gubler, Lemma 6.3.5, without the restriction `ε ≤ 1 / 2`). It comes from the
exponential-moment bound `TauCeti.simplexVolume_le_exp_mul_pow`,
`V_m(s) ≤ exp (l s) ((1 - exp (-l)) / l) ^ m` for `0 < l`, an instance of
`TauCeti.setIntegral_prod_le_exp_mul_pow` at the indicator of `[0, 1]`, together with
`Real.sinh_le_mul_exp_sq_div_six` at `l = 12 ε`.

## Main declarations

* `TauCeti.simplexVolume`: the volume `V_m(t)`.
* `TauCeti.simplexVolume_eq_zero_of_neg`, `TauCeti.simplexVolume_eq_one_of_le`,
  `TauCeti.simplexVolume_pos`, `TauCeti.simplexVolume_one`: `V_m(t) = 0` for `t < 0`,
  `V_m(t) = 1` for `m ≤ t`, `0 < V_m(t)` for `0 < t`, and `V_1(t) = min 1 t` for `0 ≤ t`.
* `TauCeti.simplexVolume_mono`, `TauCeti.simplexVolume_nonneg`, `TauCeti.simplexVolume_le_one`.
* `TauCeti.simplexVolume_le_exp_mul_pow` and `TauCeti.simplexVolume_le_exp_neg`: the
  exponential-moment bound and the tail bound.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- The volume `V_m(t)` of `{x ∈ [0, 1] ^ m | ∑ j, x j ≤ t}`, the part of the unit cube of
`ℝ ^ m` on or below the hyperplane `∑ j, x j = t`. -/
noncomputable def simplexVolume (m : ℕ) (t : ℝ) : ℝ :=
  volume.real (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t})

/-- Unfolds `TauCeti.simplexVolume` to the volume of its defining region. -/
theorem simplexVolume_def (m : ℕ) (t : ℝ) :
    simplexVolume m t = volume.real (Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t}) := (rfl)

/-- The unit cube of `ℝ ^ m` has volume `1`. -/
private theorem measureReal_Icc_zero_one (m : ℕ) : volume.real (Icc (0 : Fin m → ℝ) 1) = 1 := by
  simp [measureReal_def, Real.volume_Icc_pi]

/-- `V_m(t)` is nonnegative. -/
theorem simplexVolume_nonneg (m : ℕ) (t : ℝ) : 0 ≤ simplexVolume m t :=
  measureReal_nonneg

/-- `V_m(t) ≤ 1`: the region lies in the unit cube. -/
theorem simplexVolume_le_one (m : ℕ) (t : ℝ) : simplexVolume m t ≤ 1 := by
  rw [simplexVolume_def, ← measureReal_Icc_zero_one m]
  exact measureReal_mono inter_subset_left isCompact_Icc.measure_ne_top

/-- `V_m(t)` is monotone in `t`. -/
theorem simplexVolume_mono (m : ℕ) : Monotone (simplexVolume m) := fun s _ hst ↦
  measureReal_mono (inter_subset_inter_right _ fun _ (hx : _ ≤ s) ↦ hx.trans hst)
    (measure_ne_top_of_subset inter_subset_left isCompact_Icc.measure_ne_top)

/-- `V_m(t) = 0` for `t < 0`: the coordinates of a point of the cube have a nonnegative sum. -/
theorem simplexVolume_eq_zero_of_neg (m : ℕ) {t : ℝ} (ht : t < 0) : simplexVolume m t = 0 := by
  have h : Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t} = ∅ :=
    eq_empty_of_forall_notMem fun x ⟨hx, (hxt : _ ≤ t)⟩ ↦
      (Finset.sum_nonneg fun j _ ↦ hx.1 j).not_gt (hxt.trans_lt ht)
  rw [simplexVolume_def, h, measureReal_empty]

/-- `V_m(t) = 1` for `m ≤ t`: the coordinates of a point of the cube sum to at most `m`. -/
theorem simplexVolume_eq_one_of_le {m : ℕ} {t : ℝ} (ht : m ≤ t) : simplexVolume m t = 1 := by
  rw [simplexVolume_def, inter_eq_left.2 fun x hx ↦ ?_, measureReal_Icc_zero_one]
  calc ∑ j, x j ≤ ∑ _j : Fin m, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ hx.2 j
    _ = m := by simp
    _ ≤ t := ht

/-- `0 < V_m(t)` for `0 < t`: the region contains the cube `[0, c] ^ m` with
`c = min 1 (t / (m + 1))`. -/
theorem simplexVolume_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < simplexVolume m t := by
  set c := min 1 (t / (m + 1))
  have hc : 0 < c := lt_min one_pos (by positivity)
  have hsub : Icc (0 : Fin m → ℝ) (fun _ ↦ c) ⊆ Icc (0 : Fin m → ℝ) 1 ∩ {x | ∑ j, x j ≤ t} :=
    fun x hx ↦ ⟨⟨hx.1, fun j ↦ (hx.2 j).trans (min_le_left _ _)⟩, by
      calc ∑ j, x j ≤ ∑ _j : Fin m, t / (m + 1) :=
            Finset.sum_le_sum fun j _ ↦ (hx.2 j).trans (min_le_right _ _)
        _ = m * t / (m + 1) := by simp [mul_div_assoc]
        _ ≤ t := by rw [div_le_iff₀ (by positivity)]; nlinarith⟩
  calc 0 < c ^ m := pow_pos hc m
    _ = volume.real (Icc (0 : Fin m → ℝ) (fun _ ↦ c)) := by
      simp [measureReal_def, Real.volume_Icc_pi, hc.le]
    _ ≤ simplexVolume m t :=
      measureReal_mono hsub (measure_ne_top_of_subset inter_subset_left
        isCompact_Icc.measure_ne_top)

/-- `V_1(t) = min 1 t` for `0 ≤ t`, which pins the normalization: in one variable the region
is the interval `[0, min 1 t]`. -/
theorem simplexVolume_one {t : ℝ} (ht : 0 ≤ t) : simplexVolume 1 t = min 1 t := by
  have hset : Icc (0 : Fin 1 → ℝ) 1 ∩ {x | ∑ j, x j ≤ t} =
      MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Icc 0 (min 1 t) := by
    ext x
    simp [Pi.le_def, Fin.forall_fin_one, and_assoc]
  rw [simplexVolume_def, hset]
  calc volume.real (MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Icc 0 (min 1 t))
      = volume.real (Icc 0 (min 1 t)) :=
        (volume_preserving_funUnique (Fin 1) ℝ).measureReal_preimage
          measurableSet_Icc.nullMeasurableSet
    _ = min 1 t := by rw [Real.volume_real_Icc_of_le (le_min zero_le_one ht), sub_zero]

/-- `exp (-(l * x))` times the indicator of `[0, 1]` is the indicator of `x ↦ exp (-(l * x))`. -/
private theorem exp_neg_mul_mul_indicator_Icc (l : ℝ) :
    (fun x ↦ Real.exp (-(l * x)) * (Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) x) =
      (Icc (0 : ℝ) 1).indicator fun x ↦ Real.exp (-(l * x)) := by
  ext x
  by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]

/-- `∫₀¹ exp (-(l * x)) dx = (1 - exp (-l)) / l` for `l ≠ 0`. -/
private theorem integral_exp_neg_mul_indicator {l : ℝ} (hl : l ≠ 0) :
    ∫ x, Real.exp (-(l * x)) * (Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) x =
      (1 - Real.exp (-l)) / l := by
  have hderiv : ∀ x, HasDerivAt (fun x ↦ -Real.exp (-(l * x)) / l) (Real.exp (-(l * x))) x :=
    fun x ↦ by
      have h : HasDerivAt (fun y ↦ -(l * y)) (-l) x := by
        simpa using (hasDerivAt_id' x).const_mul (-l)
      convert h.exp.neg.div_const l using 1
      field_simp
  rw [exp_neg_mul_mul_indicator_Icc, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      ((by fun_prop : Continuous fun x ↦ Real.exp (-(l * x))).intervalIntegrable _ _)]
  simp only [mul_one, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- **The exponential-moment bound.** For `0 < l`,
`V_m(s) ≤ exp (l s) ((1 - exp (-l)) / l) ^ m`, where `(1 - exp (-l)) / l` is the integral of
`exp (-l x)` over `[0, 1]`. -/
theorem simplexVolume_le_exp_mul_pow (m : ℕ) {l : ℝ} (hl : 0 < l) (s : ℝ) :
    simplexVolume m s ≤ Real.exp (l * s) * ((1 - Real.exp (-l)) / l) ^ m := by
  have hint :
      Integrable fun x ↦ Real.exp (-(l * x)) * (Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) x := by
    rw [exp_neg_mul_mul_indicator_Icc]
    exact (integrable_indicator_iff measurableSet_Icc).2
      (by fun_prop : Continuous fun x ↦ Real.exp (-(l * x))).integrableOn_Icc
  have h := setIntegral_prod_le_exp_mul_pow (ι := Fin m) (g := (Icc (0 : ℝ) 1).indicator 1)
    (fun x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x) hl.le hint s
  -- The product of the indicators of `[0, 1]` at the coordinates is the indicator of the cube.
  have hprod (x : Fin m → ℝ) : ∏ j, (Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (x j) =
      (Icc (0 : Fin m → ℝ) 1).indicator (1 : (Fin m → ℝ) → ℝ) x := by
    rw [← pi_univ_Icc, ← Finset.coe_univ, indicator_pi_one_apply]
    simp only [Pi.zero_apply, Pi.one_apply]
  simp_rw [hprod] at h
  rw [simplexVolume_def]
  rwa [integral_indicator_one measurableSet_Icc,
    measureReal_restrict_apply measurableSet_Icc, integral_exp_neg_mul_indicator hl.ne',
    Fintype.card_fin] at h

/-- `(1 - exp (-l)) / l ≤ exp (-(l / 2) + l ^ 2 / 24)` for `0 < l`: the left side is
`exp (-(l / 2)) * (sinh (l / 2) / (l / 2))`. -/
private theorem one_sub_exp_neg_div_le {l : ℝ} (hl : 0 < l) :
    (1 - Real.exp (-l)) / l ≤ Real.exp (-(l / 2) + l ^ 2 / 24) := by
  have h1 : 1 - Real.exp (-l) = Real.exp (-(l / 2)) * (2 * Real.sinh (l / 2)) := by
    rw [Real.sinh_eq, mul_div_cancel₀ _ two_ne_zero, mul_sub, ← Real.exp_add, ← Real.exp_add,
      show -(l / 2) + l / 2 = 0 by ring, show -(l / 2) + -(l / 2) = -l by ring, Real.exp_zero]
  have h2 := Real.sinh_le_mul_exp_sq_div_six (half_pos hl).le
  rw [h1, Real.exp_add, div_le_iff₀ hl, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc 2 * Real.sinh (l / 2) ≤ 2 * (l / 2 * Real.exp ((l / 2) ^ 2 / 6)) := by gcongr
    _ = Real.exp (l ^ 2 / 24) * l := by ring_nf

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
        · exact one_sub_exp_neg_div_le hl
    _ = Real.exp (-(6 * m * ε ^ 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        ring_nf

end TauCeti
