/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Integral lemmas for completely monotone functions

Taylor-remainder sign bounds and improper-integral facts about completely monotone functions.

These extend the object API in `CompletelyMonotone/Basic.lean` with the sign of the Taylor
integral remainder and improper-integral facts for the first derivative within `[0, ∞)`.

## Main declarations

* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_taylor_remainder_nonneg`: the Taylor integral
  remainder has sign `(-1)ⁿ`.
* `TauCeti.IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici`:
  transfer of the first-derivative integral from the interval-dependent differentiability set
  `Icc 0 T` to the fixed half-line `Ici 0`.
* `TauCeti.IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn`,
  `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one`: integrability and the
  improper integral of `-f'` on `(0, ∞)`, represented as `iteratedDerivWithin 1`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

namespace IsCompletelyMonotone

/-- **CM sign of the Taylor remainder.** For a completely monotone function the Taylor
integral remainder `∫ₓᵀ (T-t)ⁿ⁻¹/(n-1)! · f⁽ⁿ⁾(t) dt` has sign `(-1)ⁿ`:
`0 ≤ (-1)ⁿ` times it. -/
lemma neg_one_pow_mul_taylor_remainder_nonneg (hf : IsCompletelyMonotone f) {x T : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hxT : x ≤ T) :
    0 ≤ (-1 : ℝ) ^ n * ∫ t in x..T,
      (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
      iteratedDerivWithin n f (Icc x T) t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_nonneg_of_ae_restrict hxT
  have hIoo : ∀ t ∈ Ioo x T, (0 : ℝ) ≤ ((-1 : ℝ) ^ n *
      ((↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
        iteratedDerivWithin n f (Icc x T) t)) := fun t ht =>
    calc (0 : ℝ) ≤ (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Icc x T) t) :=
          mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (pow_nonneg (sub_nonneg.mpr ht.2.le) _))
            (by
              have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
              have hcda : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
                (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (by
                  exact_mod_cast le_top)
              rw [iteratedDerivWithin_eq_iteratedDeriv
                    (uniqueDiffOn_Icc (lt_trans ht.1 ht.2)) hcda (Ioo_subset_Icc_self ht),
                  ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
                    (mem_Ici.mpr ht_pos.le)]
              exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht_pos.le)
      _ = _ := by ring
  have h_mem : ∀ᵐ t ∂volume.restrict (Icc x T), t ∈ Ioo x T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact (Ioo_ae_eq_Icc (a := x) (b := T)).mono (fun t h ht => h.mpr ht)
  exact h_mem.mono fun t ht => by simp only [Pi.zero_apply]; exact hIoo t ht

end IsCompletelyMonotone

/-! ## Smoothness-index helpers -/

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-- The interval integral of `-f'` with the `T`-dependent set `Icc 0 T` equals the integral with
the fixed set `Ici 0` for a completely monotone function. -/
lemma IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici
    (hcm : IsCompletelyMonotone f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t =
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t := by
  exact ContDiffOn.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici
    (fun t ht => (hcm.contDiffOn.contDiffAt (Ici_mem_nhds ht.1)).of_le (nat_le_top _))
    le_rfl hT

/-- The integral `∫₀ᵀ (-f') dt → f(0) - L` as `T → ∞`, where `L = lim f(t)`. This is
the key uniform bound for the tightness argument in Bernstein's theorem. -/
lemma IsCompletelyMonotone.tendsto_integral_neg_iteratedDerivWithin_one_Icc_atTop
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t) atTop
        (nhds (f 0 - L)) :=
  ContDiffOn.tendsto_integral_neg_iteratedDerivWithin_one_Icc_atTop
    (a := 0) (hcm.contDiffOn.of_le (nat_le_top _)) hL

/-- `-f'` is integrable on `(0, ∞)` for a completely monotone function, where the derivative is
taken within the closed half-line `[0, ∞)`. -/
lemma IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn
    (hcm : IsCompletelyMonotone f) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0) := by
  obtain ⟨L, hL, -⟩ := hcm.exists_nonneg_tendsto_atTop
  -- Reduce the improper-integrability criterion to convergence of the interval integrals of
  -- the nonnegative function `-f'`.
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto (f 0 - L) 0
      (l := atTop) (b := id)
  -- Local integrability on each compact interval follows from continuity of the derivative
  -- within the fixed half-line.
  · intro T
    exact ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _)
      (uniqueDiffOn_Ici 0)).neg.mono Icc_subset_Ici_self).integrableOn_compact
        isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  -- On positive intervals the norm drops because `f' ≤ 0`; the finite-interval FTC identity
  -- then identifies the primitive with `f(0) - f(T)`.
  · have hnorm : ∀ᶠ T in atTop, (∫ t in (0 : ℝ)..id T,
        ‖(fun t => -iteratedDerivWithin 1 f (Ici 0) t) t‖) = f 0 - f T := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      simp only [id]
      have : (∫ t in (0 : ℝ)..T, ‖(fun t => -iteratedDerivWithin 1 f (Ici 0) t) t‖) =
              ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
          rw [uIoc_of_le hT.le] at ht
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by linarith [hcm.iteratedDerivWithin_one_nonpos ht.1.le])])
      rw [this, ← hcm.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici T hT.le]
      have hcm_Icc : ContDiffOn ℝ 1 f (Icc 0 T) :=
        (hcm.contDiffOn.mono Icc_subset_Ici_self).of_le (nat_le_top _)
      rw [iteratedDerivWithin_one, intervalIntegral.integral_neg,
        intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hcm_Icc hT.le, neg_sub]
    exact Tendsto.congr' (EventuallyEq.symm hnorm) (Tendsto.sub tendsto_const_nhds hL)

/-- The improper integral `∫₀^∞ (-f') dt = f(0) - L` for completely monotone functions. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi 0, -iteratedDerivWithin 1 f (Ici 0) t = f 0 - L := by
  have hint := hcm.neg_iteratedDerivWithin_one_integrableOn
  have htend := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have htend2 : Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      -iteratedDerivWithin 1 f (Ici 0) t) atTop (nhds (f 0 - L)) :=
    Tendsto.congr'
      ((eventually_gt_atTop 0).mono fun T hT =>
        by
          simp only
          rw [← hcm.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici T hT.le]
          have hcm_Icc : ContDiffOn ℝ 1 f (Icc 0 T) :=
            (hcm.contDiffOn.mono Icc_subset_Ici_self).of_le (nat_le_top _)
          rw [iteratedDerivWithin_one, intervalIntegral.integral_neg,
            intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hcm_Icc hT.le, neg_sub])
      (Tendsto.sub tendsto_const_nhds hL)
  exact tendsto_nhds_unique htend htend2

end TauCeti
