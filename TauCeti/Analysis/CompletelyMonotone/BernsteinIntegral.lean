/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.CompletelyMonotone.BernsteinAux
public import TauCeti.Analysis.CompletelyMonotone.Limits

/-!
# Integral and limit lemmas for completely monotone functions

General integral, integrability, and derivative-within limit lemmas for completely monotone
functions used in the Bernstein representation proof.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Smoothness-index helpers -/

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
private lemma nat_lt_top (n : ℕ) : (n : WithTop ℕ∞) < ∞ :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)

/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-- The interval integral of `-f'` with the `T`-dependent set `Icc 0 T` equals the integral with
the fixed set `Ici 0` (both agree a.e. by set transfer at interior points). -/
lemma IsCompletelyMonotone.integral_neg_deriv_Ici
    (hcm : IsCompletelyMonotone f) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t =
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t := by
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all volume
  intro t ht
  rw [uIoc_of_le hT.le] at ht
  have ht_pos : 0 < t := ht.1
  have hcda : ContDiffAt ℝ (↑1 : WithTop ℕ∞) f t :=
    (hcm.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
  simp only [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT) hcda
      (Ioc_subset_Icc_self ht),
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
      (mem_Ici.mpr ht_pos.le)]

/-- The total mass `∫₀ᵀ (-f') dt → f(0) - L` as `T → ∞`, where `L = lim f(t)`. This is the key
uniform bound for the tightness argument in Bernstein's theorem. -/
lemma IsCompletelyMonotone.tendsto_total_mass
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t) atTop
        (nhds (f 0 - L)) :=
  Tendsto.congr' (EventuallyEq.symm
    ((eventually_gt_atTop 0).mono fun T hT => hcm.integral_mass T hT))
    (Tendsto.sub tendsto_const_nhds hL)

/-- `-f'` is integrable on `(0, ∞)` for completely monotone functions (total mass `f(0) - L`). -/
lemma IsCompletelyMonotone.neg_deriv_integrableOn (hcm : IsCompletelyMonotone f) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0) := by
  obtain ⟨L, hL, -⟩ := hcm.tendsto_atTop
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto (f 0 - L) 0
      (l := atTop) (b := id)
  · intro T
    exact ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _)
      (uniqueDiffOn_Ici 0)).neg.mono Icc_subset_Ici_self).integrableOn_compact
        isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
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
      rw [this, ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
    exact Tendsto.congr' (EventuallyEq.symm hnorm) (Tendsto.sub tendsto_const_nhds hL)

/-- The improper integral `∫₀^∞ (-f') dt = f(0) - L` for completely monotone functions. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_deriv
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi 0, -iteratedDerivWithin 1 f (Ici 0) t = f 0 - L := by
  have hint := hcm.neg_deriv_integrableOn
  have htend := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have htend2 : Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      -iteratedDerivWithin 1 f (Ici 0) t) atTop (nhds (f 0 - L)) :=
    Tendsto.congr'
      ((eventually_gt_atTop 0).mono fun T hT =>
        ((hcm.integral_neg_deriv_Ici T hT).symm.trans (hcm.integral_mass T hT)).symm)
      (Tendsto.sub tendsto_const_nhds hL)
  exact tendsto_nhds_unique htend htend2

/-- For a completely monotone `f`, the `k`-th iterated derivative within `[0, ∞)` is
differentiable at any `t > 0`, with derivative the `(k+1)`-th iterated derivative. -/
lemma IsCompletelyMonotone.hasDerivAt_iteratedDerivWithin_succ
    (hcm : IsCompletelyMonotone f) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDerivWithin k f (Ici 0))
      (iteratedDerivWithin (k + 1) f (Ici 0) t) t := by
  have hmem : Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht
  have hda := (hcm.contDiffOn.differentiableOn_iteratedDerivWithin
    (nat_lt_top k) (uniqueDiffOn_Ici 0)).hasDerivAt hmem
  have hval : iteratedDerivWithin (k + 1) f (Ici 0) t
      = deriv (iteratedDerivWithin k f (Ici 0)) t := by
    rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hmem]
  rw [hval]; exact hda

end TauCeti
