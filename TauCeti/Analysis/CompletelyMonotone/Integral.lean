/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Integral and analysis lemmas for completely monotone functions

The generic completely-monotone integral/analysis layer: FTC, Taylor-remainder, and
improper-integral facts about completely monotone functions.

These extend the object API in `CompletelyMonotone/Basic.lean` with derivative-within transfer
on compact intervals, the sign of the Taylor integral remainder, finite-interval
fundamental-theorem identities, and improper-integral facts for `-f'`.

## Main declarations

* `TauCeti.ContDiffAt.iteratedDerivWithin_Icc_eq_Ici`: iterated derivatives within `Icc x T`
  and within `Ici a` agree at interior points.
* `TauCeti.ContDiffOn.integral_neg_derivWithin_Icc`,
  `TauCeti.ContDiffOn.integral_neg_derivWithin_Icc_zero_left`: finite-interval
  fundamental-theorem identities for smooth functions.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_taylor_remainder_nonneg`: the Taylor integral
  remainder has sign `(-1)ⁿ`.
* `TauCeti.IsCompletelyMonotone.integral_neg_deriv`, `TauCeti.IsCompletelyMonotone.integral_mass`:
  compatibility wrappers for the smooth finite-interval identities.
* `TauCeti.IsCompletelyMonotone.neg_deriv_integrableOn`,
  `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_deriv`: integrability and the improper integral
  of `-f'` on `(0, ∞)`.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}

/-- `iteratedDerivWithin` on `Icc x T` agrees with `iteratedDerivWithin` on `Ici a` at interior
points, since both equal `iteratedDeriv n f t` under local smoothness at `t`. -/
lemma ContDiffAt.iteratedDerivWithin_Icc_eq_Ici {n : ℕ}
    {a x T t : ℝ} (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f t) (ht_lo : a < t)
    (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici a) t := by
  have hxT : x < T := lt_trans ht.1 ht.2
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hf
        (Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a) hf
        (mem_Ici.mpr ht_lo.le)]

/-- The fundamental-theorem identity
`f x - f T = ∫ₓᵀ -f'` on a compact interval, with derivatives taken within that interval. -/
lemma ContDiffOn.integral_neg_derivWithin_Icc {x T : ℝ}
    [CompleteSpace E] (hf : ContDiffOn ℝ 1 f (Icc x T)) (hxT : x ≤ T) :
    f x - f T = ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t := by
  have hFTC := intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hf hxT
  rw [iteratedDerivWithin_one]
  rw [intervalIntegral.integral_neg, hFTC, neg_sub]

/-- The zero-left specialization of `ContDiffOn.integral_neg_derivWithin_Icc`. -/
lemma ContDiffOn.integral_neg_derivWithin_Icc_zero_left {T : ℝ}
    [CompleteSpace E] (hf : ContDiffOn ℝ 1 f (Icc 0 T)) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t = f 0 - f T := by
  exact (ContDiffOn.integral_neg_derivWithin_Icc hf hT).symm

/-- The interval integral of `-f'` with the `T`-dependent set `Icc 0 T` equals the integral with
the fixed set `Ici 0`, under local smoothness at the strict interior points. -/
lemma ContDiffOn.integral_neg_derivWithin_Icc_eq_Ici
    {T : ℝ} (hf : ∀ t ∈ Ioo (0 : ℝ) T, ContDiffAt ℝ 1 f t) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t =
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  rw [uIoo_of_le hT] at ht
  have ht_pos : 0 < t := ht.1
  have hT_pos : 0 < T := lt_trans ht_pos ht.2
  have hcda : ContDiffAt ℝ 1 f t := hf t ht
  simp only [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT_pos) hcda
      (Ioo_subset_Icc_self ht),
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
      (mem_Ici.mpr ht_pos.le)]

/-- The total mass `∫₀ᵀ (-f') dt → f(0) - L` as `T → ∞`, assuming smoothness on `[0, ∞)`
and convergence of `f` to `L` at infinity. -/
lemma ContDiffOn.tendsto_total_mass
    [CompleteSpace E] (hf : ContDiffOn ℝ 1 f (Ici 0)) {L : E}
    (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t) atTop
        (nhds (f 0 - L)) := by
  refine Tendsto.congr' (EventuallyEq.symm ?_) (Tendsto.sub tendsto_const_nhds hL)
  exact (eventually_gt_atTop 0).mono fun T hT =>
    ContDiffOn.integral_neg_derivWithin_Icc_zero_left (hf.mono Icc_subset_Ici_self) hT.le

variable {f : ℝ → ℝ}

namespace IsCompletelyMonotone

/-- `iteratedDerivWithin` on `Icc x T` agrees with `iteratedDerivWithin` on `Ici 0` at interior
points, since both equal `iteratedDeriv n f t` when `0 < t`. -/
lemma iteratedDerivWithin_Icc_eq_Ici {n : ℕ} (hf : IsCompletelyMonotone f)
    {x T t : ℝ} (ht_pos : 0 < t) (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  have hcda : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (by exact_mod_cast le_top)
  exact ContDiffAt.iteratedDerivWithin_Icc_eq_Ici (a := 0) hcda ht_pos ht

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
            (by rw [hf.iteratedDerivWithin_Icc_eq_Ici (lt_of_le_of_lt hx ht.1) ht]
                exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n
                  (lt_of_le_of_lt hx ht.1).le)
      _ = _ := by ring
  have h_mem : ∀ᵐ t ∂volume.restrict (Icc x T), t ∈ Ioo x T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact (Ioo_ae_eq_Icc (a := x) (b := T)).mono (fun t h ht => h.mpr ht)
  exact h_mem.mono fun t ht => by simp only [Pi.zero_apply]; exact hIoo t ht

/-- For a completely monotone `f` the `n = 1` fundamental-theorem identity gives
`f(x) - f(T) = ∫ₓᵀ (-f'(t)) dt`, with the integrand nonnegative by the sign condition. -/
lemma integral_neg_deriv (hf : IsCompletelyMonotone f)
    (x T : ℝ) (hx : 0 ≤ x) (hxT : x ≤ T) :
    f x - f T = ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t := by
  have hsubset : Icc x T ⊆ Ici 0 := Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx)
  have hcm_Icc : ContDiffOn ℝ 1 f (Icc x T) :=
    (hf.contDiffOn.mono hsubset).of_le (by exact_mod_cast le_top)
  exact ContDiffOn.integral_neg_derivWithin_Icc hcm_Icc hxT

/-- The total mass identity `∫₀ᵀ (-f') = f(0) - f(T)` for a completely monotone function. -/
lemma integral_mass (hf : IsCompletelyMonotone f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t = f 0 - f T := by
  exact (hf.integral_neg_deriv 0 T le_rfl hT).symm

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
the fixed set `Ici 0` (both agree a.e. by set transfer at interior points). -/
lemma IsCompletelyMonotone.integral_neg_deriv_Ici
    (hcm : IsCompletelyMonotone f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t =
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t := by
  exact ContDiffOn.integral_neg_derivWithin_Icc_eq_Ici
    (fun t ht => (hcm.contDiffOn.contDiffAt (Ici_mem_nhds ht.1)).of_le (nat_le_top _)) hT

/-- The total mass `∫₀ᵀ (-f') dt → f(0) - L` as `T → ∞`, where `L = lim f(t)`. This is
the key uniform bound for the tightness argument in Bernstein's theorem. -/
lemma IsCompletelyMonotone.tendsto_total_mass
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t) atTop
        (nhds (f 0 - L)) :=
  ContDiffOn.tendsto_total_mass (hcm.contDiffOn.of_le (nat_le_top _)) hL

/-- `-f'` is integrable on `(0, ∞)` for a completely monotone function, where the derivative is
taken within the closed half-line `[0, ∞)`. -/
lemma IsCompletelyMonotone.neg_deriv_integrableOn (hcm : IsCompletelyMonotone f) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0) := by
  obtain ⟨L, hL, -⟩ := hcm.exists_nonneg_tendsto_atTop
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
      rw [this, ← hcm.integral_neg_deriv_Ici T hT.le, hcm.integral_mass T hT.le]
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
        ((hcm.integral_neg_deriv_Ici T hT.le).symm.trans (hcm.integral_mass T hT.le)).symm)
      (Tendsto.sub tendsto_const_nhds hL)
  exact tendsto_nhds_unique htend htend2

end TauCeti
