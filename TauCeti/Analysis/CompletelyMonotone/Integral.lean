/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Integral lemmas for completely monotone functions

Taylor-remainder sign bounds and improper-integral facts about completely monotone functions.

These extend the object API in `CompletelyMonotone/Basic.lean` with the sign of the Taylor
integral remainder and improper-integral facts for the first derivative within `[0, ∞)`.

## Main declarations

* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_taylor_remainder_nonneg`: the Taylor integral
  remainder has sign `(-1)ⁿ`.
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

private lemma iteratedDerivWithin_Icc_eq_Ici {n : ℕ} {x T t : ℝ}
    (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f t) (ht0 : 0 ≤ t) (hxT : x < T)
    (hxt : x ≤ t) (htT : t ≤ T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hf ⟨hxt, htT⟩,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hf (mem_Ici.mpr ht0)]

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
              rw [iteratedDerivWithin_Icc_eq_Ici hcda ht_pos.le (lt_trans ht.1 ht.2)
                ht.1.le ht.2.le]
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

/-- `-f'` is integrable on `(0, ∞)` for a completely monotone function, where the derivative is
taken within the closed half-line `[0, ∞)`. -/
lemma IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn
    (hcm : IsCompletelyMonotone f) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0) := by
  obtain ⟨L, hL, -⟩ := hcm.exists_nonneg_tendsto_atTop
  have hcont : ContinuousWithinAt f (Ici 0) 0 :=
    hcm.contDiffOn.continuousOn.continuousWithinAt self_mem_Ici
  have hderiv : ∀ t ∈ Ioi 0,
      HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t := by
    intro t ht
    exact hcm.hasDerivAt_iteratedDerivWithin_succ 0 ht
  have hneg : ∀ t ∈ Ioi 0, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos ht.le
  exact (integrableOn_Ioi_deriv_of_nonpos hcont hderiv hneg hL).neg

/-- The improper integral `∫₀^∞ (-f') dt = f(0) - L` for completely monotone functions. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi 0, -iteratedDerivWithin 1 f (Ici 0) t = f 0 - L := by
  have hcont : ContinuousWithinAt f (Ici 0) 0 :=
    hcm.contDiffOn.continuousOn.continuousWithinAt self_mem_Ici
  have hderiv : ∀ t ∈ Ioi 0,
      HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t := by
    intro t ht
    exact hcm.hasDerivAt_iteratedDerivWithin_succ 0 ht
  have hneg : ∀ t ∈ Ioi 0, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos ht.le
  have hFTC :
      ∫ t in Ioi 0, iteratedDerivWithin 1 f (Ici 0) t = L - f 0 :=
    integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg hL
  rw [MeasureTheory.integral_neg, hFTC]
  ring

end TauCeti
